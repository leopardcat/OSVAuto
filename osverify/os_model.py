from typing import Optional, Iterable
import json

from osverify.os_theory import OSTheory
from osverify import os_term
from osverify.os_term import OSNumber, VarContext
from osverify import os_struct
from osverify.os_struct import OSType
from osverify import os_simplify
from osverify.os_term import OSTerm
from osverify import os_z3wrapper
from osverify.os_tactics import ProofState
from osverify.os_z3wrapper import z3, convert_z3_expr
from osverify import os_util
from osverify import os_theory


class ModelKey:
    """Key in a model, corresponding to atomic terms.
    
    Each key is specified by a name and a list of indices, representing
    an atomic term.

    """
    def __init__(self, name: str, indices: Iterable[OSTerm]):
        self.name = name
        self.indices = tuple(indices)

    def get_readable_name(self) -> str:
        """Return readable name for the key."""
        res = ""
        parts = self.name.split(".")
        cur_index = 0
        for i, part in enumerate(parts):
            if part in ('get', 'index'):
                res += f"[{self.indices[cur_index]}]"
                cur_index += 1
            else:
                if i > 0:
                    res += "."
                res += part
                if part == "indom":
                    res += f"({self.indices[cur_index]})"
                    cur_index += 1
        if cur_index != len(self.indices):
            raise AssertionError(
                f"get_readable_name: length does not match for {self.name}, {len(self.indices)}")
        return res
        
    def __str__(self):
        return self.get_readable_name()
    
    def __repr__(self):
        return f"ModelKey({repr(self.name)}, {repr(self.indices)})"
    
    def __hash__(self):
        return hash(("ModelKey", self.name, self.indices))
    
    def __eq__(self, other):
        return isinstance(other, ModelKey) and self.name == other.name and \
            self.indices == other.indices

    def is_prefix(self, other: "ModelKey") -> bool:
        """Return whether self is a prefix of other (including equality)."""
        parts1 = self.name.split('.')
        parts2 = other.name.split('.')
        idx1, idx2 = self.indices, other.indices
        return len(parts1) <= len(parts2) and parts1 == parts2[:len(parts1)] and \
            len(idx1) <= len(idx2) and idx1 == idx2[:len(idx1)]

    def get_suffix(self, other: "ModelKey") -> "ModelKey":
        """Given other is a prefix of self, extract the extra suffix of self."""
        parts1 = self.name.split('.')
        parts2 = other.name.split('.')
        idx1, idx2 = self.indices, other.indices
        return ModelKey("." + ".".join(parts1[len(parts2):]), idx1[len(idx2):])
    
    def join(self, other: "ModelKey") -> "ModelKey":
        """Return the join of two keys. The second key is required to
        be a submodel key (preceded by ".").
        
        """
        parts1 = self.name.split(".")
        parts2 = other.name.split(".")
        if len(parts2) == 0 or parts2[0] != "":
            raise AssertionError(f"join: {other.name} is not a submodel key")
        name = ".".join(parts1 + parts2[1:])
        return ModelKey(name, self.indices + other.indices)

base_key: ModelKey = ModelKey(".", [])

class PartialTerm:
    """Base classes for partial terms."""
    type: OSType

    def pprint(self, thy: OSTheory) -> str:
        """Obtain the pretty-printed form of the partial term."""
        return str(self)

    def evaluate(self, thy: OSTheory, sub_key: ModelKey) -> "PartialTerm":
        """Evaluate at the given sub-key."""
        raise NotImplementedError(f"PartialTerm evaluate on {type(self)}")

    def update(self, thy: OSTheory, sub_key: ModelKey, pt: "PartialTerm") -> "PartialTerm":
        """Update the value at sub-key to given partial term."""
        raise NotImplementedError(f"PartialTerm update on {type(self)}")



class UnknownTerm(PartialTerm):
    def __init__(self, *, type: OSType):
        self.type = type

    def __str__(self):
        return "?"

    def __repr__(self):
        return f"UnknownTerm({repr(self.type)})"

    def __eq__(self, other):
        return isinstance(other, UnknownTerm) and self.type == other.type

    def evaluate(self, thy: OSTheory, sub_key: ModelKey) -> PartialTerm:
        if sub_key.name == ".":
            return self
        raise AssertionError(f"Evaluate on UnknownTerm: {sub_key}")        

    def update(self, thy: OSTheory, sub_key: ModelKey, pt: PartialTerm) -> PartialTerm:
        if sub_key.name == ".":
            return pt
        
        if os_struct.is_map_type(self.type):
            empty_map = PartialMapTerm(dict(), dict(), type=self.type)
            return empty_map.update(thy, sub_key, pt)
        elif os_struct.is_seq_type(self.type):
            empty_seq = PartialSeqTerm(dict(), UnknownTerm(type=os_struct.Int), type=self.type)
            return empty_seq.update(thy, sub_key, pt)
        elif isinstance(self.type, os_struct.OSStructType):
            empty_struct = PartialStructTerm(self.type.name, [])
            return empty_struct.update(thy, sub_key, pt)
        else:
            raise AssertionError(f"initialize for {self.type}")

class FullTerm(PartialTerm):
    def __init__(self, t: OSTerm):
        self.t = t
        self.type = t.type

    def __str__(self):
        return str(self.t)

    def __repr__(self):
        return f"FullTerm({repr(self.t)})"

    def __eq__(self, other):
        return isinstance(other, FullTerm) and self.t == other.t

    def evaluate(self, thy: OSTheory, sub_key: ModelKey) -> PartialTerm:
        if sub_key.name == ".":
            return self
        raise AssertionError(f"Evaluate on FullTerm: {sub_key}")        

    def update(self, thy: OSTheory, sub_key: ModelKey, pt: PartialTerm) -> PartialTerm:
        if sub_key.name == ".":
            return pt
        raise AssertionError(f"Update on FullTerm: {sub_key}")

class PartialMapTerm(PartialTerm):
    """Represents a partially known map.
    
    Attributes
    ----------
    data: dict[OSTerm, PartialTerm]
        mapping from keys to values. Not all keys need to be mapped.
    indom_data: dict[OSTerm, bool]
        mapping from keys to whether they are in the map.
    
    """
    def __init__(self, data: dict[OSTerm, PartialTerm],
                 indom_data: dict[OSTerm, PartialTerm], *, type: OSType):
        self.data = data
        self.indom_data = indom_data
        assert os_struct.is_map_type(type)
        self.type = type
        self.key_type, self.val_type = self.type.params

    def __str__(self):
        res = "{"
        all_keys = set(self.data.keys())
        all_keys.update(self.indom_data.keys())
        keys = sorted(all_keys, key=lambda x: str(x))
        for i, key in enumerate(keys):
            if i > 0:
                res += ", "
            if key in self.indom_data and self.indom_data[key] == FullTerm(OSNumber(False)):
                res += f"{key}: -"
            elif key in self.data:
                res += f"{key}: {self.data[key]}"
            else:
                res += f"{key}: ?"
        res += "}"
        return res
    
    def __repr__(self):
        return f"PartialMapTerm(data={repr(self.data)}, indom_data={repr(self.indom_data)}, " \
               f"type={repr(self.type)})"
    
    def __eq__(self, other):
        return isinstance(other, PartialMapTerm) and self.data == other.data and \
            self.indom_data == other.indom_data and self.type == other.type

    def pprint(self, thy: OSTheory) -> str:
        res = "{"
        all_keys = set(self.data.keys())
        all_keys.update(self.indom_data.keys())
        keys = sorted(all_keys, key=lambda x: str(x))
        for i, key in enumerate(keys):
            if i > 0:
                res += ", "
            if key in self.indom_data and self.indom_data[key] == FullTerm(OSNumber(False)):
                res += f"{key}: -"
            elif key in self.data:
                res += f"{key}: {self.data[key]}"
            else:
                res += f"{key}: ?"
        res += "}"
        return res

    def evaluate(self, thy: OSTheory, sub_key: ModelKey) -> PartialTerm:
        if sub_key.name == ".":
            return self

        names = sub_key.name.split(".")
        assert len(names) > 1 and names[0] == ""
        if names[1] == "get":
            idx = sub_key.indices[0]
            assert is_literal_term(thy, idx), f"Evaluate on PartialMapTerm: {idx} is not literal term"
            if idx not in self.data:
                return UnknownTerm(type=self.val_type)
            return self.data[idx].evaluate(
                thy, sub_key.get_suffix(ModelKey(".get", [idx])))
        elif names[1] == "indom":
            idx = sub_key.indices[0]
            assert is_literal_term(thy, idx), f"Evaluate on PartialMapTerm: {idx} is not literal term"
            if idx not in self.indom_data:
                return UnknownTerm(type=os_struct.Bool)
            return self.indom_data[idx]
        else:
            raise AssertionError(f"Unexpected name {sub_key.name} for partial map")

    def update(self, thy: OSTheory, sub_key: ModelKey, pt: PartialTerm) -> PartialTerm:
        if sub_key.name == ".":
            return pt

        names = sub_key.name.split(".")
        assert len(names) > 1 and names[0] == ""
        if names[1] == "get":
            idx = sub_key.indices[0]
            assert is_literal_term(thy, idx), f"Update on PartialMapTerm: {idx} is not literal term"
            new_data: dict[OSTerm, PartialTerm] = dict()
            for k, v in self.data.items():
                new_data[k] = v
            if idx not in new_data:
                new_data[idx] = UnknownTerm(type=self.val_type)
            new_data[idx] = new_data[idx].update(
                thy, sub_key.get_suffix(ModelKey(".get", [idx])), pt)
            return PartialMapTerm(new_data, dict(self.indom_data), type=self.type)
        elif names[1] == "indom":
            idx = sub_key.indices[0]
            assert is_literal_term(thy, idx), f"Update on PartialMapTerm: {idx} is not literal term"
            new_indom_data: dict[OSTerm, PartialTerm] = dict()
            for k, v in self.indom_data.items():
                new_indom_data[k] = v
            new_indom_data[idx] = pt
            return PartialMapTerm(dict(self.data), new_indom_data, type=self.type)
        else:
            raise AssertionError(f"Unexpected name {sub_key.name} for partial map")

class PartialSeqTerm(PartialTerm):
    def __init__(self, data: dict[int, PartialTerm], length: PartialTerm, *,
                 type: OSType):
        self.data = data
        self.length = length
        for k, v in self.data.items():
            assert isinstance(k, int) and isinstance(v, PartialTerm)
        assert os_struct.is_seq_type(type)
        self.type = type
        self.val_type = self.type.params[0]

    def __str__(self):
        res = "["
        i = 0
        keys = sorted(self.data.keys(), key=lambda x: str(x))
        for key in keys:
            if i > 0:
                res += ", "
            res += f"{key}: {self.data[key]}"
            i += 1
        res += f", len={self.length}]"
        return res
    
    def __repr__(self):
        return f"PartialSeqTerm({repr(self.data)}, {repr(self.length)}, type={repr(self.type)})"
    
    def __eq__(self, other):
        return isinstance(other, PartialSeqTerm) and self.data == other.data and \
            self.length == other.length and self.type == other.type

    def pprint(self, thy: OSTheory) -> str:
        res = "["
        i = 0
        keys = sorted(self.data.keys(), key=lambda x: str(x))
        for key in keys:
            if i > 0:
                res += ", "
            res += f"{key}: {self.data[key].pprint(thy)}"
            i += 1
        res += f", len={self.length}]"
        return res

    def evaluate(self, thy: OSTheory, sub_key: ModelKey) -> PartialTerm:
        if sub_key.name == ".":
            return self
        
        names = sub_key.name.split(".")
        if names[1] == "index":
            idx = sub_key.indices[0]
            if not (isinstance(idx, OSNumber) and idx.type == os_struct.Int):
                raise AssertionError(f"evaluate on PartialSeqTerm: unexpected index {idx}")
            if idx.val not in self.data:
                return UnknownTerm(self.val_type)
            else:
                return self.data[idx.val].evaluate(
                    thy, sub_key.get_suffix(ModelKey(".index", [idx])))
        elif names[1] == "length":
            return self.length
        else:
            raise AssertionError(f"Unexpected name {sub_key.name} for sequence")        

    def update(self, thy: OSTheory, sub_key: ModelKey, pt: PartialTerm) -> PartialTerm:
        if sub_key.name == ".":
            return pt

        names = sub_key.name.split(".")
        assert len(names) > 1 and names[0] == ""
        if names[1] == "index":
            idx = sub_key.indices[0]
            if not (isinstance(idx, OSNumber) and idx.type == os_struct.Int):
                raise AssertionError(f"update on PartialSeqTerm: unexpected index {idx}")
            new_data: dict[int, PartialTerm] = dict()
            for k, v in self.data.items():
                new_data[k] = v
            if idx.val not in new_data:
                new_data[idx.val] = UnknownTerm(type=self.val_type)
            new_data[idx.val] = new_data[idx.val].update(
                thy, sub_key.get_suffix(ModelKey(".index", [idx])), pt)
            return PartialSeqTerm(new_data, self.length, type=self.type)
            
        elif names[1] == "length":
            new_data: dict[int, PartialTerm] = dict()
            for k, v in self.data.items():
                new_data[k] = v
            return PartialSeqTerm(new_data, pt, type=self.type)            
        else:
            raise AssertionError(f"Unexpected name {sub_key.name} for sequence")


class PartialFunTerm(PartialTerm):
    def __init__(self, func_name: str, args: Iterable[PartialTerm], *, type: OSType):
        self.func_name = func_name
        self.args = tuple(args)
        self.type = type

    def __str__(self):
        return f"{self.func_name}({', '.join(str(arg) for arg in self.args)})"

    def __eq__(self, other):
        return isinstance(other, PartialFunTerm) and self.func_name == other.func_name and \
            self.args == other.args

    def pprint(self, thy: OSTheory) -> str:
        return f"{self.func_name}({', '.join(arg.pprint(thy) for arg in self.args)})"

    def evaluate(self, thy: OSTheory, sub_key: ModelKey) -> PartialTerm:
        if sub_key.name == ".":
            return self
        assert isinstance(self.type, os_struct.OSHLevelType) and self.type.name in thy.datatypes, \
            f"evaluate: unexpected type {self.type}"

        names = sub_key.name.split(".")
        datatype = thy.datatypes[self.type.name]
        if names[1] == "id":
            # Get ID of partial term
            return FullTerm(os_term.integer(datatype.get_branch_id(self.func_name)))
        else:
            # Get specific field
            branch = datatype.branch_map[self.func_name]
            for i, (param_name, _) in enumerate(branch.params):
                if param_name == names[1]:
                    return self.args[i].evaluate(
                        thy, sub_key.get_suffix(ModelKey(f".{names[1]}", tuple())))

        raise NotImplementedError(
            f"evaluate: {self.func_name}({", ".join(str(arg) for arg in self.args)}) at {repr(sub_key)}")

    def update(self, thy: OSTheory, sub_key: ModelKey, pt: PartialTerm) -> PartialTerm:
        if sub_key.name == ".":
            return pt
        
        raise NotImplementedError(
            f"update: {self.func_name}({", ".join(str(arg) for arg in self.args)}) at {repr(sub_key)}")


class PartialStructTerm(PartialTerm):
    def __init__(self, struct_name: str, vals: Iterable[tuple[str, PartialTerm]]):
        self.struct_name = struct_name
        self.vals = tuple(vals)
        self.val_map: dict[str, PartialTerm] = dict()
        for name, pt in self.vals:
            self.val_map[name] = pt
        self.type = os_struct.OSStructType(struct_name)

    def __str__(self):
        oneline = "%s{{%s}}" % (self.struct_name, ", ".join("%s: %s" % (k, v) for k, v in self.vals))
        if len(oneline) <= 100:
            return oneline
        
        # Otherwise, print in multiple lines
        res = "%s{{\n" % self.struct_name
        for k, v in self.vals:
            res += os_util.indent("%s: %s," % (k, v)) + '\n'
        res += "}}"
        return res

    def __eq__(self, other):
        return isinstance(other, PartialStructTerm) and self.struct_name == other.struct_name and \
            self.vals == other.vals

    def pprint(self, thy: OSTheory) -> str:
        field_strs: list[str] = list()

        struct = thy.structs[self.struct_name]
        for field in struct.fields:
            name = field.field_name
            if name not in self.val_map:
                field_strs.append(f"{name}: ?")
            else:
                val = self.val_map[name]
                val_str = str(val)
                if isinstance(val, FullTerm) and isinstance(val.t, os_term.OSNumber) and \
                    isinstance(val.t.val, int):
                    if "binary" in field.annotations:
                        val_str = bin(val.t.val)
                    elif "octal" in field.annotations:
                        val_str = oct(val.t.val)
                    elif "hex" in field.annotations:
                        val_str = hex(val.t.val)
                field_strs.append(f"{name}: {val_str}")
        oneline = "%s{{%s}}" % (self.struct_name, ", ".join(field_strs))
        if len(oneline) <= 72:
            return oneline
        
        # Otherwise, print in multiple lines
        res = "%s{{\n" % self.struct_name
        for s in field_strs:
            res += os_util.indent(s) + '\n'
        res += "}}"
        return res

    def evaluate(self, thy: OSTheory, sub_key: ModelKey) -> PartialTerm:
        if sub_key.name == ".":
            return self

        names = sub_key.name.split(".")
        assert len(names) > 1 and names[0] == ""
        for field, pt in self.vals:
            if field == names[1]:
                return pt.evaluate(thy, sub_key.get_suffix(ModelKey(f".{names[1]}", [])))

        # Not found
        field_ty = thy.get_field_type(self.type, names[1])
        return UnknownTerm(type=field_ty)

    def update(self, thy: OSTheory, sub_key: ModelKey, pt: PartialTerm) -> PartialTerm:
        if sub_key.name == ".":
            return pt

        names = sub_key.name.split(".")
        assert len(names) > 1 and names[0] == ""
        new_vals = list(self.vals)
        found = False
        for i, (field, field_pt) in enumerate(new_vals):
            if field == names[1]:
                new_vals[i] = (field, field_pt.update(
                    thy, sub_key.get_suffix(ModelKey(f".{names[1]}", [])), pt))
                found = True
        if not found:
            field_ty = thy.get_field_type(self.type, names[1])
            new_vals.append((names[1], UnknownTerm(type=field_ty).update(
                thy, sub_key.get_suffix(ModelKey(f".{names[1]}", [])), pt)))
        return PartialStructTerm(self.struct_name, new_vals)


def seq_append_partial(a: PartialSeqTerm, b: PartialSeqTerm) -> PartialSeqTerm:
    """Compute `seq_append` on two partial terms."""

    if isinstance(a.length, UnknownTerm):
        raise NotImplementedError("seq_append_partial: length of a is unknown")

    assert isinstance(a.length, FullTerm) and isinstance(a.length.t, os_term.OSNumber), \
        f"seq_append_partial: unexpected length {a.length} for a"

    assert isinstance(b.length, FullTerm) and isinstance(b.length.t, os_term.OSNumber), \
        f"seq_append_partial: unexpected length {b.length} for b"

    length_a = a.length.t.val
    length_b = b.length.t.val
    new_data: dict[int, PartialTerm] = dict()
    for idx, pt in a.data.items():
        new_data[idx] = pt
    for idx, pt in b.data.items():
        new_data[idx + length_a] = pt
    return PartialSeqTerm(new_data, FullTerm(os_term.integer(length_a + length_b)), type=a.type)

def seq_cons_partial(x: PartialTerm, xs: PartialSeqTerm) -> PartialSeqTerm:
    """Compute `seq_cons` on two terms."""

    if isinstance(xs.length, UnknownTerm):
        raise NotImplementedError("seq_cons_partial: length of xs is unknown")
    assert isinstance(xs.length, FullTerm) and isinstance(xs.length.t, os_term.OSNumber), \
        f"seq_cons_partial: unexpected length {xs.length} for xs"
    
    length_xs = xs.length.t.val
    new_data: dict[int, PartialTerm] = dict()
    for idx, pt in xs.data.items():
        new_data[idx + 1] = pt
    new_data[0] = x
    return PartialSeqTerm(new_data, FullTerm(os_term.integer(length_xs + 1)), type=xs.type)

def seq_update_partial(k: int, v: PartialTerm, seq: PartialSeqTerm) -> PartialSeqTerm:
    """Compute seq_update on partial terms."""

    new_data: dict[int, PartialTerm] = dict()
    for idx, pt in seq.data.items():
        new_data[idx] = pt
    new_data[k] = v
    return PartialSeqTerm(new_data, seq.length, type=seq.type)

def seq_slice_partial(start: int, end: int, seq: PartialSeqTerm) -> PartialSeqTerm:
    """Compute `seq_slice` on partial terms."""

    if isinstance(seq.length, UnknownTerm):
        raise NotImplementedError("seq_slice_partial: length of seq is unknown")

    new_data: dict[int, PartialTerm] = dict()
    for idx, pt in seq.data.items():
        if idx >= start and idx < end:
            new_data[idx - start] = pt
    return PartialSeqTerm(new_data, FullTerm(os_term.integer(end - start)), type=seq.type)

def seq_repeat_partial(value: PartialTerm, n: int) -> PartialSeqTerm:
    """Compute `seq_repeat` on partial term."""

    if n > 100:
        # TODO: implement range for this case
        raise NotImplementedError
    new_data: dict[int, PartialTerm] = dict()
    for i in range(n):
        new_data[i] = value
    return PartialSeqTerm(new_data, FullTerm(os_term.integer(n)),
                          type=os_struct.SeqType(value.type))    

def seq_remove_partial(i: int, seq: PartialSeqTerm) -> PartialSeqTerm:
    """Compute `seq_remove` on partial terms."""

    if isinstance(seq.length, UnknownTerm):
        raise NotImplementedError("seq_remove_partial: length of seq is unknown")
    assert isinstance(seq.length, FullTerm) and isinstance(seq.length.t, OSNumber)

    new_data: dict[int, PartialTerm] = dict()
    for idx, pt in seq.data.items():
        if idx < i:
            new_data[idx] = pt
        else:
            new_data[idx - 1] = pt
    return PartialSeqTerm(new_data, FullTerm(os_term.integer(seq.length.t.val - 1)), type=seq.type)


class Model:
    """Model as counterexample to a query.
    
    Each model is given by a map from keys (of type `ModelKey`) to
    their values (of type `OSTerm`).

    Attributes
    ----------
    key_data: dict[ModelKey, OSTerm]
        mapping from model keys (atomic terms) to their value
    term_data: dict[OSTerm, OSTerm]
        cached values of evaluation of existing terms
    var_data: dict[str, PartialTerm]
        model value for each variable

    """
    def __init__(self, *, key_data: dict[ModelKey, OSTerm] = None):
        if key_data is None:
            key_data = dict()
        self.key_data: dict[ModelKey, OSTerm] = key_data
        self.term_data: dict[OSTerm, OSTerm] = dict()
        self.var_data: dict[str, PartialTerm] = dict()

    def print_model(self, *, print_key_map=False, print_term_map=False,
                    print_var_map=False) -> str:
        res = ""
        if print_key_map:
            res += "key map:\n"
            for key, val in self.key_data.items():
                res += "%s := %s\n" % (key, val)
        if print_term_map:
            res += "term map:\n"
            for key, val in self.term_data.items():
                res += "%s := %s\n" % (key, val)
        if print_var_map:
            res += "var map:\n"
            for key, val in self.var_data.items():
                res += "%s := %s\n" % (key, val)
        return res
    
    def pprint(self, thy: OSTheory) -> str:
        res = ""
        for key, val in self.var_data.items():
            res += "%s := %s\n" % (key, val.pprint(thy))
        return res

    def __str__(self):
        return self.print_model(print_var_map=True)
    
    def add_key_data(self, key: ModelKey, val: OSTerm):
        self.key_data[key] = val

    def add_map_update(self, key: OSTerm, val: OSTerm):
        self.add_key_data(ModelKey(".get", [key]), val)

    def add_struct_update(self, update: os_term.FieldUpdate):
        self.add_key_data(ModelKey(f".{update.field_name}", []), update.expr)

    def get_length(self) -> OSTerm:
        return self.key_data(ModelKey(".length", []))

    def add_submodel(self, key: ModelKey, submodel: "Model"):
        for subkey, val in submodel.key_data.items():
            self.add_key_data(key.join(subkey), val)

    def eval(self, t: OSTerm) -> OSTerm:
        if t in self.term_data:
            return self.term_data[t]
        elif os_term.is_atomic_term(t):
            name, indices = os_term.dest_atomic_term(t)
            indices_val = [self.eval(index) for index in indices]
            model_key = ModelKey(name, indices_val)
            if model_key in self.key_data:
                return self.key_data[model_key]
        raise AssertionError(f"eval: {t} not found in model")
    
    def eval_submodel(self, t_key: ModelKey) -> "Model":
        """Given an atomic term, evaluate the submodel for that term."""
        res_key_data: dict[ModelKey, OSTerm] = dict()
        for key, val in self.key_data.items():
            if t_key.is_prefix(key):
                res_key_data[key.get_suffix(t_key)] = val
        return Model(key_data=res_key_data)

    def update_partial_term(self, thy: OSTheory, key: ModelKey, pt: PartialTerm):
        """Update location at key."""
        parts = key.name.split(".")
        assert len(parts) > 0 and len(parts[0]) > 0
        var_name = parts[0]
        sub_key = key.get_suffix(ModelKey(var_name, []))
        if var_name not in self.var_data:
            raise AssertionError(f"update_partial_term: variable {var_name} not found")
        self.var_data[var_name] = self.var_data[var_name].update(
            thy, sub_key, pt)

    def extract_partial_term(self, thy: OSTheory, ty: OSType) -> PartialTerm:
        """Extract partial term from submodel."""

        # Primitive type case
        if isinstance(ty, (os_struct.OSPrimType, os_struct.OSBoundType)):
            if base_key in self.key_data:
                return FullTerm(self.key_data[base_key])
            else:
                return UnknownTerm(type=ty)

        # Map case
        elif os_struct.is_map_type(ty):
            _, val_ty = ty.params
            all_keys: set[OSTerm] = set()
            for key in self.key_data:
                if key.name.startswith(".get") or key.name.startswith(".indom"):
                    all_keys.add(key.indices[0])
            data: dict[OSTerm, PartialTerm] = dict()
            indom_data: dict[OSTerm, bool] = dict()
            for key in all_keys:
                data[key] = self.extract_partial_term_for_key(thy, ModelKey(".get", [key]), val_ty)
                indom_data[key] = self.extract_partial_term_for_key(thy, ModelKey(".indom", [key]), os_struct.Bool)
            return PartialMapTerm(data, indom_data, type=ty)

        # Sequence case
        elif os_struct.is_seq_type(ty):
            val_ty, = ty.params
            all_keys: set[OSTerm] = set()
            for key in self.key_data:
                if key.name.startswith(".index"):
                    all_keys.add(key.indices[0])
            data: dict[int, PartialTerm] = dict()
            for key in all_keys:
                assert isinstance(key, os_term.OSNumber)
                data[key.val] = self.extract_partial_term_for_key(thy, ModelKey(".index", [key]), val_ty)
            length = self.extract_partial_term_for_key(thy, ModelKey(".length", []), os_struct.Int)
            return PartialSeqTerm(data, length, type=ty)

        # Struct case
        elif isinstance(ty, os_struct.OSStructType):
            struct = thy.structs[ty.name]
            vals: list[tuple[str, OSTerm]] = []
            for field in struct.fields:
                name = field.field_name
                field_ty = thy.get_field_type(ty, name)
                vals.append((name, self.extract_partial_term_for_key(thy, ModelKey(f".{name}", []), field_ty)))
            return PartialStructTerm(ty.name, vals)

        # Datatype case
        elif isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.datatypes:
            datatype = thy.datatypes[ty.name]
            id = self.extract_partial_term_for_key(thy, ModelKey(".id", []), os_struct.Int)
            if isinstance(id, UnknownTerm):
                return UnknownTerm(type=ty)

            if not (isinstance(id, FullTerm) and isinstance(id.t, os_term.OSNumber)):
                raise AssertionError(f"id {repr(id)} is not a number")
            id_val = id.t.val
            branch = datatype.branches[id_val]

            args: list[OSTerm] = []
            for param_name, _ in branch.params:
                param_ty = thy.get_field_type(ty, param_name)
                args.append(self.extract_partial_term_for_key(thy, ModelKey(f".{param_name}", []), param_ty))
            return PartialFunTerm(branch.constr_name, args, type=ty)
        else:
            raise NotImplementedError(f"extract_partial_term: {ty}")

    def extract_partial_term_for_key(self, thy: OSTheory, key: ModelKey, ty: OSType) -> PartialTerm:
        """Extract partial term for a given key."""
        return self.eval_submodel(key).extract_partial_term(thy, ty)

    def compute_var(self, thy: OSTheory, name: str, ty: OSType):
        """Compute (partial) value of variable and store in var_data."""
        submodel = self.eval_submodel(ModelKey(name, []))
        pt = submodel.extract_partial_term(thy, ty)
        self.var_data[name] = pt
    
    def evaluate_term(self, thy: OSTheory, t: OSTerm) -> PartialTerm:
        """Extract partial term for arbitrary term."""
        # Constant case
        if is_literal_term(thy, t):
            return FullTerm(t)

        # Type conversion cases
        elif os_term.is_fun(t, "int"):
            arg = self.evaluate_term(thy, t.args[0])
            assert isinstance(arg, FullTerm) and isinstance(arg.t, os_term.OSNumber)
            return FullTerm(os_term.OSNumber(arg.t.val, os_struct.Int))
        
        elif os_term.is_fun(t, "ite"):
            eval_cond = self.evaluate_term(thy, t.args[0])
            assert isinstance(eval_cond, FullTerm) and isinstance(eval_cond.t, os_term.OSNumber)
            if eval_cond.t.val:
                return self.evaluate_term(thy, t.args[1])
            else:
                return self.evaluate_term(thy, t.args[2])

        # Arithmetic functions
        elif isinstance(t, os_term.OSOp):
            args = [self.evaluate_term(thy, arg) for arg in t.args]
            vals: list[int | bool] = []
            for arg in args:
                assert isinstance(arg, FullTerm) and isinstance(arg.t, os_term.OSNumber)
                vals.append(arg.t.val)
            res_val, res_ty = os_term.eval_op(t.op, t.args[0].type, vals)
            return FullTerm(os_term.OSNumber(res_val, type=res_ty))

        # Atomic case
        elif os_term.is_atomic_term(t):
            name, indices = os_term.dest_atomic_term(t)

            # First evaluate all indices, make sure they are concrete terms
            eval_indices = list()
            for idx in indices:
                eval_idx = self.evaluate_term(thy, idx)
                if not isinstance(eval_idx, FullTerm):
                    raise AssertionError(f"index {idx} evaluates to {repr(eval_idx)}")
                eval_indices.append(eval_idx.t)
            key = ModelKey(name, eval_indices)

            parts = name.split(".")
            if parts[0] not in self.var_data:
                raise AssertionError(f"evaluate_term: variable {parts[0]} not found")
            sub_key = key.get_suffix(ModelKey(parts[0], []))
            res = self.var_data[parts[0]].evaluate(thy, sub_key)
            return res

        # Map update case
        elif os_term.is_fun(t, "updateMap"):
            k, v, m = t.args
            partial_k = self.evaluate_term(thy, k)
            if not (isinstance(partial_k, FullTerm) and is_literal_term(thy, partial_k.t)):
                raise AssertionError(f"evaluate_term: unexpected {partial_k} for key")
            partial_m = self.evaluate_term(thy, m)
            partial_v = self.evaluate_term(thy, v)
            return partial_m.update(thy, ModelKey(f".get", [partial_k.t]), partial_v)
        
        # Map access case
        elif os_term.is_fun(t, "get"):
            k, m = t.args
            partial_k = self.evaluate_term(thy, k)
            if not (isinstance(partial_k, FullTerm) and is_literal_term(thy, partial_k.t)):
                raise AssertionError(f"evaluate_term: unexpected {partial_k} for key")
            partial_m = self.evaluate_term(thy, m)
            return partial_m.evaluate(thy, ModelKey(f".get", [partial_k.t]))
        
        elif os_term.is_fun(t, "indom"):
            raise NotImplementedError

        # Structure update case
        elif isinstance(t, os_term.OSStructUpdate):
            partial_t = self.evaluate_term(thy, t.ori_expr)
            for update in t.updates:
                partial_e = self.evaluate_term(thy, update.expr)
                partial_t = partial_t.update(thy, ModelKey(f".{update.field_name}", []), partial_e)
            return partial_t

        # Structure value
        elif isinstance(t, os_term.OSStructVal):
            partial_vals = list()
            for field, field_t in t.vals:
                partial_vals.append((field, self.evaluate_term(thy, field_t)))
            partial_t = PartialStructTerm(t.struct_name, partial_vals)
            return partial_t
        
        # Field access
        elif isinstance(t, os_term.FieldGet):
            partial_expr = self.evaluate_term(thy, t.expr)
            if isinstance(partial_expr, PartialStructTerm):
                if t.field in partial_expr.val_map:
                    return partial_expr.val_map[t.field]
                else:
                    raise AssertionError
            else:
                raise NotImplementedError
        
        # Functions in the theory
        elif isinstance(t, os_term.OSFun) and t.func_name in thy.fixps:
            expand_t = os_simplify.rewrite_def(thy, t)
            return self.evaluate_term(thy, expand_t)
        
        elif isinstance(t, os_term.OSFun) and t.func_name in thy.constr_datatype:
            args = [self.evaluate_term(thy, arg) for arg in t.args]
            return PartialFunTerm(t.func_name, args, type=t.type)

        # Sequence functions
        elif os_term.is_fun(t, "seq_append"):
            a, b = t.args
            a = self.evaluate_term(thy, a)
            b = self.evaluate_term(thy, b)
            if isinstance(a, UnknownTerm) or isinstance(b, UnknownTerm):
                return UnknownTerm(type=t.type)
            if not isinstance(a, PartialSeqTerm):
                raise AssertionError(f"evaluate_term on {t}: unexpected {a}")
            if not isinstance(b, PartialSeqTerm):
                raise AssertionError(f"evaluate_term on {t}: unexpected {b}")
            return seq_append_partial(a, b)

        elif os_term.is_fun(t, "seq_cons"):
            x, xs = t.args
            x = self.evaluate_term(thy, x)
            xs = self.evaluate_term(thy, xs)
            if isinstance(xs, UnknownTerm):
                return UnknownTerm(type=t.type)
            if not isinstance(xs, PartialSeqTerm):
                raise AssertionError(f"evaluate_term on {t}: unexpected {xs}")
            return seq_cons_partial(x, xs)

        elif os_term.is_fun(t, "seq_update"):
            k, v, seq = t.args
            k = self.evaluate_term(thy, k)
            v = self.evaluate_term(thy, v)
            seq = self.evaluate_term(thy, seq)
            if isinstance(seq, UnknownTerm):
                return UnknownTerm(type=t.type)
            if not isinstance(seq, PartialSeqTerm):
                raise AssertionError(f"evaluate term on {t}: unexpected {seq}")

            assert isinstance(k, FullTerm) and isinstance(k.t, os_term.OSNumber)
            return seq_update_partial(k.t.val, v, seq)

        elif os_term.is_fun(t, "seq_slice"):
            start, end, seq = t.args
            start = self.evaluate_term(thy, start)
            end = self.evaluate_term(thy, end)
            seq = self.evaluate_term(thy, seq)

            if isinstance(seq, UnknownTerm):
                return UnknownTerm(type=t.type)
            if not isinstance(seq, PartialSeqTerm):
                raise AssertionError(f"evaluate term on {t}: unexpected {seq}")

            assert isinstance(start, FullTerm) and isinstance(start.t, os_term.OSNumber)
            assert isinstance(end, FullTerm) and isinstance(end.t, os_term.OSNumber)
            return seq_slice_partial(start.t.val, end.t.val, seq)

        elif os_term.is_fun(t, "seq_repeat"):
            value, n = t.args
            value = self.evaluate_term(thy, value)
            n = self.evaluate_term(thy, n)

            assert isinstance(n, FullTerm) and isinstance(n.t, os_term.OSNumber)
            return seq_repeat_partial(value, n.t.val)

        elif os_term.is_fun(t, "seq_remove"):
            i, seq = t.args
            i = self.evaluate_term(thy, i)
            seq = self.evaluate_term(thy, seq)

            if isinstance(seq, UnknownTerm):
                return UnknownTerm(type=t.type)
            if not isinstance(seq, PartialSeqTerm):
                raise AssertionError(f"evaluate term on {t}: unexpected {seq}")

            assert isinstance(i, FullTerm) and isinstance(i.t, os_term.OSNumber)
            return seq_remove_partial(i.t.val, seq)

        else:
            raise AssertionError(f"evaluate_term on {t}, of type {type(t)}")


def is_literal_term(thy: OSTheory, t: OSTerm) -> bool:
    """Return whether `t` is a literal term.
    
    A literal term is either a number or a datatype constructor
    applied to literal terms.

    """
    if isinstance(t, OSNumber):
        return True
    elif isinstance(t, os_term.OSFun):
        if t.func_name in thy.constr_datatype:
            for arg in t.args:
                if not is_literal_term(thy, arg):
                    return False
            return True
        elif t.func_name == "default":
            return True
        elif len(t.args) == 0 and isinstance(t.type, os_struct.OSBoundType) and \
            t.func_name.index("!val!") != -1:
            return True
        else:
            return False
    else:
        return False
    
def get_model_value(thy: OSTheory, z3_model: z3.ModelRef,
                    model_map: dict[str, z3.Z3PPObject],
                    model: Model,
                    t: OSTerm) -> OSTerm:
    """Obtain OSTerm value for a given Z3 value.
    
    Parameters
    ----------
    thy : OSTheory
        the current theory
    z3_model : z3.ModelRef
        Z3 model to be converted
    model_map : dict[str, z3.Z3PPObject]
        mapping from variable name to value in the model
    model : Model
        the model to be built
    t : OSTerm
        term to evaluate in the model
    
    """
    # First, we process the case of numbers and non-atomic terms.
    if t in model.term_data:
        return model.term_data[t]

    res: Optional[OSTerm] = None
    if isinstance(t, OSNumber):
        res = t
    elif isinstance(t, os_term.OSOp):
        if len(t.args) == 1:
            a = get_model_value(thy, z3_model, model_map, model, t.args[0])
            assert isinstance(a, OSNumber)
            if t.op == "!":
                res = OSNumber(not a.val)
            elif t.op == "~":
                res = OSNumber(~a.val, type=t.type)
            elif t.op == "-":
                res = OSNumber(-a.val, type=t.type)
            else:
                raise NotImplementedError(f"get_model_value: {t}")
        elif len(t.args) == 2:
            a = get_model_value(thy, z3_model, model_map, model, t.args[0])
            b = get_model_value(thy, z3_model, model_map, model, t.args[1])
            assert is_literal_term(thy, a) and is_literal_term(thy, b), \
                f"get_model_value for {t}"
            if os_term.is_fun(a, "default") or os_term.is_fun(b, "default"):
                res = os_term.OSFun("default", type=t.type)
            else:
                if t.op != '==' and t.op != '!=':
                    assert isinstance(a, OSNumber) and isinstance(b, OSNumber), \
                        f"get_model_value: {a} {t.op} {b}"

                if t.op == '==':
                    res = OSNumber(a == b)
                elif t.op == '!=':
                    res = OSNumber(a != b)
                elif t.op == '&&':
                    res = OSNumber(a.val and b.val)
                elif t.op == '||':
                    res = OSNumber(a.val or b.val)
                elif t.op == '->':
                    res = OSNumber(not a.val or b.val)
                elif t.op == '==':
                    res = OSNumber(a.val == b.val)
                elif t.op == '!=':
                    res = OSNumber(a.val != b.val)
                elif t.op == '<=':
                    res = OSNumber(a.val <= b.val)
                elif t.op == '<':
                    res = OSNumber(a.val < b.val)
                elif t.op == '>=':
                    res = OSNumber(a.val >= b.val)
                elif t.op == '>':
                    res = OSNumber(a.val > b.val)
                elif t.op == "+":
                    res = OSNumber(a.val + b.val, type=t.type)
                elif t.op == "-":
                    res = OSNumber(a.val - b.val, type=t.type)
                elif t.op == "*":
                    res = OSNumber(a.val * b.val, type=t.type)
                elif t.op == "/":
                    res = OSNumber(a.val / b.val, type=t.type)
                elif t.op == "&":
                    res = OSNumber(a.val & b.val, type=t.type)
                elif t.op == ">>":
                    res = OSNumber(a.val >> b.val, type=t.type)
                elif t.op == "<<":
                    res = OSNumber(a.val << b.val, type=t.type)
                elif t.op == "|":
                    res = OSNumber(a.val | b.val, type=t.type)
                elif t.op == "**":
                    res = OSNumber(a.val ** b.val, type=t.type)
                elif t.op == "%":
                    res = OSNumber(a.val % b.val, type=t.type)
    elif isinstance(t, os_term.OSFun):
        if t.func_name == "default":
            res = t
        elif t.func_name == "ite":
            cond, t1, t2 = [get_model_value(thy, z3_model, model_map, model, arg) for arg in t.args]
            assert isinstance(cond, OSNumber)
            res = t1 if cond.val else t2
        elif t.func_name == "max":
            t1, t2 = [get_model_value(thy, z3_model, model_map, model, arg) for arg in t.args]
            assert isinstance(t1, OSNumber) and isinstance(t2, OSNumber)
            res = t1 if t1.val >= t2.val else t2
        elif t.func_name == "min":
            t1, t2 = [get_model_value(thy, z3_model, model_map, model, arg) for arg in t.args]
            assert isinstance(t1, OSNumber) and isinstance(t2, OSNumber)
            res = t1 if t1.val <= t2.val else t2
        elif t.func_name == "int":
            arg = get_model_value(thy, z3_model, model_map, model, t.args[0])
            assert isinstance(arg, OSNumber), "got %s" % arg
            res = OSNumber(arg.val, type=os_struct.Int)
        elif t.func_name == "int8u":
            arg = get_model_value(thy, z3_model, model_map, model, t.args[0])
            assert isinstance(arg, OSNumber), "got %s %s %s" % (arg, type(arg), repr(arg))
            res = OSNumber(arg.val, type=os_struct.Int8U)
        elif t.func_name == "int16u":
            arg = get_model_value(thy, z3_model, model_map, model, t.args[0])
            assert isinstance(arg, OSNumber), "got %s" % arg
            res = OSNumber(arg.val, type=os_struct.Int16U)
        elif t.func_name == "int32u":
            arg = get_model_value(thy, z3_model, model_map, model, t.args[0])
            assert isinstance(arg, OSNumber), "got %s" % arg
            res = OSNumber(arg.val, type=os_struct.Int32U)
        elif t.func_name in thy.constr_datatype:
            args = t.args
            args_val = [get_model_value(thy, z3_model, model_map, model, arg) for arg in t.args]
            res = os_term.OSFun(t.func_name, *args_val, type=t.type)
        elif t.func_name in thy.axiom_func and t.func_name not in [
                "indom", "get", "emptyMap", "updateMap", "range", "range8"] and \
                not t.func_name.startswith("seq_"):
            args = t.args
            args_val = [get_model_value(thy, z3_model, model_map, model, arg) for arg in t.args]
            z3_func = z3.Function(
                t.func_name, *(os_z3wrapper.get_Z3type(thy, arg.type) for arg in t.args),
                os_z3wrapper.get_Z3type(thy, t.type))
            val = z3_model.eval(z3_func(*args_val))
            res = convert_z3_expr(val)

    if res is not None:
        model.term_data[t] = res
        return res

    if not os_term.is_atomic_term(t):
        raise AssertionError(f"get_model_value: non-atomic term {t}")

    # From here on, term `t` is assumed to be atomic
    ty = t.type
    name, indices = os_term.dest_atomic_term(t)
    indices_val = [get_model_value(thy, z3_model, model_map, model, index)
                   for index in indices]
    model_key = ModelKey(name, indices_val)
    if model_key in model.key_data:
        return model.key_data[model_key]

    if isinstance(ty, os_struct.OSPrimType):
        # Primitive type, convert value directly
        if name not in model_map:
            # Use default value here
            if os_struct.is_num_type(ty):
                return os_term.OSNumber(0, type=ty)
            elif ty == os_struct.Bool:
                return os_term.OSNumber(False)
            else:
                raise NotImplementedError(f"Default value for primitive type {ty}")
        else:
            if len(indices) > 0:
                z3_func = z3.Function(
                    name, *(os_z3wrapper.get_Z3type(thy, index.type) for index in indices),
                    os_z3wrapper.get_Z3type(thy, ty))
                args = []
                for index_val in indices_val:
                    assert isinstance(index_val, OSNumber)
                    args.append(index_val.val)
                val = z3_model.eval(z3_func(*args))
            else:
                val = model_map[name]
            res = convert_z3_expr(val)

    elif isinstance(ty, os_struct.OSStructType):
        raise AssertionError("get_model_value: structure type")

    elif isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.datatypes:
        raise AssertionError(f"get_model_value: datatype {ty} for {t}")

    elif isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.typedefs:
        raise AssertionError("get_model_value: typedef")

    elif os_struct.is_map_type(ty):
        raise AssertionError(f"get_model_value: map type, {t} has type {ty}")
        
    elif os_struct.is_seq_type(ty):
        raise AssertionError(f"get_model_value: sequence type, {t} has type {ty}")

    elif isinstance(ty, os_struct.OSBoundType):
        # Type parameter: should always be a variable
        if len(indices) > 0:
            z3_func = z3.Function(
                name, *(os_z3wrapper.get_Z3type(thy, index.type) for index in indices),
                os_z3wrapper.get_Z3type(thy, ty))
            args = []
            for index_val in indices_val:
                assert isinstance(index_val, OSNumber)
                args.append(index_val.val)
            z3_val = z3_model.eval(z3_func(*args))
        else:
            z3_val = model_map[name]
        assert isinstance(z3_val, z3.ExprRef)
        res = os_term.OSFun(z3_val.decl().name(), type=ty)

    elif isinstance(ty, os_struct.OSFunctionType):
        raise NotImplementedError("get_model_for_val: function type")
    else:
        raise NotImplementedError("get_model_for_val for type %s" % ty)
    
    # Add value for t itself
    model.key_data[model_key] = res
    return res

def convert_model(thy: OSTheory,
                  assumes: Iterable[OSTerm],
                  concl: OSTerm,
                  z3_model: z3.ModelRef,
                  verbose: bool = False,
                  check_model: bool = False) -> Model:
    """Convert a Z3 model to a more readable form.
    
    Parameters
    ----------
    thy : OSTheory
        the current theory
    z3_model : z3.ModelRef
        the original Z3 model
    verbose : bool, default to False
        print out additional information during model conversion
    check_model : bool, default to False
        check the model in the proof state

    """
    # os_term.CHECK_INIT_TYPE = True

    # Prepare model_map: maps each variable name to value in the model
    model_map: dict[str, z3.Z3PPObject] = dict()
    for decl in z3_model.decls():
        assert isinstance(decl, z3.FuncDeclRef)
        val = z3_model[decl]
        model_map[decl.name()] = val

    # Evaluate each assumption and conclusion
    model = Model()
    for assume in assumes:
        get_model_value(thy, z3_model, model_map, model, assume)
    get_model_value(thy, z3_model, model_map, model, concl)

    if check_model:
        for assume in assumes:
            eval_prop = model.eval(assume)
            if eval_prop != os_term.true:
                raise AssertionError(f"Assumption {assume} evaluate to {eval_prop}, expected true")
        eval_concl = model.eval(concl)
        if eval_concl != os_term.false:
            raise AssertionError(f"Goal {concl} evaluate to {eval_prop}, expected false")

    # os_term.CHECK_INIT_TYPE = False
    return model

def fill_by_defining_eq(thy: OSTheory, model: Model, define_eq: OSTerm):
    """Fill by defining equation on the model."""
    lhs, rhs = define_eq.lhs, define_eq.rhs
    if not os_term.is_atomic_term(lhs):
        raise AssertionError("fill_by_defining_eq: lhs is not atomic term")
    name, indices = os_term.dest_atomic_term(lhs)

    # First evaluate all indices, make sure they are concrete terms
    eval_indices = list()
    for idx in indices:
        eval_idx = model.evaluate_term(thy, idx)
        if not isinstance(eval_idx, FullTerm):
            raise AssertionError(f"index {idx} evaluates to {repr(eval_idx)}")
        eval_indices.append(eval_idx.t)
    key = ModelKey(name, eval_indices)

    pt = model.evaluate_term(thy, rhs)
    model.update_partial_term(thy, key, pt)

def fill_by_defining_eqs(thy: OSTheory, var_ctxt: VarContext, model: Model,
                         define_eqs: list[OSTerm]):
    """Fill by list of defining equations."""
    order = os_simplify.check_simplify_eqs(var_ctxt, define_eqs)

    # Proceed in reverse order compared to rewriting
    for idx in reversed(order):
        fill_by_defining_eq(thy, model, define_eqs[idx])

def convert_model_on_state(thy: OSTheory,
                           state: ProofState,
                           z3_model: z3.ModelRef,
                           verbose: bool = False,
                           check_model: bool = False) -> Model:
    """Convert a Z3 model to a more readable form.
        
    """
    var_ctxt = state.get_var_context()
    define_eqs, assumes, concl = os_z3wrapper.simplify_state(thy, state)
    model = convert_model(thy, assumes, concl, z3_model, verbose=verbose,
                          check_model=check_model)
    
    # Find model value for each variable
    for var in state.fixes:
        model.compute_var(thy, var.name, var.type)

    # Complete using defining equations
    fill_by_defining_eqs(thy, var_ctxt, model, define_eqs)

    return model


class DiagnosticInfo:
    """Diagnostic information for a given term."""
    def __init__(self, t: OSTerm, eval_t: OSTerm, childs: Iterable["DiagnosticInfo"]):
        self.t = t
        self.eval_t = eval_t
        self.childs: tuple[DiagnosticInfo] = tuple(childs)

    def export(self) -> dict:
        """Export info to JSON data."""
        str_t = str(self.t)
        return {
            "t": str_t,
            "short_form": os_util.short_form(str_t, threshold=80),
            "eval_t": str(self.eval_t),
            "childs": [child.export() for child in self.childs]
        }


def diagnose_term(thy: OSTheory, t: OSTerm, model: Model) -> DiagnosticInfo:
    """Obtain diagnostic info for the given term."""
    eval_t = model.eval(t)
    childs: list[DiagnosticInfo] = []
    if os_term.is_ite(t):
        cond, t1, t2 = t.args
        childs.append(diagnose_term(thy, cond, model))
        if childs[-1].eval_t == OSNumber(True):
            childs.append(diagnose_term(thy, t1, model))
        else:
            childs.append(diagnose_term(thy, t2, model))
    elif os_term.is_conj(t):
        conjs = os_term.split_conj(t)
        for conj in conjs:
            childs.append(diagnose_term(thy, conj, model))
    return DiagnosticInfo(t, eval_t, childs)

def diagnose_query(thy: OSTheory, state: ProofState, model: Model):
    # Write diagnostic information
    json_data = dict()
    json_data["assume"] = list()
    json_data["concl"] = list()
    for assume in state.assumes:
        if not os_theory.is_defining_eq(thy, assume.prop):
            json_data["assume"].append(diagnose_term(thy, assume.prop, model).export())
    json_data["concl"].append(diagnose_term(thy, state.concl.prop, model).export())
    with open("app/meta-viewer/src/assets/diagnostic.json", "w", encoding='utf-8') as file:
        file.write(json.dumps(json_data, indent=4))
