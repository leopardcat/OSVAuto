"""
Definition of OS terms
"""

from typing import Iterable, Optional, TypeGuard
from osverify import os_struct
from osverify.os_struct import OSType
from osverify.os_util import indent, variant_names


"""
Flag for checking type is initialized during term construction.

During parsing, it is not necessary to provide types for all terms
(they will be filled in by type inference), so usually this flag is
left at False. Set this flag to True to enable this check, for example
when constructing models from SMT counterexamples.

"""
CHECK_INIT_TYPE = False


class OSTermException(Exception):
    def __init__(self, msg: str):
        self.msg = msg

    def __str__(self):
        return self.msg


class VarContext:
    """Context of type parameters and variable declarations."""
    def __init__(self, data: Iterable["OSVar"] = tuple()):
        # Type parameters
        self.type_params: list[str] = list()

        # Variable declarations
        self.data = list(data)

    def add_var_decl(self, var_name: str, var_type: Optional[OSType] = None):
        """Add variable declaration.""" 
        self.data.append(OSVar(var_name, type=var_type))

    def del_var_decl(self, var_name: str):
        """Remove variable declaration."""
        for i in reversed(range(len(self.data))):
            if self.data[i].name == var_name:
                del self.data[i]
                return

        # Not found
        raise AssertionError(f"del_var_decl: variable {var_name} is not defined")

    def update_var_decl(self, var_name: str, var_type: OSType):
        """Update type of variable (originally None) to the given type."""
        for i in reversed(range(len(self.data))):
            if self.data[i].name == var_name:
                assert self.data[i].type is None, f"update_var_decl: type of {var_name} is not None"
                self.data[i] = OSVar(var_name, type=var_type)
                return
            
        # Not found
        raise AssertionError(f"update_var_decl: variable {var_name} is not defined")

    def contains_var(self, name: str) -> bool:
        """Check whether the given name is declared in the context."""
        for var in self.data:
            if var.name == name:
                return True
        return False

    def get_var_type(self, name: str) -> OSType:
        """Obtain the type of the given variable."""
        for var in reversed(self.data):
            if var.name == name:
                return var.type
        raise AssertionError(f"get_var_type: variable {name} not found")

    def variant_var(self, var: "OSVar") -> "OSVar":
        """Obtain variant of the given variable."""
        names = set(var.name for var in self.data)
        new_name = variant_names(names, var.name)
        return OSVar(new_name, type=var.type)

    def variant_vars(self, vars: Iterable["OSVar"]) -> list["OSVar"]:
        """Obtain variants of a list of variables."""
        names = set(var.name for var in self.data)
        new_vars = list()
        for var in vars:
            new_name = variant_names(names, var.name)
            names.add(new_name)
            new_vars.append(OSVar(new_name, type=var.type))
        return new_vars
    
    def is_fresh_names(self, names: Iterable[str]) -> bool:
        """Determine whether the given names are fresh for this context.
        
        Note this checks whether each name is fresh, as well as there
        is no repetition in the names.
        
        """
        for var in self.data:
            if var.name in names:
                return False
        if len(names) != len(set(names)):
            return False
        return True
    
    def clone(self) -> "VarContext":
        """Make a copy of self."""
        return VarContext(tuple(self.data))
    
    def is_free(self, t: "OSTerm") -> bool:
        """Return whether all variables in t are contained in context."""
        _, vars = t.get_vars()
        for var in vars:
            if not self.contains_var(var.name):
                return False
        return True


class Visitor:
    """Wrapper class for visit function."""
    def visit(self, var_ctxt: VarContext, t: "OSTerm"):
        raise NotImplementedError


class Transformer:
    """Wrapper class for transform function."""
    def visit(self, var_ctxt: VarContext, t: "OSTerm") -> "OSTerm":
        raise NotImplementedError


class GenField:
    """Base class for generalized fields"""

    # Each generalized field has a type, that indicates the expected type
    # of values of the field.
    type: Optional[OSType]

    def print_incr(self, res: list[str], indent: int):
        raise NotImplementedError(f"print_incr: {type(self)}")

    def subst(self, inst: dict[str, "OSTerm"]) -> "GenField":
        """Substitute variables for terms inside generalized field."""
        raise NotImplementedError("subst: %s" % type(self))
    
    def subst_type(self, tyinst: dict[str, OSType]) -> "GenField":
        """Substitute type variables for types inside generalized field."""
        raise NotImplementedError("subst_type: %s" % type(self))

    def assert_type_checked(self):
        """Assert the given term is fully type-checked."""
        raise NotImplementedError("assert_type_checked: %s" % type(self))

    def assert_init_type(self):
        if CHECK_INIT_TYPE and self.type is None:
            raise AssertionError("When building %s, need to provide type" % self)

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        """Visit the given term recursively."""
        raise NotImplementedError("traverse: %s" % type(self))

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> "GenField":
        """Transform the given term recursively."""
        raise NotImplementedError("transform: %s" % type(self))

    def get_vars_inplace(self, ty_vars: list[str], vars: list["OSVar"]):
        """Add set of variables into vars."""
        raise NotImplementedError("get_vars_inplace: %s" % type(self))

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        """Return the set of functions appearing in the term."""
        raise NotImplementedError("get_func_inplace: %s" % type(self))

class AtomGenField(GenField):
    """Atomic generalized field."""
    def __init__(self, name: str, *, type: Optional[OSType] = None):
        self.name = name
        self.type = type
        self.assert_init_type()

    def print_incr(self, res: list[str], indent: int):
        res.append(self.name)
    
    def __repr__(self):
        return f"AtomGenField({self.name}, {self.type})"
    
    def __eq__(self, other):
        return isinstance(other, AtomGenField) and self.name == other.name and \
            self.type == other.type
    
    def __hash__(self):
        return hash(("AtomGenField", self.name, self.type))

    def subst(self, inst: dict[str, "OSTerm"]) -> GenField:
        return self

    def subst_type(self, tyinst: dict[str, OSType]) -> GenField:
        return self
    
    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        pass

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> GenField:
        return self

    def get_vars_inplace(self, ty_vars: list[str], vars: list["OSVar"]):
        if self.type:
            self.type.get_vars_inplace(ty_vars)

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        pass

class IndexGenField(GenField):
    """Sequence/Map index access generalized field."""
    def __init__(self, base: GenField, index: "OSTerm", *, type: Optional[OSType] = None):
        self.base = base
        self.index = index
        self.type = type
        self.assert_init_type()

    def print_incr(self, res: list[str], indent: int):
        self.base.print_incr(res, indent)
        res.append("[")
        self.index.print_incr(res, indent)
        res.append("]")
    
    def __repr__(self):
        return f"IndexGenField({repr(self.base)}, {repr(self.index)}, {self.type})"
    
    def __eq__(self, other):
        return isinstance(other, IndexGenField) and self.base == other.base and \
            self.index == other.index and self.type == other.type
    
    def __hash__(self):
        return hash(("IndexGenField", self.base, self.index, self.type))

    def subst(self, inst: dict[str, "OSTerm"]) -> GenField:
        return IndexGenField(self.base.subst(inst), self.index.subst(inst),
                             type=self.type)

    def subst_type(self, tyinst: dict[str, OSType]) -> GenField:
        return IndexGenField(self.base.subst_type(tyinst), self.index.subst(tyinst),
                             type=self.type.subst(tyinst))

    def assert_type_checked(self):
        self.base.assert_type_checked()
        self.index.assert_type_checked()
        assert self.type is not None, "assert_type_checked: failed on %s" % self

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        self.base.traverse(var_ctxt, visitor)
        self.index.traverse(var_ctxt, visitor)

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> GenField:
        return IndexGenField(self.base.transform(var_ctxt, transformer),
                             self.index.transform(var_ctxt, transformer),
                             type=self.type)

    def get_vars_inplace(self, ty_vars: list[str], vars: list["OSVar"]):
        self.base.get_vars_inplace(ty_vars, vars)
        self.index.get_vars_inplace(ty_vars, vars)
        if self.type:
            self.type.get_vars_inplace(ty_vars)

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        self.base.get_funcs_inplace(funcs)
        self.index.get_funcs_inplace(funcs)

class FieldGetGenField(GenField):
    """Field access generalized field."""
    def __init__(self, base: GenField, field: str, *, type: Optional[OSType] = None):
        self.base = base
        self.field = field
        self.type = type
        self.assert_init_type()

    def print_incr(self, res: list[str], indent: int):
        self.base.print_incr(res, indent)
        res.append(f".{self.field}")
    
    def __repr__(self):
        return f"FieldGetGenField({repr(self.base)}, {self.field}, {self.type})"

    def __eq__(self, other):
        return isinstance(other, FieldGetGenField) and self.base == other.base and \
            self.field == other.field and self.type == other.type

    def __hash__(self):
        return hash(("FieldGetGenField", self.base, self.field, self.type))

    def subst(self, inst: dict[str, "OSTerm"]) -> GenField:
        return FieldGetGenField(self.base.subst(inst), self.field, type=self.type)

    def subst_type(self, tyinst: dict[str, OSType]) -> GenField:
        return FieldGetGenField(self.base.subst_type(tyinst), self.field,
                                type=self.type.subst(tyinst))

    def assert_type_checked(self):
        self.base.assert_type_checked()
        assert self.type is not None, "assert_type_checked: failed on %s" % self

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        self.base.traverse(var_ctxt, visitor)

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> GenField:
        return FieldGetGenField(self.base.transform(var_ctxt, transformer),
                                self.field, type=self.type)

    def get_vars_inplace(self, ty_vars: list[str], vars: list["OSVar"]):
        self.base.get_vars_inplace(ty_vars, vars)
        if self.type:
            self.type.get_vars_inplace(ty_vars)

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        self.base.get_funcs_inplace(funcs)


class OSTerm:
    """Base class for terms."""

    # Any term has a type
    type: Optional[OSType]

    def __add__(self, other: "OSTerm") -> "OSTerm":
        assert os_struct.is_num_type(self.type) and self.type == other.type, \
            "__add__: unexpected types %s, %s" % (self.type, other.type)
        return OSOp("+", self, other, type=self.type)

    def __sub__(self, other: "OSTerm") -> "OSTerm":
        assert os_struct.is_num_type(self.type) and self.type == other.type, \
            "__sub__: unexpected types %s, %s" % (self.type, other.type)
        return OSOp("-", self, other, type=self.type)

    def __neg__(self) -> "OSTerm":
        assert os_struct.is_num_type(self.type), \
            "__neg__: unexpected type %s" % self.type
        return OSOp("-", self, type=self.type)

    def __le__(self, other: "OSTerm") -> "OSTerm":
        assert os_struct.is_num_type(self.type) and self.type == other.type, \
            "__le__: unexpected types %s, %s" % (self.type, other.type)
        return OSOp("<=", self, other, type=os_struct.Bool)

    def __lt__(self, other: "OSTerm") -> "OSTerm":
        assert os_struct.is_num_type(self.type) and self.type == other.type, \
            "__lt__: unexpected types %s, %s" % (self.type, other.type)
        return OSOp("<", self, other, type=os_struct.Bool)

    def __ge__(self, other: "OSTerm") -> "OSTerm":
        assert os_struct.is_num_type(self.type) and self.type == other.type, \
            "__ge__: unexpected types %s, %s" % (self.type, other.type)
        return OSOp(">=", self, other, type=os_struct.Bool)

    def __gt__(self, other: "OSTerm") -> "OSTerm":
        assert os_struct.is_num_type(self.type) and self.type == other.type, \
            "__gt__: unexpected types %s, %s" % (self.type, other.type)
        return OSOp(">", self, other, type=os_struct.Bool)
    
    @property
    def lhs(self) -> "OSTerm":
        return lhs(self)
    
    @property
    def rhs(self) -> "OSTerm":
        return rhs(self)

    def priority(self):
        """Return priority of a term during printing."""
        raise NotImplementedError("priority: %s" % type(self))
    
    def print_incr(self, res: list[str], indent: int):
        """Incrementally print the term."""
        raise NotImplementedError(f"print_incr: {type(self)}")

    def __str__(self):
        res: list[str] = []
        self.print_incr(res, 0)
        return ''.join(res)

    def subst(self, inst: dict[str, "OSTerm"]) -> "OSTerm":
        """Substitute variables for terms according to inst."""
        raise NotImplementedError("subst: %s" % type(self))
    
    def subst_type(self, tyinst: dict[str, OSType]) -> "OSTerm":
        """Substitute type variables for types according to tyinst.
        
        This function assumes that type inference has finished. It may
        raise an exception if type of the term is not set.
        
        """
        return NotImplementedError("subst_type: %s" % type(self))

    def assert_type_checked(self):
        """Assert the given term is fully type-checked."""
        raise NotImplementedError("assert_type_checked: %s" % type(self))
    
    def assert_init_type(self):
        if CHECK_INIT_TYPE and self.type is None:
            raise AssertionError("When building %s, need to provide type" % self)

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        """Visit the given term recursively."""
        raise NotImplementedError("traverse: %s" % type(self))

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> "OSTerm":
        """Transform the given term recursively."""
        raise NotImplementedError("transform: %s" % type(self))

    def get_vars_inplace(self, ty_vars: list[str], vars: list["OSVar"]):
        """Add set of variables into vars."""
        raise NotImplementedError("get_vars_inplace: %s" % type(self))
    
    def get_vars(self) -> tuple[tuple[str], tuple["OSVar"]]:
        """Obtain the set of (type) variables.
        
        Returns
        -------
        tuple[str]
            list of type variables
        tuple[OSVar]
            list of variables
            
        """
        ty_vars, vars = list(), list()
        self.get_vars_inplace(ty_vars, vars)
        return tuple(ty_vars), tuple(vars)
    
    def get_var_context(self) -> VarContext:
        """Create variable context from given term.
        
        This should be used with care, as it only obtains the list of
        type parameters and variables in the term, not in the entire
        problem. Actual variable context for the problem should be used
        whenever available.

        """
        ty_vars, vars = self.get_vars()
        var_ctxt = VarContext(vars)
        var_ctxt.type_params = ty_vars
        return var_ctxt

    def has_var(self, var_name: str) -> bool:
        """Return whether the term contains variable with the given name."""
        _, vars = self.get_vars()
        for var in vars:
            if var.name == var_name:
                return True
        return False
    
    def has_sch_var(self) -> bool:
        """Return whether the term contains a schematic variable."""
        _, vars = self.get_vars()
        return any(var.is_sch_var() for var in vars)
    
    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        """Return the set of functions appearing in the term."""
        raise NotImplementedError("get_func_inplace: %s" % type(self))
    
    def get_funcs(self) -> tuple[tuple[str, OSType]]:
        """Obtain the set of functions appearing in the term."""
        funcs = list()
        self.get_funcs_inplace(funcs)
        return tuple(funcs)
    
    def make_schematic(self, ty_vars: Iterable[str], vars: Iterable["OSVar"]) -> "OSTerm":
        """Change the given variables and type variables into schematic.
        
        In more detail, for each type variable in ty_vars and each variable
        in vars, change it into corresponding schematic (type) variables
        by prefixing '?' to its name. Eventually, this is done by calling
        subst and subst_type functions.

        Parameters
        ----------
        ty_vars : Iterable[str]
            list of type variables to make schematic
        vars : Iterable[OSVar]
            list of variables to make schematic
        
        Returns
        -------
        OSTerm
            result after converting each input (type) variable into schematic
            (type) variables.
        
        """
        tyinst = dict((ty_var, os_struct.OSBoundType('?' + ty_var)) for ty_var in ty_vars)
        inst = dict((var.name, OSVar('?' + var.name, type=var.type)) for var in vars)
        return self.subst(inst).subst_type(tyinst)
    
    def make_all_schematic(self) -> "OSTerm":
        """Change all variables and type variables to schematic."""
        ty_vars, vars = self.get_vars()
        return self.make_schematic(ty_vars, vars)


class OSWildcard(OSTerm):
    """Wildcard.
    
    This occurs as "_" in pattern matching.

    """
    def __init__(self, *, type: Optional[OSType] = None):
        self.type = type
        self.assert_init_type()

    def priority(self):
        return 100
    
    def __eq__(self, other):
        return isinstance(other, OSWildcard) and self.type == other.type

    def print_incr(self, res: list[str], indent: int):
        res.append("_")
    
    def __repr__(self):
        return "OSWildcard(%s)" % self.type

    def __hash__(self):
        return hash(("OSWildCard", self.type))

    def subst(self, inst: dict[str, OSTerm]) -> OSTerm:
        return self
    
    def subst_type(self, tyinst: dict[str, OSType]) -> OSTerm:
        return OSWildcard(type=self.type.subst(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        visitor.visit(var_ctxt, self)

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> OSTerm:
        return transformer.visit(var_ctxt, self)

    def get_vars_inplace(self, ty_vars: list[str], vars: list["OSVar"]):
        if self.type:
            self.type.get_vars_inplace(ty_vars)

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        pass


class OSVar(OSTerm):
    """Variable.
    
    Type of variables are either provided at first or set during type
    inference.

    """
    def __init__(self, name: str, *, type: Optional[OSType] = None):
        self.name = name
        self.type = type
        self.assert_init_type()

    def priority(self):
        return 100

    def __eq__(self, other):
        return isinstance(other, OSVar) and self.name == other.name and self.type == other.type

    def print_incr(self, res: list[str], indent: int):
        res.append(self.name)

    def __repr__(self):
        return "OSVar(%s, %s)" % (repr(self.name), self.type)

    def __hash__(self):
        return hash(("OSVar", self.name, self.type))

    def is_sch_var(self) -> bool:
        """Return whether the variable is a schematic variable.

        Schematic variables are distinguished by its name having
        prefix "?".
        
        """
        return self.name.startswith("?")

    def subst(self, inst: dict[str, OSTerm]) -> OSTerm:
        if self.name in inst:
            if inst[self.name].type != self.type:
                raise AssertionError(
                    f"subst: attempt to substitute {inst[self.name]} with type {inst[self.name].type}" +
                    f" for variable {self} with type {self.type}")
            return inst[self.name]
        else:
            return self
        
    def subst_type(self, tyinst: dict[str, OSType]) -> OSTerm:
        return OSVar(self.name, type=self.type.subst(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        visitor.visit(var_ctxt, self)

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> OSTerm:
        return transformer.visit(var_ctxt, self)

    def get_vars_inplace(self, ty_vars: list[str], vars: list["OSVar"]):
        if self.type:
            self.type.get_vars_inplace(ty_vars)
        if self not in vars:
            vars.append(self)

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        pass


class OSNumber(OSTerm):
    """Numeral constants.
    
    The type of numeral constant may be unknown at first. It is set during
    type inference.

    Attributes
    ----------
    val : int | bool
        value of the constant
    type : OSType
        type of the constant. If the value is boolean, type should be Bool.
        Otherwise type is one of the numeric types.

    """
    def __init__(self, val: int | bool, type: Optional[OSType] = None):
        self.val = val
        self.type = type
        if self.type == os_struct.Bool:
            assert isinstance(val, bool), f"OSNumber: trying to create {self.val} with type bool"
        if isinstance(self.val, bool):
            self.type = os_struct.Bool
        self.assert_init_type()

    def priority(self):
        return 100

    def __eq__(self, other):
        return isinstance(other, OSNumber) and self.val == other.val and self.type == other.type

    def print_incr(self, res: list[str], indent: int):
        if isinstance(self.val, bool):
            if self.val == True:
                res.append("true")
            else:
                res.append("false")
        else:
            res.append(str(self.val))

    def __repr__(self):
        return "OSNumber(%s, %s)" % (self.val, self.type)

    def __hash__(self):
        return hash(("OSNumber", self.val, self.type))

    def subst(self, inst: dict[str, OSTerm]) -> OSTerm:
        return self
    
    def subst_type(self, tyinst: dict[str, OSType]) -> OSTerm:
        return OSNumber(self.val, self.type.subst(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        visitor.visit(var_ctxt, self)

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> OSTerm:
        return transformer.visit(var_ctxt, self)

    def get_vars_inplace(self, ty_vars: list[str], vars: list[OSVar]):
        if self.type:
            self.type.get_vars_inplace(ty_vars)

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        pass


uop_priority = {
    '!': 90, '~': 90, "-": 90,
}

op_priority = {
    "**": 89,
    "*": 87, "/": 87, "%": 87,
    "+": 85, "-": 85,
    '<<': 80, '>>': 80,
    '&': 70,
    '^': 65,
    '|': 60,
    '<': 50, '<=': 50, '>': 50, '>=': 50, '==': 50, '!=': 50,
    '&&': 35,
    '||': 30,
    '->': 25,
}

class OSOp(OSTerm):
    """Application of an operator.
    
    The list of supported operators are:

    Logical operators: ! (unary), &&, ||, ->
    Bitwise operators: ~ (unary), &, ^, |, <<, >>
    Equality operators: ==, !=
    Comparison operators: <, <=, >, >=
    Arithmetic operators: +, -, *, /, - (unary)

    """
    def __init__(self, op: str, *args: OSTerm, type: Optional[OSType] = None):
        self.op = op
        self.args = tuple(args)
        self.type = type
        self.assert_init_type()

    def priority(self):
        if len(self.args) == 1:
            return uop_priority[self.op]
        elif len(self.args) == 2:
            return op_priority[self.op]
        else:
            raise NotImplementedError

    def __eq__(self, other):
        return isinstance(other, OSOp) and self.op == other.op and self.args == other.args

    def print_incr(self, res: list[str], indent: int):
        if len(self.args) == 1:
            res.append(self.op)
            if self.args[0].priority() < self.priority():
                res.append('(')
                self.args[0].print_incr(res, indent)
                res.append(')')
            else:
                self.args[0].print_incr(res, indent)
        elif len(self.args) == 2:
            if self.op == "->":
                As, C = strip_implies(self)
                for i, t in enumerate(As + (C,)):
                    if i > 0:
                        res.append(' ->\n' + ' ' * indent)
                    if t.priority() < self.priority():
                        res.append('(')
                        t.print_incr(res, indent)
                        res.append(')')
                    else:
                        t.print_incr(res, indent)
            else:
                if self.args[0].priority() < self.priority():
                    res.append('(')
                    self.args[0].print_incr(res, indent)
                    res.append(')')
                else:
                    self.args[0].print_incr(res, indent)
                res.append(f' {self.op} ')
                if self.args[1].priority() <= self.priority():
                    res.append('(')
                    self.args[1].print_incr(res, indent)
                    res.append(')')
                else:
                    self.args[1].print_incr(res, indent)
        else:
            raise NotImplementedError

    def __repr__(self):
        return "OSOp(%s, %s, %s)" % (self.op, ", ".join(repr(arg) for arg in self.args), self.type)
    
    def __hash__(self):
        return hash(("OSOp", self.op, self.args, self.type))

    def subst(self, inst: dict[str, OSTerm]) -> OSTerm:
        return OSOp(self.op, *(arg.subst(inst) for arg in self.args), type=self.type)

    def subst_type(self, tyinst: dict[str, OSType]) -> OSTerm:
        return OSOp(self.op, *(arg.subst_type(tyinst) for arg in self.args),
                    type=self.type.subst(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self
        for arg in self.args:
            arg.assert_type_checked()
        if self.op in ['<', '>', '<=', '>=', '==', '!=']:
            assert self.type == os_struct.Bool, \
                "assert_type_checked: failed on %s (actual type %s)" % (self, self.type)

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        for arg in self.args:
            arg.traverse(var_ctxt, visitor)
        visitor.visit(var_ctxt, self)

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> OSTerm:
        args = [arg.transform(var_ctxt, transformer) for arg in self.args]
        return transformer.visit(var_ctxt, OSOp(self.op, *args, type=self.type))

    def get_vars_inplace(self, ty_vars: list[str], vars: list[OSVar]):
        if self.type:
            self.type.get_vars_inplace(ty_vars)
        for arg in self.args:
            arg.get_vars_inplace(ty_vars, vars)

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        # Currently we do not consider operators to be functions
        for arg in self.args:
            arg.get_funcs_inplace(funcs)


class OSFun(OSTerm):
    """Application of a function, predicate, or constructor.
    
    Some functions have special syntax:

    - ite(cond, t1, t2) is written as if (cond) { t1 } else { t2 }
    - pair(t1, t2) is written as (t1, t2)

    literal maps and lists are printed in corresponding syntax

    """
    def __init__(self, func_name: str, *args: OSTerm, type: Optional[OSType] = None):
        self.func_name = func_name
        self.args = tuple(args)
        assert all(isinstance(arg, OSTerm) for arg in self.args)
        self.type = type
        self.assert_init_type()

    def priority(self):
        return 100

    def __eq__(self, other):
        return isinstance(other, OSFun) and self.func_name == other.func_name and \
            self.args == other.args and self.type == other.type

    def print_incr(self, res: list[str], indent: int):
        if self.func_name == "ite":
            res.append("if (")
            self.args[0].print_incr(res, indent + 4)
            res.append(") {\n" + ' ' * (indent + 2))
            self.args[1].print_incr(res, indent + 2)
            res.append('\n' + ' ' * indent + '} else {\n' + ' ' * (indent + 2))
            self.args[2].print_incr(res, indent + 2)
            res.append("\n" + ' ' * indent + '}')
        elif self.func_name == "pair":
            res.append('(')
            self.args[0].print_incr(res, indent)
            res.append(', ')
            self.args[1].print_incr(res, indent)
            res.append(')')
        elif self.func_name == "seq_index":
            idx, seq = self.args
            seq.print_incr(res, indent)
            res.append('[')
            idx.print_incr(res, indent)
            res.append(']')
        elif self.func_name == "get":
            key, map = self.args
            map.print_incr(res, indent)
            res.append('[')
            key.print_incr(res, indent)
            res.append(']')
        elif self.func_name == "updateMap":
            key, val, map = self.args
            map.print_incr(res, indent)
            res.append('[')
            key.print_incr(res, indent)
            res.append(' := ')
            val.print_incr(res, indent)
            res.append(']')
        elif len(self.args) == 0:
            res.append(self.func_name)
        else:
            res.append(self.func_name + '(')
            for i, arg in enumerate(self.args):
                if i > 0:
                    res.append(', ')
                arg.print_incr(res, indent)
            res.append(')')
        
    def __repr__(self):
        if self.args:
            return "OSFun(%s, %s, %s)" % (
                repr(self.func_name), ", ".join(repr(arg) for arg in self.args), self.type)
        else:
            return "OSFun(%s, %s)" % (repr(self.func_name), self.type)

    def __hash__(self):
        return hash(("OSFun", self.func_name, self.args, self.type))

    def subst(self, inst: dict[str, OSTerm]) -> OSTerm:
        return OSFun(self.func_name, *(arg.subst(inst) for arg in self.args), type=self.type)

    def subst_type(self, tyinst: dict[str, OSType]) -> OSTerm:
        return OSFun(self.func_name, *(arg.subst_type(tyinst) for arg in self.args),
                     type=self.type.subst(tyinst))
    
    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self
        for arg in self.args:
            arg.assert_type_checked()

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        for arg in self.args:
            arg.traverse(var_ctxt, visitor)
        visitor.visit(var_ctxt, self)

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> OSTerm:
        args = [arg.transform(var_ctxt, transformer) for arg in self.args]
        return transformer.visit(var_ctxt, OSFun(self.func_name, *args, type=self.type))

    def get_vars_inplace(self, ty_vars: set[str], vars: list[OSVar]):
        if self.type:
            self.type.get_vars_inplace(ty_vars)
        for arg in self.args:
            arg.get_vars_inplace(ty_vars, vars)

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        if len(self.args) == 0:
            func = (self.func_name, self.type)
        else:
            arg_types = [arg.type for arg in self.args]
            func = (self.func_name, os_struct.OSFunctionType(*(arg_types + [self.type])))
        if func not in funcs:
            funcs.append(func)
        for arg in self.args:
            arg.get_funcs_inplace(funcs)


class FieldGet(OSTerm):
    """Access the field of a structure or datatype.
    
    Attributes
    ----------
    expr : OSTerm
        term on which to access the field, should be either a structure
        or value of a datatype.
    field : str
        name of the field.
    type : OSType
        type of the field.

    """
    def __init__(self, expr: OSTerm, field: str, *, type: Optional[OSType] = None):
        self.expr = expr
        self.field = field
        self.type = type
        self.assert_init_type()

    def priority(self):
        return 100
    
    def __eq__(self, other):
        return isinstance(other, FieldGet) and self.expr == other.expr and self.field == other.field

    def print_incr(self, res: list[str], indent: int):
        self.expr.print_incr(res, indent)
        res.append(f'.{self.field}')
    
    def __repr__(self):
        return "FieldGet(%s, %s, %s)" % (repr(self.expr), repr(self.field), self.type)

    def __hash__(self):
        return hash(("FieldGet", self.expr, self.field, self.type))

    def subst(self, inst: dict[str, OSTerm]) -> OSTerm:
        return FieldGet(self.expr.subst(inst), self.field, type=self.type)
    
    def subst_type(self, tyinst: dict[str, OSType]) -> OSTerm:
        return FieldGet(self.expr.subst_type(tyinst), self.field, type=self.type.subst(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self
        self.expr.assert_type_checked()

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        self.expr.traverse(var_ctxt, visitor)
        visitor.visit(var_ctxt, self)

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> OSTerm:
        expr = self.expr.transform(var_ctxt, transformer)
        return transformer.visit(var_ctxt, FieldGet(expr, self.field, type=self.type))

    def get_vars_inplace(self, ty_vars: list[str], vars: list[OSVar]):
        if self.type:
            self.type.get_vars_inplace(ty_vars)
        self.expr.get_vars_inplace(ty_vars, vars)

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        self.expr.get_funcs_inplace(funcs)


class FieldUpdate:
    """Single field update within a structure"""
    def __init__(self, field_name: str, expr: OSTerm = None):
        self.field_name = field_name
        self.expr = expr

    def __eq__(self, other):
        return isinstance(other, FieldUpdate) and self.field_name == other.field_name and \
            self.expr == other.expr

    def print_incr(self, res: list[str], indent: int):
        res.append(f"{self.field_name} := ")
        self.expr.print_incr(res, indent)

    def __repr__(self):
        return "FieldUpdate(%s, %s)" % (self.field_name, repr(self.expr))

    def __hash__(self):
        return hash(("FieldUpdate", self.field_name, self.expr))

    def subst(self, inst: dict[str, OSTerm]) -> "FieldUpdate":
        return FieldUpdate(self.field_name, self.expr.subst(inst))
    
    def subst_type(self, tyinst: dict[str, OSType]) -> "FieldUpdate":
        return FieldUpdate(self.field_name, self.expr.subst_type(tyinst))
    

class OSStructUpdate(OSTerm):
    """Update several fields of a structure.
    
    Attributes
    ----------
    ori_expr : OSTerm
        structure before update
    updates : tuple[FieldUpdate]
        list of updates to the structure
    dict_updates : dict[str, OSTerm]
        mapping from field name to updated value
    type : OSType
        type of the term, automatically derived to be the type of ori_expr.
    
    """
    def __init__(self, ori_expr: OSTerm, updates: Iterable[FieldUpdate]):
        self.ori_expr = ori_expr
        self.updates = tuple(updates)
        self.type = ori_expr.type

        # Update as a dictionary
        self.dict_updates: dict[str, OSTerm] = dict()
        for update in self.updates:
            assert update.field_name not in self.dict_updates, \
                "OSStructUpdate: duplicate field name %s" % update.field_name
            self.dict_updates[update.field_name] = update.expr

        self.assert_init_type()
    
    def priority(self):
        return 100

    def __eq__(self, other):
        return isinstance(other, OSStructUpdate) and self.ori_expr == other.ori_expr and \
            self.updates == other.updates

    def print_incr(self, res: list[str], indent: int):
        self.ori_expr.print_incr(res, indent)
        res.append("{")
        for i, update in enumerate(self.updates):
            if i > 0:
                res.append(", ")
            update.print_incr(res, indent)
        res.append("}")

    def __repr__(self):
        return "OSStructUpdate(%s, %s, %s)" % (repr(self.ori_expr), self.updates, self.type)

    def __hash__(self):
        return hash(("OSStructUpdate", self.ori_expr, self.updates))

    def subst(self, inst: dict[str, OSTerm]) -> OSTerm:
        return OSStructUpdate(self.ori_expr.subst(inst), [update.subst(inst) for update in self.updates])

    def subst_type(self, tyinst: dict[str, OSType]) -> OSTerm:
        return OSStructUpdate(self.ori_expr.subst_type(tyinst),
                              [update.subst_type(tyinst) for update in self.updates])

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self
        self.ori_expr.assert_type_checked()
        for update in self.updates:
            update.expr.assert_type_checked()

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        self.ori_expr.traverse(var_ctxt, visitor)
        for update in self.updates:
            update.expr.traverse(var_ctxt, visitor)
        visitor.visit(var_ctxt, self)

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> OSTerm:
        updates = [FieldUpdate(update.field_name, update.expr.transform(var_ctxt, transformer))
                   for update in self.updates]
        ori_expr = self.ori_expr.transform(var_ctxt, transformer)
        return transformer.visit(var_ctxt, OSStructUpdate(ori_expr, updates))

    def get_vars_inplace(self, ty_vars: list[str], vars: list[OSVar]):
        self.ori_expr.get_vars_inplace(ty_vars, vars)
        for update in self.updates:
            update.expr.get_vars_inplace(ty_vars, vars)

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        self.ori_expr.get_funcs_inplace(funcs)
        for update in self.updates:
            update.expr.get_funcs_inplace(funcs)

class OSStructUpdateGen(OSTerm):
    """Generalized structure updates.

    This is syntactic sugar for updates deep inside a structure.

    Attributes
    ----------
    ori_expr : OSTerm
        structure before update.
    gen_field : GenField
        generalized field name (including sequence/map index and field
        access).
    expr : OSTerm
        updated term at the generalized field.
    type : OSType
        type of the term, automatically derived to be the type of ori_expr.

    """
    def __init__(self, ori_expr: OSTerm, gen_field: GenField, expr: OSTerm):
        self.ori_expr = ori_expr
        self.gen_field = gen_field
        self.expr = expr
        self.type = ori_expr.type

    def priority(self):
        return 100
    
    def __eq__(self, other):
        return isinstance(other, OSStructUpdateGen) and \
            self.gen_field == other.gen_field and \
            self.expr == other.expr
    
    def print_incr(self, res: list[str], indent: int):
        self.ori_expr.print_incr(res, indent)
        res.append("{|")
        self.gen_field.print_incr(res, indent)
        res.append(" := ")
        self.expr.print_incr(res, indent)
        res.append("|}")

    def __repr__(self):
        return "OSStructUpdateGen(%s, %s, %s)" % (
            repr(self.ori_expr), repr(self.gen_field), repr(self.expr))

    def __hash__(self):
        return hash(("OSStructUpdateGen", self.ori_expr, self.gen_field, self.expr))

    def subst(self, inst: dict[str, OSTerm]) -> OSTerm:
        return OSStructUpdateGen(
            self.ori_expr.subst(inst), self.gen_field.subst(inst),
            self.expr.subst(inst))

    def subst_type(self, tyinst: dict[str, OSType]) -> OSTerm:
        return OSStructUpdateGen(
            self.ori_expr.subst_type(tyinst), self.gen_field.subst_type(tyinst),
            self.expr.subst_type(tyinst))

    def assert_type_checked(self):
        self.ori_expr.assert_type_checked()
        self.gen_field.assert_type_checked()
        self.expr.assert_type_checked()
        assert self.type is not None, "assert_type_checked: failed on %s" % self

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        self.ori_expr.traverse(var_ctxt, visitor)
        self.gen_field.traverse(var_ctxt, visitor)
        self.expr.traverse(var_ctxt, visitor)
        visitor.visit(var_ctxt, self)

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> GenField:
        return transformer.visit(var_ctxt, OSStructUpdateGen(
            self.ori_expr.transform(var_ctxt, transformer),
            self.gen_field.transform(var_ctxt, transformer),
            self.expr.transform(var_ctxt, transformer)))

    def get_vars_inplace(self, ty_vars: list[str], vars: list["OSVar"]):
        self.ori_expr.get_vars_inplace(ty_vars, vars)
        self.gen_field.get_vars_inplace(ty_vars, vars)
        self.expr.get_vars_inplace(ty_vars, vars)

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        self.ori_expr.get_funcs_inplace(funcs)
        self.gen_field.get_funcs_inplace(funcs)
        self.expr.get_funcs_inplace(funcs)

class OSStructVal(OSTerm):
    """Structure literal expression.
    
    Each literal is given by structure name, and a list of correspondence
    between field names and values.

    Attributes
    ----------
    struct_name : str
        name of the structure
    vals : tuple[tuple[str, OSTerm]]
        list of field name and value pairs
    dict_vals : dict[str, OSTerm]
        Mapping from field name to value
    type : OSType
        Type of the term, derived to be struct <struct_name>.

    """
    def __init__(self, struct_name: str, vals: Iterable[tuple[str, OSTerm]]):
        self.struct_name = struct_name
        self.vals = tuple(vals)
        self.dict_vals: dict[str, OSTerm] = dict()
        for field, val in self.vals:
            self.dict_vals[field] = val
        self.type = os_struct.OSStructType(struct_name)
        self.assert_init_type()

    def priority(self):
        return 100
    
    def __eq__(self, other):
        return isinstance(other, OSStructVal) and self.struct_name == other.struct_name and \
            self.vals == other.vals

    def print_incr(self, res: list[str], indent: int):
        res.append(self.struct_name)
        res.append("{{")
        for i, (k, v) in enumerate(self.vals):
            if i > 0:
                res.append(", ")
            res.append(f"{k}: ")
            v.print_incr(res, indent)
        res.append("}}")

    def __repr__(self):
        return "OSStructVal(%s, %s)" % (self.struct_name, self.vals)

    def __hash__(self):
        return hash(("OSStructVal", self.struct_name, self.vals))

    def subst(self, inst: dict[str, OSTerm]) -> OSTerm:
        return OSStructVal(self.struct_name, [(field, val.subst(inst)) for field, val in self.vals])

    def subst_type(self, tyinst: dict[str, OSType]) -> OSTerm:
        return OSStructVal(self.struct_name, [(field, val.subst_type(tyinst)) for field, val in self.vals])

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self
        for _, val in self.vals:
            val.assert_type_checked()

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        for _, val in self.vals:
            val.traverse(var_ctxt, visitor)
        visitor.visit(var_ctxt, self)

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> OSTerm:
        vals = [(field, val.transform(var_ctxt, transformer))
                for field, val in self.vals]
        return transformer.visit(var_ctxt, OSStructVal(self.struct_name, vals))
        
    def get_vars_inplace(self, ty_vars: list[str], vars: list[OSVar]):
        if self.type:
            self.type.get_vars_inplace(ty_vars)
        for _, val in self.vals:
            val.get_vars_inplace(ty_vars, vars)

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        for _, val in self.vals:
            val.get_funcs_inplace(funcs)

class SeqLiteral(OSTerm):
    """Literal sequence values."""
    def __init__(self, exprs: Iterable[OSTerm], *, type: Optional[OSType] = None):
        self.exprs = tuple(exprs)
        if type is not None:
            self.type = type
        elif len(self.exprs) > 0:
            self.type = None
            for expr in self.exprs:
                if expr.type is not None:
                    self.type = os_struct.SeqType(expr.type)            
        else:
            self.type = None

    def priority(self):
        return 100
    
    def __eq__(self, other):
        return isinstance(other, SeqLiteral) and self.exprs == other.exprs

    def print_incr(self, res: list[str], indent: int):
        res.append("[")
        for i, expr in enumerate(self.exprs):
            if i > 0:
                res.append(", ")
            expr.print_incr(res, indent)
        res.append("]")
    
    def __repr__(self):
        return "SeqLiteral(%s)" % ", ".join(repr(expr) for expr in self.exprs)

    def __hash__(self):
        return hash(("SeqLiteral", self.exprs))
    
    def subst(self, inst: dict[str, OSTerm]) -> OSTerm:
        return SeqLiteral([expr.subst(inst) for expr in self.exprs], type=self.type)
    
    def subst_type(self, tyinst: dict[str, OSType]) -> OSTerm:
        return SeqLiteral([expr.subst_type(tyinst) for expr in self.exprs],
                          type=self.type.subst(tyinst))

    def assert_type_checked(self):
        for expr in self.exprs:
            expr.assert_type_checked()
        assert self.type is not None, "assert_type_checked: failed on %s" % self

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        for expr in self.exprs:
            expr.traverse(var_ctxt, visitor)
        visitor.visit(var_ctxt, self)

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> OSTerm:
        exprs = [expr.transform(var_ctxt, transformer) for expr in self.exprs]
        return transformer.visit(var_ctxt, SeqLiteral(exprs, type=self.type))

    def get_vars_inplace(self, ty_vars: list[str], vars: list[OSVar]):
        if self.type:
            self.type.get_vars_inplace(ty_vars)
        for expr in self.exprs:
            expr.get_vars_inplace(ty_vars, vars)

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        for expr in self.exprs:
            expr.get_funcs_inplace(funcs)


class OSLet(OSTerm):
    """Let expression.
    
    A let expression has the form `let x = expr in body end`, it defines
    a bound variable `x` that can be used in `body`.

    Attributes
    ----------
    var_name : str
        name of the introduced variable.
    expr : OSTerm
        expression the introduced variable should equal to.
    body : OSTerm
        body of the let expression.
    type : OSType
        type of the let term, automatically derived to be type of body.

    """
    def __init__(self, var_name: str, expr: OSTerm, body: OSTerm):
        self.var_name = var_name
        self.expr = expr
        self.body = body
        self.type = self.body.type
        self.assert_init_type()

    def priority(self):
        return 10

    def __eq__(self, other):
        # Note we do not compare according to alpha-equivalence
        return isinstance(other, OSLet) and self.var_name == other.var_name and \
            self.expr == other.expr and self.body == other.body

    def print_incr(self, res: list[str], indent: int):
        res.append(f"let {self.var_name} = ")
        self.expr.print_incr(res, indent)
        res.append(" in\n" + ' ' * (indent + 2))
        self.body.print_incr(res, indent + 2)
        res.append("\n" + ' ' * indent + "end")

    def __repr__(self):
        return "OSLet(%s, %s, %s)" % (self.var_name, repr(self.expr), repr(self.body))

    def __hash__(self):
        return hash(("OSLet", self.var_name, self.expr, self.body))

    def subst(self, inst: dict[str, OSTerm]) -> OSTerm:
        # Make a new copy as inst is modified
        inst2 = dict(inst)

        # Bound variables are never substituted
        if self.var_name in inst2:
            del inst2[self.var_name]

        # Moreover, if any of the substituted values contain variables
        # that conflict with the bound variables, rename the bound variables
        ty_vars: list[str] = list()
        vars: list[OSVar] = list()
        for _, t in inst2.items():
            t.get_vars_inplace(ty_vars, vars)
        vars: set[OSVar] = set([var.name for var in vars])
        new_params = list()
        body_inst = dict()
        new_name = variant_names(vars, self.var_name)
        new_var = OSVar(new_name, type=self.expr.type)
        new_params.append(new_var)
        vars.add(new_name)
        if new_name != self.var_name:
            body_inst[self.var_name] = new_var
        return OSLet(new_name, self.expr.subst(inst2), self.body.subst(body_inst).subst(inst2))
    
    def subst_type(self, tyinst: dict[str, OSType]) -> OSType:
        return OSLet(self.var_name, self.expr.subst_type(tyinst), self.body.subst(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self
        self.expr.assert_type_checked()
        self.body.assert_type_checked()

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        # First traverse expr
        self.expr.traverse(var_ctxt, visitor)

        # Create fresh name for the bound variable, and traverse the substituted
        # version of body.
        new_var = var_ctxt.variant_var(OSVar(self.var_name, type=self.expr.type))
        body_inst = {self.var_name: new_var}
        var_ctxt.add_var_decl(new_var.name, new_var.type)
        self.body.subst(body_inst).traverse(var_ctxt, visitor)
        var_ctxt.del_var_decl(new_var.name)

        # Traverse self
        visitor.visit(var_ctxt, self)

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> OSTerm:
        # First transform expr
        expr = self.expr.transform(var_ctxt, transformer)

        # Transform body in new context
        new_var = var_ctxt.variant_var(OSVar(self.var_name, type=self.expr.type))
        body_inst = {self.var_name: new_var}
        var_ctxt.add_var_decl(new_var.name, new_var.type)
        body = self.body.subst(body_inst).transform(var_ctxt, transformer)
        var_ctxt.del_var_decl(new_var.name)

        # Transform self
        return transformer.visit(var_ctxt, OSLet(new_var.name, expr, body))

    def get_vars_inplace(self, ty_vars: list[str], vars: list[OSVar]):
        self.expr.get_vars_inplace(ty_vars, vars)
        self.body.type.get_vars_inplace(ty_vars)

        # Obtain the list of variables in the body, then subtract bound variable.
        body_ty_vars, body_vars = self.body.get_vars()
        for body_ty_var in body_ty_vars:
            if body_ty_var not in ty_vars:
                ty_vars.append(body_ty_var)
        for body_var in body_vars:
            if body_var.name != self.var_name and body_var not in vars:
                vars.append(body_var)

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        self.expr.get_funcs_inplace(funcs)
        self.body.get_funcs_inplace(funcs)

class OSSwitchBranch:
    """Base class for switch branches."""

    # Body of the switch branch
    expr : OSTerm

    def print_incr(self, res: list[str], indent: int):
        raise NotImplementedError

    def subst(self, inst: dict[str, OSTerm]) -> "OSSwitchBranch":
        raise NotImplementedError
    
    def subst_type(self, tyinst: dict[str, OSType]) -> "OSSwitchBranch":
        raise NotImplementedError

    def assert_type_checked(self):
        raise NotImplementedError

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        raise NotImplementedError
    
    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> "OSSwitchBranch":
        raise NotImplementedError

    def get_vars_inplace(self, ty_vars: list[str], vars: list[OSVar]):
        raise NotImplementedError
    
    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        raise NotImplementedError
    

class OSSwitchBranchCase(OSSwitchBranch):
    """Case branch.
    
    This corresponds to a case branch of the form
        case pat: t
    for matching on a pattern. The arguments args...
    are bound parameters of the constructor that can appear in t.

    Attributes
    ----------
    pattern : OSTerm
        pattern to be matched in the case
    expr : OSTerm
        output of the case

    """
    def __init__(self, pattern: OSTerm, expr: OSTerm):
        self.pattern = pattern
        self.expr = expr

    def print_incr(self, res: list[str], indent: int):
        res.append("case ")
        self.pattern.print_incr(res, indent)
        res.append("\n" + ' ' * (indent + 2))
        self.expr.print_incr(res, indent + 2)
    
    def __repr__(self):
        return "OSSwitchBranchCase(%s, %s)" % (repr(self.pattern), repr(self.expr))
        
    def __eq__(self, other):
        return isinstance(other, OSSwitchBranchCase) and self.pattern == other.pattern and \
            self.expr == other.expr
    
    def __hash__(self):
        return hash(("OSSwitchBranchCase", self.pattern, self.expr))

    def subst(self, inst: dict[str, OSTerm]) -> OSSwitchBranch:
        # Make a new copy as inst is modified
        inst2 = dict(inst)

        # Bound variables are never substituted
        _, bound_vars = self.pattern.get_vars()
        for var in bound_vars:
            if var.name in inst2:
                del inst2[var.name]
        
        # Moreover, if any of the substituted values contain variables
        # that conflict with the bound variables, rename the bound variables
        ty_vars: list[str] = list()
        vars: list[OSVar] = list()
        for _, t in inst2.items():
            t.get_vars_inplace(ty_vars, vars)
        vars: set[OSVar] = set([var.name for var in vars])
        new_params = list()
        body_inst = dict()
        for param in bound_vars:
            new_name = variant_names(vars, param.name)
            new_var = OSVar(new_name, type=param.type)
            new_params.append(new_var)
            vars.add(new_name)
            if new_name != param.name:
                body_inst[param.name] = new_var
        return OSSwitchBranchCase(self.pattern.subst(body_inst),
                                  self.expr.subst(body_inst).subst(inst2))

    def subst_type(self, tyinst: dict[str, OSType]) -> OSSwitchBranch:
        return OSSwitchBranchCase(self.pattern.subst_type(tyinst), self.expr.subst_type(tyinst))

    def assert_type_checked(self):
        self.pattern.assert_type_checked()
        self.expr.assert_type_checked()

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        _, bound_vars = self.pattern.get_vars()
        vars = var_ctxt.variant_vars(bound_vars)
        body_inst = dict()
        for bound_var, var in zip(bound_vars, vars):
            var_ctxt.add_var_decl(var.name, var.type)
            body_inst[bound_var.name] = var
        self.expr.subst(body_inst).traverse(var_ctxt, visitor)
        for var in vars:
            var_ctxt.del_var_decl(var.name)

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> OSSwitchBranch:
        _, bound_vars = self.pattern.get_vars()
        vars = var_ctxt.variant_vars(bound_vars)
        body_inst = dict()
        for bound_var, var in zip(bound_vars, vars):
            var_ctxt.add_var_decl(var.name, var.type)
            body_inst[bound_var.name] = var
        expr = self.expr.subst(body_inst).transform(var_ctxt, transformer)
        for var in vars:
            var_ctxt.del_var_decl(var.name)
        return OSSwitchBranchCase(self.pattern.subst(body_inst), expr)

    def get_vars_inplace(self, ty_vars: list[str], vars: list[OSVar]):
        _, bound_vars = self.pattern.get_vars()
        expr_ty_vars, expr_vars = self.expr.get_vars()
        for expr_ty_var in expr_ty_vars:
            if expr_ty_var not in ty_vars:
                ty_vars.append(expr_ty_var)
        for expr_var in expr_vars:
            if expr_var not in bound_vars and expr_var not in vars:
                vars.append(expr_var)

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        # We do not consider datatype constructors in the pattern to be
        # function calls.
        self.expr.get_funcs_inplace(funcs)


class OSSwitchBranchDefault(OSSwitchBranch):
    """Default branch.
    
    This corresponds to the default case, of the form
        default: t
    for matching on constructors that have not appeared before.

    Attributes
    ----------
    expr : OSTerm
        output of the case

    """
    def __init__(self, expr: OSTerm):
        self.expr = expr

    def print_incr(self, res: list[str], indent: int):
        res.append("default: ")
        self.expr.print_incr(res, indent)
    
    def __repr__(self):
        return "OSSwitchBranchDefault(%s)" % repr(self.expr)

    def __eq__(self, other):
        return isinstance(other, OSSwitchBranchDefault) and self.expr == other.expr
    
    def __hash__(self):
        return hash(("OSSwitchBranchDefault", self.expr))

    def subst(self, inst: dict[str, OSTerm]) -> OSSwitchBranch:
        return OSSwitchBranchDefault(self.expr.subst(inst))

    def subst_type(self, tyinst: dict[str, OSType]) -> OSSwitchBranch:
        return OSSwitchBranchDefault(self.expr.subst_type(tyinst))

    def assert_type_checked(self):
        self.expr.assert_type_checked()

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        self.expr.traverse(var_ctxt, visitor)

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> OSSwitchBranch:
        expr = self.expr.transform(var_ctxt, transformer)
        return OSSwitchBranchDefault(expr)

    def get_vars_inplace(self, ty_vars: list[str], vars: list[OSVar]):
        self.expr.get_vars_inplace(ty_vars, vars)

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        self.expr.get_funcs_inplace(funcs)


class OSSwitch(OSTerm):
    """Switch term.
    
    This corresponds to a term of the form
        switch (switch_expr) {
            cases ...
        }
    for switching on the form of switch_expr. Each case may be given by
    a pattern (nesting of datatype constructors and structure literals) or
    is the default case. Type of the switch term is not automatically derived,
    and need to be provided if necessary.

    Attributes
    ----------
    switch_expr : OSTerm
        Expression to perform switching on.
    branches : tuple[OSSwitchBranch]
        List of branches.
    type : OSType
        Type of the switch term.

    """
    def __init__(self, switch_expr: OSTerm, branches: Iterable[OSSwitchBranch],
                 type: Optional[OSType] = None):
        self.switch_expr = switch_expr
        self.branches = tuple(branches)
        self.type = type
        self.assert_init_type()

    def print_incr(self, res: list[str], indent: int):
        res.append("switch (")
        self.switch_expr.print_incr(res, indent)
        res.append(") {")
        for branch in self.branches:
            res.append(';\n' + ' ' * (indent + 2))
            branch.print_incr(res, indent + 2)
        res.append("\n" + ' ' * indent + "}")
    
    def __repr__(self):
        return "Switch(%s, [%s])" % (repr(self.switch_expr), ', '.join(repr(branch) for branch in self.branches))
    
    def __eq__(self, other):
        return isinstance(other, OSSwitch) and self.switch_expr == other.switch_expr and \
            self.branches == other.branches

    def __hash__(self):
        return hash(("OSSwitch", self.switch_expr, self.branches, self.type))

    def priority(self):
        return 10

    def subst(self, inst: dict[str, OSTerm]) -> OSTerm:
        return OSSwitch(self.switch_expr.subst(inst),
                        [branch.subst(inst) for branch in self.branches],
                        self.type)

    def subst_type(self, tyinst: dict[str, OSType]) -> OSTerm:
        return OSSwitch(self.switch_expr.subst_type(tyinst),
                        [branch.subst_type(tyinst) for branch in self.branches],
                        self.type.subst(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self
        for branch in self.branches:
            branch.assert_type_checked()

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        self.switch_expr.traverse(var_ctxt, visitor)
        for branch in self.branches:
            branch.traverse(var_ctxt, visitor)
        visitor.visit(var_ctxt, self)

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> OSTerm:
        switch_expr = self.switch_expr.transform(var_ctxt, transformer)
        branches = list()
        for branch in self.branches:
            branches.append(branch.transform(var_ctxt, transformer))
        return transformer.visit(var_ctxt, OSSwitch(switch_expr, branches, type=self.type))

    def get_vars_inplace(self, ty_vars: list[str], vars: list[OSVar]):
        self.switch_expr.get_vars_inplace(ty_vars, vars)
        for branch in self.branches:
            branch.get_vars_inplace(ty_vars, vars)

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        self.switch_expr.get_funcs_inplace(funcs)
        for branch in self.branches:
            branch.get_funcs_inplace(funcs)


class OSQuant(OSTerm):
    """Quantifier expression.
    
    This represents a term of the form

        `forall/exists vars..., body`

    where `vars...` is a list of bound variables that may appear in `body`.
    `body` should be a term of type `Bool`, and the quantifier term itself
    always has type `Bool`.

    Attributes
    ----------
    quantifier : str
        type of the quantifier, supports "forall" and "exists"
    params : tuple[OSVar]
        list of bound variables, these may appear in the body
    body : OSTerm
        body of the quantifier expression
    type : OSType
        type of the expression, derived to be Bool.

    """
    def __init__(self, quantifier: str, params: Iterable[OSVar], body: OSTerm):
        self.quantifier = quantifier
        self.params: tuple[OSVar] = tuple(params)
        self.body = body
        self.type = os_struct.Bool

    def print_incr(self, res: list[str], indent: str):
        res.append(f"{self.quantifier} (")
        for i, param in enumerate(self.params):
            if i > 0:
                res.append(", ")
            param.type.print_incr(res, indent)
            res.append(f" {param.name}")
        res.append(") {\n" + ' ' * (indent + 2))
        self.body.print_incr(res, indent + 2)
        res.append("\n" + ' ' * indent + "}")

    def __eq__(self, other):
        return isinstance(other, OSQuant) and self.quantifier == other.quantifier and \
            self.params == other.params and self.body == other.body
    
    def __repr__(self):
        return "OSQuant(%s, %s, %s)" % (self.quantifier, self.params, self.body)
    
    def __hash__(self):
        return hash(("OSQuant", self.quantifier, self.params, self.body))
    
    def priority(self):
        return 100

    def subst(self, inst: dict[str, OSTerm]) -> OSTerm:
        # Make a new copy as inst is modified
        inst2 = dict(inst)

        # Bound variables are never substituted
        for param in self.params:
            if param.name in inst2:
                del inst2[param.name]

        # Moreover, if any of the substituted values contain variables
        # that conflict with the bound variables, rename the bound variables
        ty_vars: list[str] = list()
        vars: list[OSVar] = list()
        for _, t in inst2.items():
            t.get_vars_inplace(ty_vars, vars)
        vars: set[OSVar] = set([var.name for var in vars])
        new_params = list()
        body_inst = dict()
        for param in self.params:
            new_name = variant_names(vars, param.name)
            new_var = OSVar(new_name, type=param.type)
            new_params.append(new_var)
            vars.add(new_name)
            if new_name != param.name:
                body_inst[param.name] = new_var
        return OSQuant(self.quantifier, new_params, self.body.subst(body_inst).subst(inst2))
    
    def subst_type(self, tyinst: dict[str, OSType]) -> OSTerm:
        return OSQuant(self.quantifier, [param.subst_type(tyinst) for param in self.params],
                       self.body.subst_type(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self
        for param in self.params:
            param.assert_type_checked()
        self.body.assert_type_checked()

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        new_vars = var_ctxt.variant_vars(self.params)
        body_inst = dict()
        for bound_var, new_var in zip(self.params, new_vars):
            var_ctxt.add_var_decl(new_var.name, new_var.type)
            body_inst[bound_var.name] = new_var
        self.body.subst(body_inst).traverse(var_ctxt, visitor)
        for new_var in new_vars:
            var_ctxt.del_var_decl(new_var.name)
        visitor.visit(var_ctxt, self)

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> OSTerm:
        new_vars = var_ctxt.variant_vars(self.params)
        body_inst = dict()
        for bound_var, new_var in zip(self.params, new_vars):
            var_ctxt.add_var_decl(new_var.name, new_var.type)
            body_inst[bound_var.name] = new_var
        body = self.body.subst(body_inst).transform(var_ctxt, transformer)
        for new_var in new_vars:
            var_ctxt.del_var_decl(new_var.name)
        return transformer.visit(var_ctxt, OSQuant(self.quantifier, new_vars, body))

    def get_vars_inplace(self, ty_vars: list[str], vars: list[OSVar]):
        # Obtain the list of variables in the body, then subtract bound variable.
        body_ty_vars, body_vars = self.body.get_vars()
        for body_ty_var in body_ty_vars:
            if body_ty_var not in ty_vars:
                ty_vars.append(body_ty_var)
        for body_var in body_vars:
            if body_var not in self.params and body_var not in vars:
                vars.append(body_var)

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        self.body.get_funcs_inplace(funcs)


class OSQuantIn(OSTerm):
    """Quantifier expression, ranging over maps or lists.
    
    Attributes
    ----------
    quantifier : str
        type of the quantifier, supports "forall" and "exists"
    param : OSVar
        bound variable
    collection : OSTerm
        range of the bound variable
    body : OSTerm
        body of the quantifier expression
    type : OSType
        type of the expression, derived to be Bool.

    """
    def __init__(self, quantifier: str, param: OSVar, collection: OSTerm, body: OSTerm):
        self.quantifier = quantifier
        self.param = param
        self.collection = collection
        self.body = body
        self.type = os_struct.Bool

    def print_incr(self, res: list[str], indent: int):
        res.append(f"{self.quantifier} (")
        self.param.type.print_incr(res, indent)
        res.append(f" {self.param.name} in ")
        self.collection.print_incr(res, indent)
        res.append(") {\n" + ' ' * (indent + 2))
        self.body.print_incr(res, indent + 2)
        res.append("\n" + ' ' * indent + "}")
    
    def __eq__(self, other):
        return isinstance(other, OSQuantIn) and self.quantifier == other.quantifier and \
            self.param == other.param and self.collection == other.collection and \
            self.body == other.body
    
    def __repr__(self):
        return "OSQuantIn(%s, %s, %s, %s)" % (
            self.quantifier, self.param, repr(self.collection), repr(self.body))

    def __hash__(self):
        return hash(("OSQuantIn", self.quantifier, self.param, self.collection, self.body))

    def priority(self):
        return 100

    def subst(self, inst: dict[str, OSTerm]) -> OSTerm:
        # Make a new copy as inst is modified
        inst2 = dict(inst)

        # Bound variables are never substituted
        if self.param.name in inst2:
            del inst2[self.param.name]

        # Moreover, if any of the substituted values contain variables
        # that conflict with the bound variables, rename the bound variables
        ty_vars: list[str] = list()
        vars: list[OSVar] = list()
        for _, t in inst2.items():
            t.get_vars_inplace(ty_vars, vars)
        vars: set[OSVar] = set([var.name for var in vars])
        body_inst = dict()

        new_name = variant_names(vars, self.param.name)
        new_var = OSVar(new_name, type=self.param.type)
        vars.add(new_name)
        if new_name != self.param.name:
            body_inst[self.param.name] = new_var
        return OSQuantIn(self.quantifier, new_var, self.collection.subst(inst2),
                         self.body.subst(body_inst).subst(inst2))
    
    def subst_type(self, tyinst: dict[str, OSType]) -> OSTerm:
        return OSQuantIn(self.quantifier, self.param.subst_type(tyinst),
                         self.collection.subst_type(tyinst),
                         self.body.subst_type(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self
        self.param.assert_type_checked()
        self.collection.assert_type_checked()
        self.body.assert_type_checked()

    def traverse(self, var_ctxt: VarContext, visitor: Visitor):
        # Visit collection
        self.collection.traverse(var_ctxt, visitor)

        # Visit body with bound variable added
        new_var = var_ctxt.variant_var(self.param)
        body_inst = {self.param.name: new_var}
        var_ctxt.add_var_decl(new_var.name, new_var.type)
        self.body.subst(body_inst).traverse(var_ctxt, visitor)
        var_ctxt.del_var_decl(new_var.name)

        # Visit self
        visitor.visit(var_ctxt, self)

    def transform(self, var_ctxt: VarContext, transformer: Transformer) -> OSTerm:
        # Transform collection
        collection = self.collection.transform(var_ctxt, transformer)

        # Transform body with bound variable added
        new_var = var_ctxt.variant_var(self.param)
        body_inst = {self.param.name: new_var}
        var_ctxt.add_var_decl(new_var.name, new_var.type)
        body = self.body.subst(body_inst).transform(var_ctxt, transformer)
        var_ctxt.del_var_decl(new_var.name)

        # Transform self
        return transformer.visit(var_ctxt, OSQuantIn(self.quantifier, new_var, collection, body))

    def get_vars_inplace(self, ty_vars: list[str], vars: list[OSVar]):
        # Obtain the list of variables in the body, then subtract bound variable.
        body_ty_vars, body_vars = self.body.get_vars()
        for body_ty_var in body_ty_vars:
            if body_ty_var not in ty_vars:
                ty_vars.append(body_ty_var)
        for body_var in body_vars:
            if body_var != self.param and body_var not in vars:
                vars.append(body_var)
        body_ty_vars, body_vars = self.collection.get_vars()
        for body_ty_var in body_ty_vars:
            if body_ty_var not in ty_vars:
                ty_vars.append(body_ty_var)
        for body_var in body_vars:
            if body_var != self.param and body_var not in vars:
                vars.append(body_var)

    def get_funcs_inplace(self, funcs: list[tuple[str, OSType]]):
        self.collection.get_funcs_inplace(funcs)
        self.body.get_funcs_inplace(funcs)
    
    def get_constraint(self) -> OSTerm:
        """Obtain the constraint on the bound variable."""
        ty = self.collection.type
        if os_struct.is_map_type(ty):
            return indom(self.param, self.collection)
        elif os_struct.is_seq_type(ty):
            if is_fun(self.collection, "range") or is_fun(self.collection, "range8"):
                return conj(greater_eq(self.param, self.collection.args[0]),
                            less(self.param, self.collection.args[1]))
            else:
                raise NotImplementedError
        else:
            raise NotImplementedError("get_constraint: unknown collection type %s" % ty)


def is_plus(t: OSTerm) -> TypeGuard[OSOp]:
    return isinstance(t, OSOp) and t.op == "+"

def is_minus(t: OSTerm) -> TypeGuard[OSOp]:
    return isinstance(t, OSOp) and t.op == "-" and len(t.args) == 2

def is_uminus(t: OSTerm) -> TypeGuard[OSOp]:
    return isinstance(t, OSOp) and t.op == "-" and len(t.args) == 1

def get_uminus(t: OSTerm) -> OSTerm:
    """Obtain unary minus of arithmetic term.
    
    This function performs additional checks to simplify the result.

    """
    if isinstance(t, OSNumber):
        return OSNumber(-t.val, type=t.type)
    elif is_uminus(t):
        return t.args[0]
    else:
        return -t

def get_plus(t1: OSTerm, t2: OSTerm) -> OSTerm:
    """Obtain plus of arithmetic terms.
    
    This function performs additional checks to simplify the result.

    """
    if isinstance(t1, OSNumber) and t1.val == 0:
        return t2
    elif isinstance(t2, OSNumber) and t2.val == 0:
        return t1
    elif is_uminus(t1):
        return get_minus(t2, t1.args[0])
    elif is_uminus(t2):
        return get_minus(t1, t2.args[0])
    elif isinstance(t1, OSOp) and t1.op == "-" and t1.rhs == t2:
        return t1.lhs
    else:
        return t1 + t2

def get_minus(t1: OSTerm, t2: OSTerm) -> OSTerm:
    """Obtain minus of arithmetic terms.
    
    This function performs additional checks to simpify the result.

    """
    if isinstance(t1, OSNumber) and t1.val == 0:
        return get_uminus(t2)
    elif isinstance(t2, OSNumber) and t2.val == 0:
        return t1
    elif is_uminus(t2):
        return t1 + t2.args[0]
    elif isinstance(t1, OSOp) and t1.op == "+" and t1.rhs == t2:
        return t1.lhs
    else:
        return t1 - t2

true = OSNumber(True)
false = OSNumber(False)
int_zero = OSNumber(0, os_struct.Int)
int_one = OSNumber(1, os_struct.Int)

neg_map = {
    "<": ">=",
    ">": "<=",
    ">=": "<",
    "<=": ">",
    "==": "!=",
    "!=": "==" 
}

def get_negation(t: OSTerm) -> OSTerm:
    """Return the logical negation of a term, suitably simplified.
    
    Simplifications include:
    - remove double negations
    - negation of operators <, >, <=, >=, ==, and !=

    """
    if t.type != os_struct.Bool:
        raise AssertionError("get_negation: input term %s is not boolean" % t)

    if isinstance(t, OSOp):
        if t.op == "!":
            return t.args[0]
        elif t.op in neg_map:
            return OSOp(neg_map[t.op], *t.args, type=os_struct.Bool)
        else:
            return OSOp("!", t, type=os_struct.Bool)
    else:
        return OSOp("!", t, type=os_struct.Bool)

def is_pair(t: OSTerm) -> TypeGuard[OSFun]:
    """Check whether a term is a pair."""
    return isinstance(t, OSFun) and t.func_name == "pair"

def list_pair(*ts: OSTerm) -> OSTerm:
    """Construct the tuple consisting of terms ts."""
    if len(ts) == 0:
        raise AssertionError("list_pair")
    if len(ts) == 1:
        return ts[0]
    t2 = list_pair(*ts[1:])
    return OSFun("pair", ts[0], t2, type=os_struct.OSHLevelType("Prod", ts[0].type, t2.type))

"""
Utility functions for Maps
"""
def empty_map(K: OSType, V: OSType) -> OSTerm:
    """Construct empty map."""
    return OSFun("emptyMap", type=os_struct.MapType(K, V))

def is_empty_map(t: OSTerm) -> TypeGuard[OSFun]:
    return isinstance(t, OSFun) and t.func_name == "emptyMap"

def is_update_map(t: OSTerm) -> TypeGuard[OSFun]:
    return isinstance(t, OSFun) and t.func_name == "updateMap"

def dest_map_get(t: OSTerm) -> tuple[OSTerm, OSTerm]:
    """Deconstruct `get(k, m)` into pair `(k, m)`."""
    if not is_fun(t, "get"):
        raise AssertionError("dest_map_get")
    return t.args

def dest_map_indom(t: OSTerm) -> tuple[OSTerm, OSTerm]:
    """Deconstruct `indom(k, m)` into pair `(k, m)`."""
    if not is_fun(t, "indom"):
        raise AssertionError("dest_map_indom")
    return t.args

def indom(k: OSTerm, map: OSTerm) -> OSTerm:
    return OSFun("indom", k, map, type=os_struct.Bool)

"""
Utility functions for integers
"""
def int32u(n: int) -> OSTerm:
    """Return constant value with type `int32u."""
    return OSNumber(n, type=os_struct.Int32U)

def integer(n: int) -> OSTerm:
    """Return constant value with type `int`."""
    return OSNumber(n, type=os_struct.Int)

def convert_int(t: OSTerm) -> OSTerm:
    """Convert expression of bitvector type to integer type."""
    if not os_struct.is_bv_type(t.type):
        raise AssertionError("convert_int: expect bitvector type for t, found %s" % t.type)
    if isinstance(t, OSNumber):
        return OSNumber(t.val, type=os_struct.Int)
    else:
        return OSFun("int", t, type=os_struct.Int)

def convert_bitvector(t: OSTerm, ty: OSType) -> OSTerm:
    """Convert expression of integer type to given bitvector type."""
    if not os_struct.is_bv_type(ty):
        raise AssertionError("convert_bitvector: %s is not bitvector type" % ty)
    if t.type != os_struct.Int:
        raise AssertionError("convert_bitvector: %s is not an integer" % t)
    if isinstance(t, OSNumber):
        return OSNumber(t.val, type=ty)
    elif is_fun(t, "int") and ty == t.args[0].type:
        return t.args[0]
    else:
        return OSFun(ty.name, t, type=ty)

"""
Equality and inequalities
"""
def eq(t1: OSTerm, t2: OSTerm) -> OSTerm:
    """Construct the term t1 == t2."""
    return OSOp("==", t1, t2, type=os_struct.Bool)

def diseq(t1: OSTerm, t2: OSTerm) -> OSTerm:
    """Construct the term t1 != t2."""
    return OSOp("!=", t1, t2, type=os_struct.Bool)

def is_eq(t: OSTerm) -> TypeGuard[OSOp]:
    """Check whether term has form t1 == t2."""
    return isinstance(t, OSOp) and t.op == "=="

def is_diseq(t: OSTerm) -> TypeGuard[OSOp]:
    """Check whether term has form t1 != t2."""
    return isinstance(t, OSOp) and t.op == "!="

def is_greater_eq(t: OSTerm) -> TypeGuard[OSOp]:
    """Check whether term has form t1 >= t2."""
    return isinstance(t, OSOp) and t.op == ">="

def greater_eq(t1: OSTerm, t2: OSTerm) -> OSTerm:
    """Construct the term t1 >= t2."""
    return OSOp(">=", t1, t2, type=os_struct.Bool)

def is_less_eq(t: OSTerm) -> TypeGuard[OSOp]:
    """Check whether term has form t1 <= t2"""
    return isinstance(t, OSOp) and t.op == "<="

def less_eq(t1: OSTerm, t2: OSTerm) -> OSTerm:
    """Construct the term t1 <= t2."""
    return OSOp("<=", t1, t2, type=os_struct.Bool)

def is_greater(t: OSTerm) -> TypeGuard[OSOp]:
    """Check whether term has form t1 > t2."""
    return isinstance(t, OSOp) and t.op == ">"

def greater(t1: OSTerm, t2: OSTerm) -> OSTerm:
    """Construct the term t1 > t2."""
    return OSOp(">", t1, t2, type=os_struct.Bool)

def is_less(t: OSTerm) -> TypeGuard[OSOp]:
    """Check whether term has form t1 < t2."""
    return isinstance(t, OSOp) and t.op == "<"

def less(t1: OSTerm, t2: OSTerm) -> OSTerm:
    """Construct the term t1 < t2."""
    return OSOp("<", t1, t2, type=os_struct.Bool)

def lhs(t: OSTerm) -> OSTerm:
    """Return left side of (in)equality or arithmetic operation."""
    if not isinstance(t, OSOp) and t.op in ("==", "!=", "<", ">", "<=", ">=", "+", "-", "*"):
        raise AssertionError("lhs: input is not an (dis)equality")
    return t.args[0]

def rhs(t: OSTerm) -> OSTerm:
    """Return right side of (in)equality or arithmetic operation."""
    if not isinstance(t, OSOp) and t.op in ("==", "!=", "<", ">", "<=", ">=", "+", "-", "*"):
        raise AssertionError("rhs: input is not an (dis)equality")
    return t.args[1]

"""
Logical operators
"""
def is_conj(t: OSTerm) -> TypeGuard[OSOp]:
    return isinstance(t, OSOp) and t.op == "&&"

def conj(t1: OSTerm, t2: OSTerm) -> OSTerm:
    return OSOp("&&", t1, t2, type=os_struct.Bool)

def split_conj(t: OSTerm) -> tuple[OSTerm]:
    """Deconstruct a conjunction of a list of terms."""
    res = []
    def rec(t):
        if isinstance(t, OSOp) and t.op == "&&":
            rec(t.args[0])
            rec(t.args[1])
        else:
            res.append(t)
    rec(t)
    return tuple(res)

def list_conj(ts: Iterable[OSTerm]) -> OSTerm:
    """Create a conjunction of a list of terms."""
    ts = tuple(ts)
    if not ts:
        return true  # conjunction of empty list is true
    res = ts[-1]
    for t in reversed(ts[:-1]):
        res = OSOp("&&", t, res, type=os_struct.Bool)
    return res

def is_disj(t: OSTerm) -> TypeGuard[OSOp]:
    return isinstance(t, OSOp) and t.op == "||"

def disj(t1: OSTerm, t2: OSTerm) -> OSTerm:
    return OSOp("||", t1, t2, type=os_struct.Bool)

def split_disj(t: OSTerm) -> tuple[OSTerm]:
    """Deconstruct a disjunction of a list of terms."""
    res = []
    def rec(t):
        if isinstance(t, OSOp) and t.op == "||":
            rec(t.args[0])
            rec(t.args[1])
        else:
            res.append(t)
    rec(t)
    return tuple(res)

def list_disj(ts: Iterable[OSTerm]) -> OSTerm:
    """Create a disjunction of a list of terms."""
    ts = tuple(ts)
    if not ts:
        return false  # disjunction of empty list is false
    res = ts[-1]
    for t in reversed(ts[:-1]):
        res = OSOp("||", t, res, type=os_struct.Bool)
    return res

def is_implies(t: OSTerm) -> TypeGuard[OSOp]:
    return isinstance(t, OSOp) and t.op == "->"

def strip_implies(t: OSTerm) -> tuple[tuple[OSTerm], OSTerm]:
    """Destruct implies expression.

    Given input term of the form

        `A1 -> A2 -> ... -> An -> C`

    returns the pair `(A1, ..., An)` and `C`.
    
    """
    assumes = list()
    while isinstance(t, OSOp) and t.op == "->":
        assumes.append(t.args[0])
        t = t.args[1]
    return tuple(assumes), t

def implies(assume: OSTerm, concl: OSTerm) -> OSTerm:
    return OSOp("->", assume, concl, type=os_struct.Bool)

def list_implies(assumes: Iterable[OSTerm], concl: OSTerm) -> OSTerm:
    """Construct implies expression from assumptions and conclusion.
    
    Given list of terms `[A1, A2, ..., An]` and term `C`,
    form the term
    
        `A1 -> A2 -> ... -> An -> C`.

    """
    res = concl
    for assume in reversed(assumes):
        res = OSOp("->", assume, res, type=os_struct.Bool)
    return res

def strip_implies_gen(t: OSTerm) -> list[tuple[tuple[OSTerm], OSTerm]]:
    """More general form of strip_implies.
    
    Each pair (As, C) in the returned list corresponds to
    an implication A1 -> A2 -> ... -> An -> C contained in
    the input.

    """
    if is_implies(t):
        t1, t2 = t.args
        t2_res = strip_implies_gen(t2)
        return [((t1,) + As, C) for As, C in t2_res]
    elif is_conj(t):
        t1, t2 = t.args
        t1_res = strip_implies_gen(t1)
        t2_res = strip_implies_gen(t2)
        return t1_res + t2_res
    elif is_ite(t):
        cond, t1, t2 = t.args
        t1_res = strip_implies_gen(implies(cond, t1))
        t2_res = strip_implies_gen(implies(get_negation(cond), t2))
        return t1_res + t2_res
    else:
        return [(tuple(), t)]

def list_implies_gen(imps: Iterable[tuple[tuple[OSTerm], OSTerm]]) -> OSTerm:
    """Form conjunction of implications from result of `strip_implies_gen`."""
    return list_conj(list_implies(As, C) for As, C in imps)

def strip_exists(var_ctxt: VarContext, t: OSTerm, *,
                 var_names: Iterable[str] = tuple()) -> tuple[tuple[OSVar], OSTerm, VarContext]:
    """Destruct existential quantifier.
    
    Given input term of the form

        `exists t1 ... tn. P`

    return the pair `(t1, ..., tn)` and `P`

    """
    if isinstance(t, OSQuant) and t.quantifier == "exists":
        vars = t.params
        if var_names:
            if len(var_names) < len(t.params):
                raise OSTermException("strip_exists: number of variable names does not match.")
            if not var_ctxt.is_fresh_names(var_names):
                raise OSTermException(f"strip_exists: names {var_names} are not fresh.")

            new_vars = list()
            for name, var in zip(var_names, vars):
                new_vars.append(OSVar(name, type=var.type))
            rest_var_names = var_names[len(t.params):]
        else:
            new_vars = var_ctxt.variant_vars(vars)
            rest_var_names = tuple()

        body_inst = dict()
        for var, new_var in zip(vars, new_vars):
            var_ctxt.add_var_decl(new_var.name, new_var.type)
            body_inst[var.name] = new_var
        body = t.body.subst(body_inst)
        body_vars, body_t, var_ctxt2 = strip_exists(var_ctxt, body, var_names=rest_var_names)
        for new_var in new_vars:
            var_ctxt.del_var_decl(new_var.name)
        return tuple(new_vars + list(body_vars)), body_t, var_ctxt2
    else:
        if len(var_names) > 0:
            raise OSTermException("strip_exists: more variables than needed")
        return tuple(), t, var_ctxt.clone()

def is_exists(t: OSTerm) -> bool:
    """Check whether term is in exists or exists-in form."""
    if isinstance(t, OSQuant) and t.quantifier == "exists":
        return True
    if isinstance(t, OSQuantIn) and t.quantifier == "exists":
        return True
    return False

def is_forall(t: OSTerm) -> bool:
    """Check whether term is in forall or forall-in form."""
    if isinstance(t, OSQuant) and t.quantifier == "forall":
        return True
    if isinstance(t, OSQuantIn) and t.quantifier == "forall":
        return True
    return False

def strip_forall(var_ctxt: VarContext, t: OSTerm, *,
                 var_names: Iterable[str] = tuple()) -> tuple[tuple[OSVar], OSTerm, VarContext]:
    """Destruct universal quantifier.
    
    Given input term of the form `forall t1 ... tn. P`, return a list
    of fresh variables `(t1, ..., tn)`, body `P` and new variable context.

    """
    if isinstance(t, OSQuant) and t.quantifier == "forall":
        vars = t.params
        if var_names:
            if len(var_names) < len(t.params):
                raise OSTermException("strip_forall: number of variable names does not match.")
            if not var_ctxt.is_fresh_names(var_names):
                raise OSTermException(f"strip_forall: names {var_names} are not fresh.")

            new_vars = list()
            for name, var in zip(var_names, vars):
                new_vars.append(OSVar(name, type=var.type))
            rest_var_names = var_names[len(t.params):]
        else:
            new_vars = var_ctxt.variant_vars(vars)
            rest_var_names = tuple()

        body_inst = dict()
        for var, new_var in zip(vars, new_vars):
            var_ctxt.add_var_decl(new_var.name, new_var.type)
            body_inst[var.name] = new_var
        body = t.body.subst(body_inst)
        body_vars, body_t, var_ctxt2 = strip_forall(var_ctxt, body, var_names=rest_var_names)
        for new_var in new_vars:
            var_ctxt.del_var_decl(new_var.name)
        return tuple(new_vars + list(body_vars)), body_t, var_ctxt2
    else:
        if len(var_names) > 0:
            raise OSTermException("strip_forall: more variables than needed")
        return tuple(), t, var_ctxt.clone()

def strip_forall1(var_ctxt: VarContext, t: OSTerm) -> tuple[OSVar, OSTerm, VarContext]:
    """Destruct universal quantifier exactly once.
    
    Given input term of the form `forall t. P`, return fresh variable `t`,
    body `P` and new variable context.

    """
    if isinstance(t, OSQuant) and t.quantifier == "forall":
        var = t.params[0]
        new_var = var_ctxt.variant_var(var)

        body_inst = dict()
        var_ctxt.add_var_decl(new_var.name, new_var.type)
        body_inst[var.name] = new_var
        body = t.body.subst(body_inst)
        if len(t.params) > 1:
            body = OSQuant("forall", t.params[1:], body)
        var_ctxt2 = var_ctxt.clone()
        var_ctxt.del_var_decl(new_var.name)
        return new_var, body, var_ctxt2
    else:
        raise OSTermException(f"strip_forall1: {t} is not forall term")

def is_fun(t: OSTerm, func_name: str) -> TypeGuard[OSFun]:
    """Return whether t is a function application with given name."""
    return isinstance(t, OSFun) and t.func_name == func_name

def ite(cond: OSTerm, t1: OSTerm, t2: OSTerm) -> OSTerm:
    """Form the term `if (cond) { t1 } else { t2 }`"""
    if cond.type != os_struct.Bool:
        raise AssertionError(f"ite: type of cond is {cond.type}")
    if t1.type != t2.type:
        raise AssertionError(f"ite: inconsistent type: {t1.type} vs {t2.type}")
    return OSFun("ite", cond, t1, t2, type=t1.type)

def is_ite(t: OSTerm) -> TypeGuard[OSFun]:
    """Check whether a term has form `if (cond) { t1 } else { t2 }`"""
    return is_fun(t, "ite")

def list_ite(conds: Iterable[OSTerm], exprs: Iterable[OSTerm]) -> OSTerm:
    """Construct if-then-else expressions.
    
    Length of `exprs` either equals that of `conds`, or is one greater.
    In the former case, the last condition is ignored (assume the list
    of conditions together fill all possibilities). Then the last entry
    in `exprs` is used as the else branch.
    
    """
    assert len(exprs) == len(conds) or len(exprs) == len(conds) + 1, \
        f"list_ite: unexpected size of input {len(conds)} vs {len(exprs)}."

    if len(exprs) == len(conds):
        conds = conds[:len(conds)-1]  # drop the last condition
    
    res = exprs[-1]
    for i in reversed(range(len(conds))):
        res = ite(conds[i], exprs[i], res)
    return res

"""
Sequence functions
"""
def seq_length(xs: OSTerm) -> OSTerm:
    """Construct seq_length(xs)."""
    if not os_struct.is_seq_type(xs.type):
        raise AssertionError("seq_length: xs must have Seq type")
    return OSFun("seq_length", xs, type=os_struct.Int)

def seq_index(i: OSTerm, xs: OSTerm) -> OSTerm:
    """Construct `seq_index(i, xs)`."""
    if i.type != os_struct.Int:
        raise AssertionError("seq_index: i must have integer type")
    if not os_struct.is_seq_type(xs.type):
        raise AssertionError("seq_index: xs must have Seq type")
    return OSFun("seq_index", i, xs, type=xs.type.params[0])

def dest_index(t: OSTerm) -> tuple[OSTerm, OSTerm]:
    """Deconstruct `seq_index(i, xs)` into pair `(i, xs)`."""
    if not is_fun(t, "seq_index"):
        raise AssertionError("dest_index")
    return t.args

def seq_empty(ele_ty: OSType) -> OSTerm:
    """Construct `seq_empty<T>` of type Seq<T>."""
    return OSFun("seq_empty", type=os_struct.SeqType(ele_ty))

def seq_literal(*ts: OSTerm) -> OSTerm:
    """Construct the sequence literal."""
    return SeqLiteral(ts)

def seq_update(i: OSTerm, t: OSTerm, xs: OSTerm) -> OSTerm:
    """Construct seq_update(i, t, xs)."""
    if i.type != os_struct.Int:
        raise AssertionError("seq_update: i must have integer type")
    if not os_struct.is_seq_type(xs.type) or xs.type.params[0] != t.type:
        raise AssertionError("seq_update: xs must have type Seq<T> (where T = t.type)")
    return OSFun("seq_update", i, t, xs, type=xs.type)

def seq_repeat(t: OSTerm, i: OSTerm) -> OSTerm:
    """Construct seq_repeat(t, i)."""
    if i.type != os_struct.Int:
        raise AssertionError("seq_repeat: i must have integer type")
    return OSFun("seq_repeat", t, i, type=os_struct.SeqType(t.type))

def seq_append(xs: OSTerm, ys: OSTerm) -> OSTerm:
    """Construct seq_append(xs, ys)."""
    if not os_struct.is_seq_type(xs.type) or xs.type != ys.type:
        raise AssertionError("seq_append: xs and ys must be same Seq type")
    return OSFun("seq_append", xs, ys, type=xs.type)

def seq_slice(i: OSTerm, j: OSTerm, xs: OSTerm) -> OSTerm:
    """Construct seq_slice(i, j, xs)."""
    if not os_struct.is_seq_type(xs.type):
        raise AssertionError("seq_slice: xs must have Seq type")
    if i.type != os_struct.Int or j.type != os_struct.Int:
        raise AssertionError("seq_slilce: i and j must have integer type")
    return OSFun("seq_slice", i, j, xs, type=xs.type)

def max(i: OSTerm, j: OSTerm) -> OSTerm:
    """Construct max(i, j)."""
    if i.type != os_struct.Int or j.type != os_struct.Int:
        raise AssertionError("max: i and j must have integer type")
    return OSFun("max", i, j, type=os_struct.Int)

def min(i: OSTerm, j: OSTerm) -> OSTerm:
    """Construct min(i, j)."""
    if i.type != os_struct.Int or j.type != os_struct.Int:
        raise AssertionError("min: i and j must have integer type")
    return OSFun("min", i, j, type=os_struct.Int)

def is_id(t: OSTerm) -> TypeGuard[FieldGet]:
    """Determine whether `t` is of form `e.id`."""
    return isinstance(t, FieldGet) and t.field == "id"

def eval_op(op: str, ty: OSType, args: tuple[int | bool]) -> tuple[int | bool, OSType]:
    """Evaluate operator on given arguments.
    
    Parameters
    ----------
    op : str
        operator allowed by OSOp, such as ==, !=, +, <, !, etc.
    ty : OSType
        type of the arguments
    args : tuple[int | bool]
        list of arguments
    
    Returns
    -------
    val : int | bool
        evaluated result
    type : OSType
        type of the result
        
    """
    if len(args) == 1:
        if op == "!":
            return not args[0], ty
        elif op == "~":
            return ~args[0], ty
        elif op == "-":
            return -args[0], ty
        else:
            raise NotImplementedError(f"eval_op for {op}")
    elif len(args) == 2:
        a, b = args
        if op == '==':
            return a == b, os_struct.Bool
        elif op == '!=':
            return a != b, os_struct.Bool
        elif op == '&&':
            return a and b, ty
        elif op == '||':
            return a or b, ty
        elif op == '->':
            return not a or b, ty
        elif op == '<=':
            return a <= b, os_struct.Bool
        elif op == '<':
            return a < b, os_struct.Bool
        elif op == '>=':
            return a >= b, os_struct.Bool
        elif op == '>':
            return a > b, os_struct.Bool
        elif op == "+":
            return a + b, ty
        elif op == "-":
            return a - b, ty
        elif op == "*":
            return a * b, ty
        elif op == "/":
            return a / b, ty
        elif op == "&":
            return a & b, ty
        elif op == ">>":
            return a >> b, ty
        elif op == "<<":
            return a << b, ty
        elif op == "|":
            return a | b, ty
        elif op == "**":
            return a ** b, ty
        elif op == "%":
            return a & b, ty
        else:
            raise NotImplementedError(f"eval_op for {op}")
    else:
        raise NotImplementedError(f"eval_op on {len(args)} arguments")

def is_atomic_term(t: OSTerm) -> bool:
    """Return whether `t` is an atomic term.
    
    A term `t` is atomic if it is a variable, or it is formed from
    atomic terms by field access, sequence index/length, and
    map get/indom.

    """
    if isinstance(t, OSVar):
        return True
    elif is_fun(t, "default"):
        return True
    elif isinstance(t, FieldGet):
        return is_atomic_term(t.expr)
    elif is_fun(t, "seq_index"):
        _, a = dest_index(t)
        return is_atomic_term(a)
    elif is_fun(t, "seq_length"):
        a = t.args[0]
        return is_atomic_term(a)
    elif is_fun(t, "get"):
        _, map = t.args
        return is_atomic_term(map)
    elif is_fun(t, "indom"):
        _, map = t.args
        return is_atomic_term(map)
    else:
        return False

def dest_atomic_term(t: OSTerm) -> tuple[str, tuple[OSTerm]]:
    """Obtain name and indices for an atomic term.

    The name of an atomic term starts from the variable, and appends
    one of the following for each accessors:

    1. `.{field}` for field access.
    2. `.index` for index access of a sequence.
    3. `.get` for key access of a map.
    4. `.length` for accessing length of a sequence.
    5. `.indom` for in-domain query of a map.

    The array index or key in cases 2, 3, 5 above are collected into
    a tuple that forms the second return value of the function.
    
    Parameters
    ----------
    t: OSTerm
        atomic term, assumed to satisfy `os_term.is_atomic_term`.
        
    Returns
    -------
    str
        dotted name of path to the term.
    tuple[OSTerm]
        list of sequence and map indices.

    """
    if isinstance(t, OSVar):
        return t.name, tuple()
    elif is_fun(t, "default"):
        return "default", tuple()
    elif isinstance(t, FieldGet):
        s, idx = dest_atomic_term(t.expr)
        return s + "." + t.field, idx
    elif is_fun(t, "seq_index"):
        i, a = t.args
        s, idx = dest_atomic_term(a)
        return s + ".index", idx + (i,)
    elif is_fun(t, "get"):
        k, map = t.args
        s, idx = dest_atomic_term(map)
        return s + ".get", idx + (k,)
    elif is_fun(t, "seq_length"):
        a = t.args[0]
        s, idx = dest_atomic_term(a)
        return s + ".length", idx
    elif is_fun(t, "indom"):
        k, map = t.args
        s, idx = dest_atomic_term(map)
        return s + ".indom", idx + (k,)
    else:
        raise OSTermException(f"dest_atomic_term: {t} is not atomic")

"""Commonly used visitors."""

class CheckVarVisitor(Visitor):
    """Check whether variable terms are declared in the context.
    
    Helper for `check_vars`.
    
    """
    def __init__(self, msg: str = ""):
        self.msg = msg

    def visit(self, var_ctxt: VarContext, t: OSTerm):
        if isinstance(t, OSVar):
            if not var_ctxt.contains_var(t.name):
                raise AssertionError(f"{self.msg}: variable {t} is not found in context")

def check_vars(var_ctxt: VarContext, t: OSTerm):
    """Check all variables in a term `t` are declared. Used for debugging."""
    t.traverse(var_ctxt, CheckVarVisitor())

class FreeSubtermVisitor(Visitor):
    """Obtain the set of all free subterms."""
    def __init__(self, var_ctxt: VarContext):
        self.var_ctxt = var_ctxt.clone()
        self.collector: set[OSTerm] = set()

    def visit(self, var_ctxt: VarContext, t: OSTerm):
        if self.var_ctxt.is_free(t):
            self.collector.add(t)
    
def get_all_free_subterms(var_ctxt: VarContext, t: OSTerm) -> set[OSTerm]:
    """Return set of all free subterms of t."""
    visitor = FreeSubtermVisitor(var_ctxt)
    t.traverse(var_ctxt, visitor)
    return visitor.collector

class FuncVisitor(Visitor):
    """Obtain the set of all free subterms with given function application."""
    def __init__(self, var_ctxt: VarContext, func_name: str):
        self.var_ctxt = var_ctxt.clone()
        self.func_name = func_name
        self.collector: set[OSTerm] = set()

    def visit(self, var_ctxt: VarContext, t: OSTerm):
        if is_fun(t, self.func_name) and self.var_ctxt.is_free(t):
            self.collector.add(t)

def get_all_func_subterms(var_ctxt: VarContext, t: OSTerm, func_name: str) -> set[OSTerm]:
    """Return set of all free subterms of t with given function name."""
    visitor = FuncVisitor(var_ctxt, func_name)
    t.traverse(var_ctxt, visitor)
    return visitor.collector
