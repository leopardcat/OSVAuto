"""
Definition of OS terms
"""

from typing import Callable, Dict, Iterable, Optional, Set, Tuple, List, TypeGuard

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


class OSTerm:
    """Base class for terms."""
    # Any term has a type
    type: Optional[OSType]

    def priority(self):
        """Return priority of a term during printing."""
        raise NotImplementedError("priority: %s" % type(self))
    
    def subst(self, inst: Dict[str, "OSTerm"]) -> "OSTerm":
        """Substitute variables for terms according to inst."""
        raise NotImplementedError("subst: %s" % type(self))
    
    def subst_type(self, tyinst: Dict[str, OSType]) -> "OSTerm":
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

    def get_vars_inplace(self, ty_vars: List[str], vars: List["OSVar"]):
        """Add set of variables into vars."""
        raise NotImplementedError("get_vars_inplace: %s" % type(self))
    
    def get_vars(self) -> Tuple[Tuple[str], Tuple["OSVar"]]:
        """Obtain the set of (type) variables.
        
        Returns
        -------
        Tuple[str]
            list of type variables
        Tuple[OSVar]
            list of variables
            
        """
        ty_vars, vars = list(), list()
        self.get_vars_inplace(ty_vars, vars)
        return tuple(ty_vars), tuple(vars)

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
    
    def get_funcs_inplace(self, funcs: List[Tuple[str, OSType]]):
        """Return the set of functions appearing in the term."""
        raise NotImplementedError("get_func_inplace: %s" % type(self))
    
    def get_funcs(self) -> Tuple[Tuple[str, OSType]]:
        """Obtain the set of functions appearing in the term."""
        funcs = list()
        self.get_funcs_inplace(funcs)
        return tuple(funcs)
    
    def apply_subterm(self, f: Callable[["OSTerm"], "OSTerm"]) -> "OSTerm":
        """Apply transformation function to all subterms."""
        raise NotImplementedError("apply_subterm: %s" % type(self))

    def get_subterms_inplace(self, subterms: List["OSTerm"]):
        def insert(t: OSTerm):
            if t not in subterms:
                subterms.append(t)
        self.apply_subterm(insert)

    def get_subterms(self) -> Tuple["OSTerm"]:
        subterms = list()
        self.get_subterms_inplace(subterms)
        return tuple(subterms)
    
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
        """Change all (type) variables into schematic."""
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

    def __str__(self):
        return "_"
    
    def __repr__(self):
        return "OSWildcard(%s)" % self.type

    def __hash__(self):
        return hash(("OSWildCard", self.type))

    def subst(self, inst: Dict[str, OSTerm]) -> OSTerm:
        return self
    
    def subst_type(self, tyinst: Dict[str, OSType]) -> OSTerm:
        return OSWildcard(type=self.type.subst(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self

    def get_vars_inplace(self, ty_vars: List[str], vars: List["OSVar"]):
        if self.type:
            self.type.get_vars_inplace(ty_vars)

    def get_funcs_inplace(self, funcs: List[Tuple[str, OSType]]):
        pass

    def apply_subterm(self, f: Callable[[OSTerm], OSTerm]) -> OSTerm:
        return f(self)

class OSUnknown(OSTerm):
    """Unknown term.
    
    This is used to represent some part of the term has unknown value,
    written as "?". It is used, for example, during reconstruction of
    SMT counterexamples, where some term has no value in the model.

    """
    def __init__(self, *, type: Optional[OSType] = None):
        self.type = type
        self.assert_init_type()

    def priority(self):
        return 100
    
    def __eq__(self, other):
        return isinstance(other, OSUnknown) and self.type == other.type

    def __str__(self):
        return "?"
    
    def __repr__(self):
        return "OSUnknown(%s)" % self.type

    def __hash__(self):
        return hash(("OSUnknown", self.type))

    def subst(self, inst: Dict[str, OSTerm]) -> OSTerm:
        return self
    
    def subst_type(self, tyinst: Dict[str, OSType]) -> OSTerm:
        return OSUnknown(type=self.type.subst(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self

    def get_vars_inplace(self, ty_vars: List[str], vars: List["OSVar"]):
        if self.type:
            self.type.get_vars_inplace(ty_vars)

    def get_funcs_inplace(self, funcs: List[Tuple[str, OSType]]):
        pass

    def apply_subterm(self, f: Callable[[OSTerm], OSTerm]) -> OSTerm:
        return f(self)

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

    def __str__(self):
        return self.name

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

    def subst(self, inst: Dict[str, OSTerm]) -> OSTerm:
        if self.name in inst:
            return inst[self.name]
        else:
            return self
        
    def subst_type(self, tyinst: Dict[str, OSType]) -> OSTerm:
        return OSVar(self.name, type=self.type.subst(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self

    def get_vars_inplace(self, ty_vars: List[str], vars: List["OSVar"]):
        if self.type:
            self.type.get_vars_inplace(ty_vars)
        if self not in vars:
            vars.append(self)

    def get_funcs_inplace(self, funcs: List[Tuple[str, OSType]]):
        pass

    def apply_subterm(self, f: Callable[[OSTerm], OSTerm]) -> OSTerm:
        return f(self)

class OSConst(OSTerm):
    """Constant terms.
    
    These refer to constant values that are defined in the theory, roughly
    corresponding to macro definitions in C. Type of constants are either
    provided at first or set during type inference.

    """
    def __init__(self, name: str, *, type: Optional[OSType] = None):
        self.name = name
        self.type = type
        self.assert_init_type()

    def priority(self):
        return 100

    def __eq__(self, other):
        return isinstance(other, OSConst) and self.name == other.name

    def __str__(self):
        return self.name

    def __repr__(self):
        return "OSConst(%s, %s)" % (self.name, self.type)

    def __hash__(self):
        return hash(("OSConst", self.name, self.type))

    def subst(self, inst: Dict[str, OSTerm]) -> OSTerm:
        return self

    def subst_type(self, tyinst: Dict[str, OSType]) -> OSTerm:
        return OSConst(self.name, type=self.type.subst(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self

    def get_vars_inplace(self, ty_vars: List[str], vars: List[OSVar]):
        if self.type:
            self.type.get_vars_inplace(ty_vars)

    def get_funcs_inplace(self, funcs: List[Tuple[str, OSType]]):
        pass

    def apply_subterm(self, f: Callable[[OSTerm], OSTerm]) -> OSTerm:
        return f(self)

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
        if isinstance(self.val, bool):
            self.type = os_struct.Bool
        self.assert_init_type()

    def priority(self):
        return 100

    def __eq__(self, other):
        return isinstance(other, OSNumber) and self.val == other.val and self.type == other.type

    def __str__(self):
        if isinstance(self.val, bool):
            if self.val == True:
                return "true"
            else:
                return "false"
        else:
            return str(self.val)

    def __repr__(self):
        return "OSNumber(%s, %s)" % (self.val, self.type)

    def __hash__(self):
        return hash(("OSNumber", self.val, self.type))

    def subst(self, inst: Dict[str, OSTerm]) -> OSTerm:
        return self
    
    def subst_type(self, tyinst: Dict[str, OSType]) -> OSTerm:
        return OSNumber(self.val, self.type.subst(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self

    def get_vars_inplace(self, ty_vars: List[str], vars: List[OSVar]):
        if self.type:
            self.type.get_vars_inplace(ty_vars)

    def get_funcs_inplace(self, funcs: List[Tuple[str, OSType]]):
        pass

    def apply_subterm(self, f: Callable[[OSTerm], OSTerm]) -> OSTerm:
        return f(self)

uop_priority = {
    '!': 90, '~': 90, "-": 90,
}

op_priority = {
    "*": 87, "/": 87,
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

    def __str__(self):
        if len(self.args) == 1:
            s = str(self.args[0])
            if self.args[0].priority() < self.priority():
                s = '(' + s + ')'
            return "%s%s" % (self.op, s)
        elif len(self.args) == 2:
            s1, s2 = str(self.args[0]), str(self.args[1])
            if self.op == "&&":
                conjs = split_conj(self)
                str_conjs = list()
                for conj in conjs:
                    s = str(conj)
                    if conj.priority() < self.priority():
                        s = '(' + s + ')'
                    str_conjs.append(s)
                return " &&\n".join(str_conjs)
            elif self.op == "->":
                As, C = strip_implies(self)
                return " ->\n".join(str(t) for t in As + (C,))
            if self.op in ("&&", "||", "->"):
                if self.args[0].priority() <= self.priority():
                    s1 = '(' + s1 + ')'
                if self.args[1].priority() < self.priority():
                    s2 = '(' + s2 + ')'
            else:
                if self.args[0].priority() < self.priority():
                    s1 = '(' + s1 + ')'
                if self.args[1].priority() <= self.priority():
                    s2 = '(' + s2 + ')'
            return "%s %s %s" % (s1, self.op, s2)
        else:
            raise NotImplementedError

    def __repr__(self):
        return "OSOp(%s, %s, %s)" % (self.op, ", ".join(repr(arg) for arg in self.args), self.type)
    
    def __hash__(self):
        return hash(("OSOp", self.op, self.args, self.type))

    def subst(self, inst: Dict[str, OSTerm]) -> OSTerm:
        return OSOp(self.op, *(arg.subst(inst) for arg in self.args), type=self.type)

    def subst_type(self, tyinst: Dict[str, OSType]) -> OSTerm:
        return OSOp(self.op, *(arg.subst_type(tyinst) for arg in self.args),
                    type=self.type.subst(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self
        for arg in self.args:
            arg.assert_type_checked()

    def get_vars_inplace(self, ty_vars: List[str], vars: List[OSVar]):
        if self.type:
            self.type.get_vars_inplace(ty_vars)
        for arg in self.args:
            arg.get_vars_inplace(ty_vars, vars)

    def get_funcs_inplace(self, funcs: List[Tuple[str, OSType]]):
        # Currently we do not consider operators to be functions
        for arg in self.args:
            arg.get_funcs_inplace(funcs)

    def apply_subterm(self, f: Callable[[OSTerm], OSTerm]) -> OSTerm:
        args = [arg.apply_subterm(f) for arg in self.args]
        return f(OSOp(self.op, *args, type=self.type))

class OSFun(OSTerm):
    """Application of a function, predicate, or constructor.
    
    Some functions have special syntax:

    ite(cond, t1, t2) is written as if (cond) { t1 } else { t2 }
    pair(t1, t2) is written as (t1, t2)
    nth(a, i) is written as a[i]
    Store(a, i, v) is written as a[i := v]
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

    def __str__(self):
        if self.func_name == "ite":
            res = "if (%s) {\n" % self.args[0]
            res += indent(str(self.args[1])) + "\n"
            res += "} else {\n"
            res += indent(str(self.args[2])) + "\n"
            res += "}"
            return res
        elif self.func_name == "pair":
            return "(%s, %s)" % self.args
        elif self.func_name == 'nth':
            return "%s[%s]" % self.args
        elif self.func_name == 'Store':
            return "%s[%s := %s]" % self.args
        elif self.func_name == 'emptyMap':
            return "{}"
        elif self.func_name == 'updateMap':
            # If the term is a literal map (as detected by strip_map), print
            # it as a literal map. Otherwise print in update form.
            try:
                map = strip_map(self)
                res = "{\n"
                for k, v in map.items():
                    res += "    %s: %s,\n" % (k, v)
                res += "}"
                return res
            except OSTermException:
                return "updateMap(%s, %s, %s)" % (self.args[0], self.args[1], self.args[2])
        elif self.func_name == 'nil':
            return "[]"
        elif self.func_name == 'cons':
            # If the term is a literal list (as detected by strip_list), print
            # it as a literal list. Otherwise print in cons form.
            try:
                lst = strip_list(self)
                return "[%s]" % (", ".join(str(t) for t in lst))
            except OSTermException:
                return "cons(%s, %s)" % (self.args[0], self.args[1])
        elif len(self.args) == 0:
            return self.func_name
        else:
            return "%s(%s)" % (self.func_name, ", ".join(str(arg) for arg in self.args))
        
    def __repr__(self):
        if self.args:
            return "OSFun(%s, %s, %s)" % (
                repr(self.func_name), ", ".join(repr(arg) for arg in self.args), self.type)
        else:
            return "OSFun(%s, %s)" % (repr(self.func_name), self.type)

    def __hash__(self):
        return hash(("OSFun", self.func_name, self.args, self.type))

    def subst(self, inst: Dict[str, OSTerm]) -> OSTerm:
        return OSFun(self.func_name, *(arg.subst(inst) for arg in self.args), type=self.type)

    def subst_type(self, tyinst: Dict[str, OSType]) -> OSTerm:
        return OSFun(self.func_name, *(arg.subst_type(tyinst) for arg in self.args),
                     type=self.type.subst(tyinst))
    
    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self
        for arg in self.args:
            arg.assert_type_checked()

    def get_vars_inplace(self, ty_vars: Set[str], vars: List[OSVar]):
        if self.type:
            self.type.get_vars_inplace(ty_vars)
        for arg in self.args:
            arg.get_vars_inplace(ty_vars, vars)

    def get_funcs_inplace(self, funcs: List[Tuple[str, OSType]]):
        if len(self.args) == 0:
            func = (self.func_name, self.type)
        else:
            arg_types = [arg.type for arg in self.args]
            func = (self.func_name, os_struct.OSFunctionType(*(arg_types + [self.type])))
        if func not in funcs:
            funcs.append(func)
        for arg in self.args:
            arg.get_funcs_inplace(funcs)

    def apply_subterm(self, f: Callable[[OSTerm], OSTerm]) -> OSTerm:
        args = [arg.apply_subterm(f) for arg in self.args]
        return f(OSFun(self.func_name, *args, type=self.type))

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

    def __str__(self):
        return "%s.%s" % (self.expr, self.field)
    
    def __repr__(self):
        return "FieldGet(%s, %s)" % (repr(self.expr), repr(self.field))

    def __hash__(self):
        return hash(("FieldGet", self.expr, self.field, self.type))

    def subst(self, inst: Dict[str, OSTerm]) -> OSTerm:
        return FieldGet(self.expr.subst(inst), self.field, type=self.type)
    
    def subst_type(self, tyinst: Dict[str, OSType]) -> OSTerm:
        return FieldGet(self.expr.subst_type(tyinst), self.field, type=self.type.subst(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self
        self.expr.assert_type_checked()

    def get_vars_inplace(self, ty_vars: List[str], vars: List[OSVar]):
        if self.type:
            self.type.get_vars_inplace(ty_vars)
        self.expr.get_vars_inplace(ty_vars, vars)

    def get_funcs_inplace(self, funcs: List[Tuple[str, OSType]]):
        self.expr.get_funcs_inplace(funcs)

    def apply_subterm(self, f: Callable[[OSTerm], OSTerm]) -> OSTerm:
        return f(FieldGet(self.expr.apply_subterm(f), self.field, type=self.type))

class FieldUpdate:
    """Single field update within a structure"""
    def __init__(self, field_name: str, expr: OSTerm = None):
        self.field_name = field_name
        self.expr = expr

    def __eq__(self, other):
        return isinstance(other, FieldUpdate) and self.field_name == other.field_name and \
            self.expr == other.expr

    def __str__(self):
        return "%s := %s" % (self.field_name, self.expr)
    
    def __repr__(self):
        return "FieldUpdate(%s, %s)" % (self.field_name, repr(self.expr))

    def __hash__(self):
        return hash(("FieldUpdate", self.field_name, self.expr))

    def subst(self, inst: Dict[str, OSTerm]) -> "FieldUpdate":
        return FieldUpdate(self.field_name, self.expr.subst(inst))
    
    def subst_type(self, tyinst: Dict[str, OSType]) -> "FieldUpdate":
        return FieldUpdate(self.field_name, self.expr.subst_type(tyinst))
    
    def apply_subterm(self, f: Callable[[OSTerm], OSTerm]) -> "FieldUpdate":
        return FieldUpdate(self.field_name, self.expr.apply_subterm(f))

class OSStructUpdate(OSTerm):
    """Update several fields of a structure.
    
    Attributes
    ----------
    ori_expr : OSTerm
        structure before update
    updates : Tuple[FieldUpdate]
        list of updates to the structure
    dict_updates : Dict[str, OSTerm]
        mapping from field name to updated value
    type : OSType
        type of the term, automatically derived to be the type of ori_expr.
    
    """
    def __init__(self, ori_expr: OSTerm, updates: Iterable[FieldUpdate]):
        self.ori_expr = ori_expr
        self.updates = tuple(updates)
        self.type = ori_expr.type

        # Update as a dictionary
        self.dict_updates: Dict[str, OSTerm] = dict()
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

    def __str__(self):
        return "%s(%s)" % (self.ori_expr, ", ".join(str(update) for update in self.updates))

    def __repr__(self):
        return "OSStructUpdate(%s, %s, %s)" % (repr(self.ori_expr), self.updates, self.type)

    def __hash__(self):
        return hash(("OSStructUpdate", self.ori_expr, self.updates))

    def subst(self, inst: Dict[str, OSTerm]) -> OSTerm:
        return OSStructUpdate(self.ori_expr.subst(inst), [update.subst(inst) for update in self.updates])

    def subst_type(self, tyinst: Dict[str, OSType]) -> OSTerm:
        return OSStructUpdate(self.ori_expr.subst_type(tyinst),
                              [update.subst_type(tyinst) for update in self.updates])

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self
        self.ori_expr.assert_type_checked()
        for update in self.updates:
            update.expr.assert_type_checked()

    def get_vars_inplace(self, ty_vars: List[str], vars: List[OSVar]):
        self.ori_expr.get_vars_inplace(ty_vars, vars)
        for update in self.updates:
            update.expr.get_vars_inplace(ty_vars, vars)

    def get_funcs_inplace(self, funcs: List[Tuple[str, OSType]]):
        self.ori_expr.get_funcs_inplace(funcs)
        for update in self.updates:
            update.expr.get_funcs_inplace(funcs)

    def apply_subterm(self, f: Callable[[OSTerm], OSTerm]) -> OSTerm:
        updates = [update.apply_subterm(f) for update in self.updates]
        return f(OSStructUpdate(self.ori_expr.apply_subterm(f), updates))

class OSStructVal(OSTerm):
    """Structure literal expression.
    
    Each literal is given by structure name, and a list of correspondence
    between field names and values.

    Attributes
    ----------
    struct_name : str
        name of the structure
    vals : Tuple[Tuple[str, OSTerm]]
        list of field name and value pairs
    dict_vals : Dict[str, OSTerm]
        Mapping from field name to value
    type : OSType
        Type of the term, derived to be struct <struct_name>.

    """
    def __init__(self, struct_name: str, vals: Iterable[Tuple[str, OSTerm]]):
        self.struct_name = struct_name
        self.vals = tuple(vals)
        self.dict_vals: Dict[str, OSTerm] = dict()
        for field, val in self.vals:
            self.dict_vals[field] = val
        self.type = os_struct.OSStructType(struct_name)
        self.assert_init_type()

    def priority(self):
        return 100
    
    def __eq__(self, other):
        return isinstance(other, OSStructVal) and self.struct_name == other.struct_name and \
            self.vals == other.vals

    def __str__(self):
        return "%s{{%s}}" % (self.struct_name, ", ".join("%s: %s" % (k, v) for k, v in self.vals))

    def __repr__(self):
        return "OSStructVal(%s, %s)" % (self.struct_name, self.vals)

    def __hash__(self):
        return hash(("OSStructVal", self.struct_name, self.vals))

    def subst(self, inst: Dict[str, OSTerm]) -> OSTerm:
        return OSStructVal(self.struct_name, [(field, val.subst(inst)) for field, val in self.vals])

    def subst_type(self, tyinst: Dict[str, OSType]) -> OSTerm:
        return OSStructVal(self.struct_name, [(field, val.subst_type(tyinst)) for field, val in self.vals])

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self
        for _, val in self.vals:
            val.assert_type_checked()

    def get_vars_inplace(self, ty_vars: List[str], vars: List[OSVar]):
        if self.type:
            self.type.get_vars_inplace(ty_vars)
        for _, val in self.vals:
            val.get_vars_inplace(ty_vars, vars)

    def get_funcs_inplace(self, funcs: List[Tuple[str, OSType]]):
        for _, val in self.vals:
            val.get_funcs_inplace(funcs)

    def apply_subterm(self, f: Callable[[OSTerm], OSTerm]) -> OSTerm:
        vals = [(field, val.apply_subterm(f)) for field, val in self.vals]
        return f(OSStructVal(self.struct_name, vals))

class OSLet(OSTerm):
    """Let expression.
    
    A let expression has the form "let x = expr in rhs end", it defines
    a bound variable x that can be used in rhs.

    Attributes
    ----------
    var_name : str
        name of the introduced variable.
    expr : OSTerm
        term the new variable is set to.
    type : OSType
        type of the let term, automatically derived to be type of rhs.

    """
    def __init__(self, var_name: str, expr: OSTerm, rhs: OSTerm):
        self.var_name = var_name
        self.expr = expr
        self.rhs = rhs
        self.type = self.rhs.type
        self.assert_init_type()

    def priority(self):
        return 10

    def __eq__(self, other):
        # Note we do not compare according to alpha-equivalence
        return isinstance(other, OSLet) and self.var_name == other.var_name and \
            self.expr == other.expr and self.rhs == other.rhs

    def __str__(self):
        res = "let %s = %s in\n" % (self.var_name, self.expr)
        res += indent(str(self.rhs)) + '\n'
        res += "end"
        return res

    def __repr__(self):
        return "OSLet(%s, %s, %s)" % (self.var_name, repr(self.expr), repr(self.rhs))

    def __hash__(self):
        return hash(("OSLet", self.var_name, self.expr, self.rhs))

    def subst(self, inst: Dict[str, OSTerm]) -> OSTerm:
        # Make a new copy as inst is modified
        inst2 = dict(inst)

        # Bound variables are never substituted
        if self.var_name in inst2:
            del inst2[self.var_name]

        # Moreover, if any of the substituted values contain variables
        # that conflict with the bound variables, rename the bound variables
        ty_vars: List[str] = list()
        vars: List[OSVar] = list()
        for _, t in inst2.items():
            t.get_vars_inplace(ty_vars, vars)
        vars: Set[OSVar] = set([var.name for var in vars])
        new_params = list()
        body_inst = dict()
        new_name = variant_names(vars, self.var_name)
        new_var = OSVar(new_name, type=self.expr.type)
        new_params.append(new_var)
        vars.add(new_name)
        if new_name != self.var_name:
            body_inst[self.var_name] = new_var
        return OSLet(new_name, self.expr.subst(inst2), self.rhs.subst(body_inst).subst(inst2))
    
    def subst_type(self, tyinst: Dict[str, OSType]) -> OSType:
        return OSLet(self.var_name, self.expr.subst_type(tyinst), self.rhs.subst(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self
        self.expr.assert_type_checked()
        self.rhs.assert_type_checked()

    def get_vars_inplace(self, ty_vars: List[str], vars: List[OSVar]):
        self.expr.get_vars_inplace(ty_vars, vars)
        self.rhs.type.get_vars_inplace(ty_vars)

        # Obtain the list of variables in the body, then subtract bound variable.
        rhs_ty_vars, rhs_vars = self.rhs.get_vars()
        for rhs_ty_var in rhs_ty_vars:
            if rhs_ty_var not in ty_vars:
                ty_vars.append(rhs_ty_var)
        for rhs_var in rhs_vars:
            if rhs_var.name != self.var_name and rhs_var not in vars:
                vars.append(rhs_var)

    def get_funcs_inplace(self, funcs: List[Tuple[str, OSType]]):
        self.expr.get_funcs_inplace(funcs)
        self.rhs.get_funcs_inplace(funcs)

    def apply_subterm(self, f: Callable[[OSTerm], OSTerm]) -> OSTerm:
        return f(OSLet(self.var_name, self.expr.apply_subterm(f), self.rhs.apply_subterm(f)))

class OSSwitchBranch:
    """Base class for switch branches."""

    # Body of the switch branch
    expr : OSTerm

    def subst(self, inst: Dict[str, OSTerm]) -> "OSSwitchBranch":
        raise NotImplementedError
    
    def subst_type(self, tyinst: Dict[str, OSType]) -> "OSSwitchBranch":
        raise NotImplementedError

    def assert_type_checked(self):
        raise NotImplementedError

    def get_vars_inplace(self, ty_vars: List[str], vars: List[OSVar]):
        raise NotImplementedError
    
    def get_funcs_inplace(self, funcs: List[Tuple[str, OSType]]):
        raise NotImplementedError
    
    def apply_subterm(self, f: Callable[[OSTerm], OSTerm]) -> "OSSwitchBranch":
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

    def __str__(self):
        res = "case %s:\n" % self.pattern
        res += indent(str(self.expr))
        return res
    
    def __repr__(self):
        return "OSSwitchBranchCase(%s, %s)" % (repr(self.pattern), repr(self.expr))
        
    def __eq__(self, other):
        return isinstance(other, OSSwitchBranchCase) and self.pattern == other.pattern and \
            self.expr == other.expr
    
    def __hash__(self):
        return hash(("OSSwitchBranchCase", self.pattern, self.expr))

    def subst(self, inst: Dict[str, OSTerm]) -> OSSwitchBranch:
        # Make a new copy as inst is modified
        inst2 = dict(inst)

        # Bound variables are never substituted
        _, bound_vars = self.pattern.get_vars()
        for var in bound_vars:
            if var.name in inst2:
                del inst2[var.name]
        
        # Moreover, if any of the substituted values contain variables
        # that conflict with the bound variables, rename the bound variables
        ty_vars: List[str] = list()
        vars: List[OSVar] = list()
        for _, t in inst2.items():
            t.get_vars_inplace(ty_vars, vars)
        vars: Set[OSVar] = set([var.name for var in vars])
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
                                  self.expr.subst(body_inst).subst(inst))

    def subst_type(self, tyinst: Dict[str, OSType]) -> OSSwitchBranch:
        return OSSwitchBranchCase(self.pattern.subst_type(tyinst), self.expr.subst_type(tyinst))

    def assert_type_checked(self):
        self.pattern.assert_type_checked()
        self.expr.assert_type_checked()

    def get_vars_inplace(self, ty_vars: List[str], vars: List[OSVar]):
        _, bound_vars = self.pattern.get_vars()
        expr_ty_vars, expr_vars = self.expr.get_vars()
        for expr_ty_var in expr_ty_vars:
            if expr_ty_var not in ty_vars:
                ty_vars.append(expr_ty_var)
        for expr_var in expr_vars:
            if expr_var not in bound_vars and expr_var not in vars:
                vars.append(expr_var)

    def get_funcs_inplace(self, funcs: List[Tuple[str, OSType]]):
        # We do not consider datatype constructors in the pattern to be
        # function calls.
        self.expr.get_funcs_inplace(funcs)

    def apply_subterm(self, f: Callable[[OSTerm], OSTerm]) -> OSSwitchBranch:
        return OSSwitchBranchCase(self.pattern, self.expr.apply_subterm(f))

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

    def __str__(self):
        return "default: %s" % self.expr
    
    def __repr__(self):
        return "OSSwitchBranchDefault(%s)" % repr(self.expr)

    def __eq__(self, other):
        return isinstance(other, OSSwitchBranchDefault) and self.expr == other.expr
    
    def __hash__(self):
        return hash(("OSSwitchBranchDefault", self.expr))

    def subst(self, inst: Dict[str, OSTerm]) -> OSSwitchBranch:
        return OSSwitchBranchDefault(self.expr.subst(inst))

    def subst_type(self, tyinst: Dict[str, OSType]) -> OSSwitchBranch:
        return OSSwitchBranchDefault(self.expr.subst_type(tyinst))

    def assert_type_checked(self):
        self.expr.assert_type_checked()

    def get_vars_inplace(self, ty_vars: List[str], vars: List[OSVar]):
        self.expr.get_vars_inplace(ty_vars, vars)

    def get_funcs_inplace(self, funcs: List[Tuple[str, OSType]]):
        self.expr.get_funcs_inplace(funcs)

    def apply_subterm(self, f: Callable[[OSTerm], OSTerm]) -> OSSwitchBranch:
        return OSSwitchBranchDefault(self.expr.apply_subterm(f))

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
    branches : Tuple[OSSwitchBranch]
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

    def __str__(self):
        res = "switch (%s) {\n" % self.switch_expr
        for branch in self.branches:
            res += indent(str(branch) + ";") + '\n'
        res += "}"
        return res
    
    def __repr__(self):
        return "Switch(%s, [%s])" % (repr(self.switch_expr), ', '.join(repr(branch) for branch in self.branches))
    
    def __eq__(self, other):
        return isinstance(other, OSSwitch) and self.switch_expr == other.switch_expr and \
            self.branches == other.branches

    def __hash__(self):
        return hash(("OSSwitch", self.switch_expr, self.branches, self.type))

    def priority(self):
        return 10

    def subst(self, inst: Dict[str, OSTerm]) -> OSTerm:
        return OSSwitch(self.switch_expr.subst(inst),
                        [branch.subst(inst) for branch in self.branches],
                        self.type)

    def subst_type(self, tyinst: Dict[str, OSType]) -> OSTerm:
        return OSSwitch(self.switch_expr.subst_type(tyinst),
                        [branch.subst_type(tyinst) for branch in self.branches],
                        self.type.subst(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self
        for branch in self.branches:
            branch.assert_type_checked()

    def get_vars_inplace(self, ty_vars: List[str], vars: List[OSVar]):
        self.switch_expr.get_vars_inplace(ty_vars, vars)
        for branch in self.branches:
            branch.get_vars_inplace(ty_vars, vars)

    def get_funcs_inplace(self, funcs: List[Tuple[str, OSType]]):
        self.switch_expr.get_funcs_inplace(funcs)
        for branch in self.branches:
            branch.get_funcs_inplace(funcs)

    def apply_subterm(self, f: Callable[[OSTerm], OSTerm]) -> OSTerm:
        branches = [branch.apply_subterm(f) for branch in self.branches]
        return f(OSSwitch(self.switch_expr.apply_subterm(f), branches, type=self.type))

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
    params : Tuple[OSVar]
        list of bound variables, these may appear in the body
    body : OSTerm
        body of the quantifier expression
    type : OSType
        type of the expression, derived to be Bool.

    """
    def __init__(self, quantifier: str, params: Iterable[OSVar], body: OSTerm):
        self.quantifier = quantifier
        self.params: Tuple[OSVar] = tuple(params)
        self.body = body
        self.type = os_struct.Bool

    def __str__(self):
        res = "%s (%s) {\n" % (self.quantifier, ", ".join(
            "%s %s" % (param.type, param.name) for param in self.params))
        res += indent(str(self.body))
        res += "\n}"
        return res
    
    def __eq__(self, other):
        return isinstance(other, OSQuant) and self.quantifier == other.quantifier and \
            self.params == other.params and self.body == other.body
    
    def __repr__(self):
        return "OSQuant(%s, %s, %s)" % (self.quantifier, self.params, self.body)
    
    def __hash__(self):
        return hash(("OSQuant", self.quantifier, self.params, self.body))
    
    def priority(self):
        return 10

    def subst(self, inst: Dict[str, OSTerm]) -> OSTerm:
        # Make a new copy as inst is modified
        inst2 = dict(inst)

        # Bound variables are never substituted
        for param in self.params:
            if param.name in inst2:
                del inst2[param.name]

        # Moreover, if any of the substituted values contain variables
        # that conflict with the bound variables, rename the bound variables
        ty_vars: List[str] = list()
        vars: List[OSVar] = list()
        for _, t in inst2.items():
            t.get_vars_inplace(ty_vars, vars)
        vars: Set[OSVar] = set([var.name for var in vars])
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
    
    def subst_type(self, tyinst: Dict[str, OSType]) -> OSTerm:
        return OSQuant(self.quantifier, [param.subst_type(tyinst) for param in self.params],
                       self.body.subst_type(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self
        for param in self.params:
            param.assert_type_checked()
        self.body.assert_type_checked()

    def get_vars_inplace(self, ty_vars: List[str], vars: List[OSVar]):
        # Obtain the list of variables in the body, then subtract bound variable.
        body_ty_vars, body_vars = self.body.get_vars()
        for body_ty_var in body_ty_vars:
            if body_ty_var not in ty_vars:
                ty_vars.append(body_ty_var)
        for body_var in body_vars:
            if body_var not in self.params and body_var not in vars:
                vars.append(body_var)

    def get_funcs_inplace(self, funcs: List[Tuple[str, OSType]]):
        self.body.get_funcs_inplace(funcs)

    def apply_subterm(self, f: Callable[[OSTerm], OSTerm]) -> OSTerm:
        return f(OSQuant(self.quantifier, self.params, self.body.apply_subterm(f)))

class OSQuantIn(OSTerm):
    """Quantifier expression, ranging over maps or lists."""
    def __init__(self, quantifier: str, param: OSVar, collection: OSTerm, body: OSTerm):
        self.quantifier = quantifier
        self.param = param
        self.collection = collection
        self.body = body
        self.type = os_struct.Bool

    def __str__(self):
        res = "%s (%s %s in %s).\n" % (self.quantifier, self.param.type, self.param.name, self.collection)
        res += indent(str(self.body))
        return res
    
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
        return 10

    def subst(self, inst: Dict[str, OSTerm]) -> OSTerm:
        # Make a new copy as inst is modified
        inst2 = dict(inst)

        # Bound variables are never substituted
        if self.param.name in inst2:
            del inst2[self.param.name]

        # Moreover, if any of the substituted values contain variables
        # that conflict with the bound variables, rename the bound variables
        ty_vars: List[str] = list()
        vars: List[OSVar] = list()
        for _, t in inst2.items():
            t.get_vars_inplace(ty_vars, vars)
        vars: Set[OSVar] = set([var.name for var in vars])
        body_inst = dict()

        new_name = variant_names(vars, self.param.name)
        new_var = OSVar(new_name, type=self.param.type)
        vars.add(new_name)
        if new_name != self.param.name:
            body_inst[self.param.name] = new_var
        return OSQuantIn(self.quantifier, new_var, self.collection.subst(inst2),
                         self.body.subst(body_inst).subst(inst2))
    
    def subst_type(self, tyinst: Dict[str, OSType]) -> OSTerm:
        return OSQuantIn(self.quantifier, self.param.subst_type(tyinst),
                         self.collection.subst_type(tyinst),
                         self.body.subst_type(tyinst))

    def assert_type_checked(self):
        assert self.type is not None, "assert_type_checked: failed on %s" % self
        self.param.assert_type_checked()
        self.collection.assert_type_checked()
        self.body.assert_type_checked()

    def get_vars_inplace(self, ty_vars: List[str], vars: List[OSVar]):
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

    def get_funcs_inplace(self, funcs: List[Tuple[str, OSType]]):
        self.collection.get_funcs_inplace(funcs)
        self.body.get_funcs_inplace(funcs)

    def apply_subterm(self, f: Callable[[OSTerm], OSTerm]) -> OSTerm:
        return f(OSQuantIn(self.quantifier, self.param, self.collection.apply_subterm(f),
                           self.body.apply_subterm(f)))

true = OSNumber(True)
false = OSNumber(False)

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

def empty_map(K: OSType, V: OSType) -> OSTerm:
    """Construct empty map."""
    return OSFun("emptyMap", type=os_struct.MapType(K, V))

def is_empty_map(t: OSTerm) -> TypeGuard[OSFun]:
    return isinstance(t, OSFun) and t.func_name == "emptyMap"

def is_update_map(t: OSTerm) -> TypeGuard[OSFun]:
    return isinstance(t, OSFun) and t.func_name == "updateMap"

def list_map(K: OSType, V: OSType, *pairs: Tuple[OSTerm, OSTerm]) -> OSTerm:
    """Convert a list of pairs into literal map."""
    res = empty_map(K, V)
    for k, v in pairs:
        res = OSFun("updateMap", k, v, res, type=os_struct.MapType(K, V))
    return res

def strip_map(t: OSTerm) -> Dict[OSTerm, OSTerm]:
    """Deconstruct literal map into Python dictionary."""
    res = dict()
    while True:
        if is_empty_map(t):
            break
        elif is_update_map(t):
            k, v, rest = t.args
            res[k] = v
            t = rest
        else:
            raise OSTermException("strip_map: %s" % t)
    return res

def indom(k: OSTerm, map: OSTerm) -> OSTerm:
    return OSFun("indom", k, map, type=os_struct.Bool)

def inlist(t: OSTerm, list: OSTerm) -> OSTerm:
    return OSFun("inlist", t, list, type=os_struct.Bool)

def is_nil(t: OSTerm) -> TypeGuard[OSFun]:
    return isinstance(t, OSFun) and t.func_name == "nil"

def is_cons(t: OSTerm) -> TypeGuard[OSFun]:
    return isinstance(t, OSFun) and t.func_name == "cons"

def strip_list(t: OSTerm) -> Tuple[OSTerm]:
    """Deconstruct literal list into Python list."""
    res = list()
    while True:
        if is_nil(t):
            break
        elif is_cons(t):
            v, rest = t.args
            res.append(v)
            t = rest
        else:
            raise OSTermException("strip_list: %s" % t)
    return res

def strip_array(t: OSTerm) -> Tuple[OSTerm, Dict[int, OSTerm]]:
    """Deconstruct array literal.
    
    Return value is a pair (default, updates), where updates is a mapping
    from index to values.

    """
    default = None
    res: Dict[int, OSTerm] = dict()

    def helper(t):
        nonlocal default
        if isinstance(t, OSFun) and t.func_name == "K":
            default = t.args[0]
        elif isinstance(t, OSFun) and t.func_name == "Store":
            helper(t.args[0])
            if not isinstance(t.args[1], OSNumber):
                raise OSTermException("strip_array: index %s" % t.args[1])
            if isinstance(t.args[1].val, bool):
                raise OSTermException("strip_array: index %s" % t.args[1].val)
            res[t.args[1].val] = t.args[2]
        else:
            raise OSTermException("strip_array: %s" % t)

    helper(t)
    if default is None:
        raise OSTermException("strip_array: %s" % t)
    return default, res

def integer(n: int) -> OSTerm:
    return OSNumber(n, type=os_struct.Int)

def eq(t1: OSTerm, t2: OSTerm) -> OSTerm:
    """Construct the term t1 == t2."""
    return OSOp("==", t1, t2, type=os_struct.Bool)

def is_eq(t: OSTerm) -> TypeGuard[OSOp]:
    """Check whether term has form t1 == t2."""
    return isinstance(t, OSOp) and t.op == "=="

def greater_eq(t1: OSTerm, t2: OSTerm) -> OSTerm:
    """Construct the term t1 >= t2."""
    return OSOp(">=", t1, t2, type=os_struct.Bool)

def less(t1: OSTerm, t2: OSTerm) -> OSTerm:
    """Construct the term t1 < t2."""
    return OSOp("<", t1, t2, type=os_struct.Bool)

def is_conj(t: OSTerm) -> TypeGuard[OSOp]:
    return isinstance(t, OSOp) and t.op == "&&"

def conj(t1: OSTerm, t2: OSTerm) -> OSTerm:
    return OSOp("&&", t1, t2, type=os_struct.Bool)

def split_conj(t: OSTerm) -> Tuple[OSTerm]:
    """Destruct a conjunction of a list of terms."""
    res = []
    def rec(t):
        if isinstance(t, OSOp) and t.op == "&&":
            res.append(t.args[0])
            rec(t.args[1])
        else:
            res.append(t)
    rec(t)
    return tuple(res)

def list_conj(ts: Iterable[OSTerm]) -> OSTerm:
    """Create a conjunction of a list of terms."""
    if not ts:
        raise AssertionError("list_conj: input is empty list")
    res = ts[-1]
    for t in reversed(ts[:-1]):
        res = OSOp("&&", t, res, type=os_struct.Bool)
    return res

def is_implies(t: OSTerm) -> TypeGuard[OSOp]:
    return isinstance(t, OSOp) and t.op == "->"

def strip_implies(t: OSTerm) -> Tuple[Tuple[OSTerm], OSTerm]:
    """Destruct implies expression.

    Given input term of the form
        A1 -> A2 -> ... -> An -> C
    return the pair (A1, ..., An) and C
    
    """
    assumes = list()
    while isinstance(t, OSOp) and t.op == "->":
        assumes.append(t.args[0])
        t = t.args[1]
    return tuple(assumes), t

def implies(assume: OSTerm, concl: OSTerm) -> OSTerm:
    return OSOp("->", assume, concl, type=os_struct.Bool)

def list_implies(assumes: Iterable[OSTerm], concl: OSTerm) -> OSTerm:
    """Given list [A1, A2, ..., An] and term C, form the term
    A1 -> A2 -> ... -> An -> C.

    """
    res = concl
    for assume in reversed(assumes):
        res = OSOp("->", assume, res, type=os_struct.Bool)
    return res

def strip_exists(t: OSTerm) -> Tuple[Tuple[OSVar], OSTerm]:
    """Destruct existential quantifier.
    
    Given input term of the form
        exists t1 ... tn. P
    return the pair (t1, ..., tn) and P

    """
    exists = list()
    while isinstance(t, OSQuant) and t.quantifier == "exists":
        exists.extend(t.params)
        t = t.body
    return tuple(exists), t

def strip_forall(t: OSTerm) -> Tuple[Tuple[OSVar], OSTerm]:
    """Destruct universal quantifier.
    
    Given input term of the form
        forall t1 ... tn. P
    return the pair (t1, ..., tn) and P

    """
    foralls = list()
    while isinstance(t, OSQuant) and t.quantifier == "forall":
        foralls.extend(t.params)
        t = t.body
    return tuple(foralls), t
