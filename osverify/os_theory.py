"""Theory definitions"""

from typing import Dict, Iterable, List, Optional, Tuple, Set

from osverify import os_struct
from osverify import os_term
from osverify import os_fixp
from osverify import os_query
from osverify.os_struct import OSType
from osverify.os_term import OSTerm


class Theorem:
    """Represents a proved theorem.
    
    A theorem is given by a list of type parameters, list of parameters,
    and a proposition.
    
    """
    def __init__(self, name: str, type_params: Iterable[str],
                 params: Iterable[os_term.OSVar], prop: OSTerm):
        self.name = name
        self.type_params = tuple(type_params)
        self.params = tuple(params)
        self.prop = prop
        self.sch_theorem = self.prop.make_all_schematic()

    def get_sch_theorem(self) -> OSTerm:
        """Obtain version of the theorem with schematic variables."""
        return self.sch_theorem
    
    def get_forall_theorem(self, tys: Iterable[OSType]) -> OSTerm:
        """Obtain version of the theorem with forall-quantification."""
        if len(self.type_params) != len(tys):
            raise AssertionError(
                "get_forall_theorem: expect %s type parameters for %s." % (len(self.type_params), self.name))
        tyinst = dict(zip(self.type_params, tys))
        res = self.prop.subst_type(tyinst)
        params = [param.subst_type(tyinst) for param in self.params]
        return os_term.OSQuant("forall", params, res)

class TheoremSpec:
    """Specification for applying a theorem."""
    def __init__(self, thm_name: str, tys: Iterable[os_struct.OSType]):
        self.thm_name = thm_name
        self.tys = tuple(tys)

    def __str__(self):
        if self.tys:
            return "%s<%s>" % (self.thm_name, ", ".join(str(ty) for ty in self.tys))
        else:
            return self.thm_name
        
    def __repr__(self):
        return "TheoremSpec(%s, %s)" % (self.thm_name, repr(self.tys))

class OSTheory:
    """Represents the current theory"""
    def __init__(self):
        # List of declarations
        self.decls = []

        # Mapping from structure to their definitions
        self.structs: Dict[str, os_struct.Struct] = dict()

        # Mapping from constants to their values
        self.const_val: Dict[str, int] = dict()

        # Mapping from functions to their definition
        self.fixps: Dict[str, os_fixp.OSFunction] = dict()

        # Mapping of type alias definitions
        self.typedefs: Dict[str, OSType] = dict()

        # Mapping of datatype definitions
        self.datatypes: Dict[str, os_struct.Datatype] = dict()

        # Mapping of axiomatic datatype definitions
        self.axiom_types: Dict[str, OSType] = dict()

        # Mapping from constructors to their datatype
        self.constr_datatype: Dict[str, str] = dict()

        # Mapping from constructors to their types
        self.constr_types: Dict[str, OSType] = dict()

        # Mapping of axiomatic function definitions
        self.axiom_func: Dict[str, os_struct.AxiomDef] = dict()

        # Mapping from theorem (query) names to queries
        self.queries: Dict[str, os_query.Query] = dict()

        # Mapping from theorem names to statements
        self.theorems: Dict[str, Theorem] = dict()

        # List of type parameters for each theorem.
        self.type_params: Dict[str, Tuple[str]] = dict()

        # Mapping from attributes to list of theorem having that attribute.
        self.attribute_map: Dict[str, List[str]] = dict()

        # List of equality theorems used for rewriting
        self.attribute_map["rewrite"] = list()

    def add_theorem(self, name: str, thm: Theorem):
        """Add theorem with the given name."""
        if name in self.theorems:
            raise AssertionError("add_theorem: %s already exists" % name)

        self.theorems[name] = thm

    def add_struct(self, struct: os_struct.Struct):
        """Add structure definition to the theory."""
        if struct.struct_name in self.structs:
            raise AssertionError("add_struct: structure %s already defined" % struct.struct_name)
        
        self.decls.append(struct)
        self.structs[struct.struct_name] = struct

    def add_consts(self, consts: os_struct.ConstDefList):
        """Add constant declarations to the theory."""
        self.decls.append(consts)
        for const_def in consts.const_defs:
            if const_def.const_name in self.const_val:
                raise AssertionError("add_consts: constant %s already defined" % const_def.const_name)
            self.const_val[const_def.const_name] = const_def.val

    def add_function(self, fixp: os_fixp.OSFunction):
        """Add function declaration to the theory"""
        if fixp.name in self.fixps:
            raise AssertionError("add_function: function %s already defined" % fixp.name)
        self.decls.append(fixp)
        self.fixps[fixp.name] = fixp

        # Add equality corresponding to the function definition
        eq = os_term.eq(os_term.OSFun(fixp.name, *fixp.params, type=fixp.ret_type), fixp.body)
        fixp_def = fixp.name + "_def"
        self.add_theorem(fixp_def, Theorem(fixp_def, fixp.type_params, fixp.params, eq))

        if not fixp.is_recursive_func():
            # If function is not recursive, add 'rewrite' attribute for
            # definition
            self.attribute_map['rewrite'].append(fixp_def)
        elif isinstance(fixp.body, os_term.OSSwitch) and fixp.body.switch_expr in fixp.params and \
            is_standard_switch(self, fixp.body):
            # Otherwise, if the function body is switch on one of the input parameters,
            # add 'rewrite' attribute for simplification rules
            switch_id = fixp.params.index(fixp.body.switch_expr)
            for i, branch in enumerate(fixp.body.branches):
                if isinstance(branch, os_term.OSSwitchBranchCase):
                    lhs = os_term.OSFun(
                        fixp.name, *(fixp.params[:switch_id] + (branch.pattern,) + fixp.params[switch_id+1:]),
                        type=fixp.ret_type)
                    eq = os_term.eq(lhs, branch.expr)
                    fixp_simp = fixp.name + "_simps" + str(i+1)
                    self.add_theorem(fixp_simp, Theorem(fixp_simp, fixp.type_params, fixp.params, eq))
                    self.attribute_map['rewrite'].append(fixp_simp)
                else:
                    # TODO: add default cases
                    pass

    def get_sch_theorem(self, thm_name: str) -> OSTerm:
        """Obtain theorem with schematic variables.
        
        This version of theorem is suited for matching within the tool.

        """
        if thm_name not in self.theorems:
            raise AssertionError("get_theorem: %s not found" % thm_name)
        return self.theorems[thm_name].get_sch_theorem()

    def get_forall_theorem(self, thm_name: str, tys: Iterable[OSType]) -> OSTerm:
        """Obtain theorem with forall-quantification.
        
        This version of theorem is suited for input into SMT solver.

        """
        if thm_name not in self.theorems:
            raise AssertionError("get_theorem: %s not found" % thm_name)
        return self.theorems[thm_name].get_forall_theorem(tys)

    def get_definition(self, func_name: str) -> OSTerm:
        thm_name = func_name + "_def"
        return self.get_sch_theorem(thm_name)

    def is_defined_type(self, name: str):
        """Return whether name is a defined type."""
        return name in self.typedefs or name in self.datatypes

    def add_typedef(self, typedef: os_struct.TypeDef):
        """Add type alias definition."""
        type_name = typedef.type_name
        if self.is_defined_type(type_name):
            raise AssertionError("add_typedef: type %s already defined" % type_name)
        
        self.typedefs[type_name] = typedef.type

    def add_datatype(self, datatype: os_struct.Datatype):
        """Add datatype definition."""
        type_name = datatype.name
        if self.is_defined_type(type_name):
            raise AssertionError("add_datatype: type %s already defined" % type_name)
        
        self.datatypes[type_name] = datatype
        if len(datatype.branches) == 0:
            return
        # Add field constructors
        ret_type = os_struct.OSHLevelType(type_name, *(os_struct.OSBoundType(param) for param in datatype.params))
        for branch in datatype.branches:
            name = branch.constr_name
            if name in self.constr_datatype:
                raise AssertionError("add_datatype: constructor %s already defined" % branch.constr_name)
            if len(branch.params) == 0:
                self.constr_datatype[name] = type_name
                self.constr_types[name] = ret_type
            else:
                types = [param_type for _, param_type in branch.params]
                self.constr_datatype[name] = type_name
                self.constr_types[name] = os_struct.OSFunctionType(*(types + [ret_type]))

    def add_axiom_type(self, axiom_type: os_struct.AxiomType):
        self.axiom_types[axiom_type.name] = axiom_type

    def add_axiom_func(self, axiom_func: os_struct.AxiomDef):
        self.axiom_func[axiom_func.func_name] = axiom_func

    def add_query(self, query: os_query.Query):
        """Add a query."""
        if query.query_name in self.queries:
            raise AssertionError("add_query: query %s already exists" % query.query_name)
        self.queries[query.query_name] = query
        if query.query_name in self.theorems:
            raise AssertionError("add_query: theorem %s already exists" % query.query_name)

        if len(query.shows) == 1:
            prop = os_term.list_implies([assume.prop for assume in query.assumes], query.shows[0].prop)
            self.add_theorem(query.query_name, Theorem(query.query_name, query.type_params, query.fixes, prop))

    def get_field_type(self, ty: OSType, field_name: str) -> OSType:
        """Obtain type of the given field of structure or datatype."""
        if isinstance(ty, os_struct.OSStructType):
            struct = self.structs[ty.name]
            return struct.field_map[field_name]
        elif isinstance(ty, os_struct.OSHLevelType) and ty.name in self.datatypes:
            datatype = self.datatypes[ty.name]
            # Note we need to instantiate the types
            tyinst = dict(zip(datatype.params, ty.params))
            return datatype.field_map[field_name].subst(tyinst)
        else:
            raise AssertionError


class TypeCheckException(Exception):
    """Errors in type checking"""
    def __init__(self, msg: str):
        self.msg = msg

    def __str__(self):
        return self.msg

def expand_type(thy: OSTheory, ty: OSType) -> OSType:
    """Expand the given type, all typedefs in ty are unfolded.
    
    Parameters
    ----------
    thy : OSTheory
        current theory
    ty : OSType
        type to be expanded

    Returns
    -------
    OSType
        expanded version of ty, with all typedefs replaced by their definitions.

    """
    if isinstance(ty, (os_struct.OSVoidType, os_struct.OSPrimType, os_struct.OSStructType, os_struct.OSBoundType)):
        return ty
    elif isinstance(ty, os_struct.OSArrayType):
        return os_struct.OSArrayType(expand_type(thy, ty.base_type))
    elif isinstance(ty, os_struct.OSPointerType):
        return os_struct.OSPointerType(expand_type(thy, ty.type))
    elif isinstance(ty, os_struct.OSHLevelType):
        if ty.name in thy.typedefs:
            return expand_type(thy, thy.typedefs[ty.name])
        else:
            return os_struct.OSHLevelType(ty.name, *(expand_type(thy, param) for param in ty.params))
    elif isinstance(ty, os_struct.OSFunctionType):
        return os_struct.OSFunctionType(*([expand_type(thy, arg) for arg in ty.arg_types] + expand_type(thy, ty.ret_type)))
    else:
        raise NotImplementedError("expand_type on %s: %s" % (type(ty), ty))

def equal_type(thy: OSTheory, ty1: OSType, ty2: OSType) -> bool:
    """Check whether two types are equal after calling `expand_type`"""
    return expand_type(thy, ty1) == expand_type(thy, ty2)

def match_type(thy: OSTheory, pat: OSType, ty: OSType, tyinst: Dict[str, OSType]) -> bool:
    """Match two types after expansion.

    Note only schematic type variables are matched. To match on bound
    type variables, call `make_schematic` first.
    
    """
    return expand_type(thy, pat).match(expand_type(thy, ty), tyinst)

def check_type(thy: OSTheory, t: OSTerm,
               ctxt: Dict[str, OSType],
               ty: Optional[OSType] = None) -> Optional[OSType]:
    """Perform type checking on the term, fill in unknown types.
    
    If ty is None, then the type of t is unknown, try to infer the type
    of t and return it as result. If unable to infer type of t, return None.

    If ty is not None, then the type of t is known to be ty. Try to infer
    components of t.

    Parameters
    ----------
    thy : OSTheory
        Current theory information
    t : OSTerm
        Term for type inference and checking
    ctxt : Dict[str, OSType]
        Context containing inferred types of bound variables
    ty : Optional[OSType]
        Existing type of t to be checked. None if not available
    
    Returns
    -------
    Optional[OSType]
        Inferred type of t. None if unable to infer a type.

    """
    # print("check_type: t = %s, ty = %s, ctxt = %s" % (t, ty, ctxt))
    if t.type is not None and ty is not None:
        if not equal_type(thy, ty, t.type):
            raise TypeCheckException("type mismatch for %s. Expected %s, actual %s" % (t, ty, t.type))
    elif t.type is not None and ty is None:
        ty = t.type

    if isinstance(t, os_term.OSWildcard):
        # Wildcard has no assumed type
        if ty is None:
            return None
        else:
            t.type = ty
            return ty
    if isinstance(t, os_term.OSVar):
        if t.is_sch_var():
            # For schematic variables, just use provided type
            if ty is not None and t.type is None:
                t.type = ty
            elif ty is not None and t.type is not None and not equal_type(thy, ty, t.type):
                raise TypeCheckException("type mismatch for %s. Expected %s, actual %s" % (t, ty, t.type))
            return t.type
        else:
            # Lookup type of variables from context
            if t.name not in ctxt:
                raise TypeCheckException("variable %s not found" % t.name)
            t.type = ctxt[t.name]
            if ty is not None and t.type is None:
                ctxt[t.name] = ty
                t.type = ty
            elif ty is not None and t.type is not None and not equal_type(thy, ty, t.type):
                raise TypeCheckException("type mismatch for %s. Expected %s, actual %s" % (t, ty, t.type))
            return t.type
    elif isinstance(t, os_term.OSConst) or isinstance(t, os_term.OSNumber):
        # Constants and numbers can use provided type
        if t.type is None and ty is None:
            return None
        elif t.type is None:
            t.type = ty
            return ty
        elif ty is None:
            return t.type
        elif not equal_type(thy, ty, t.type):
            raise TypeCheckException("type mismatch for %s. Expected %s, actual %s" % (t, ty, t.type))
        else:
            return t.type
    elif isinstance(t, os_term.OSOp):
        if len(t.args) == 1:
            if t.op == '!':
                if ty is not None and ty != os_struct.Bool:
                    raise TypeCheckException("expected boolean type for %s" % t)
                check_type(thy, t.args[0], ctxt, os_struct.Bool)
                t.type = os_struct.Bool
                return os_struct.Bool
            elif t.op == '~':
                if ty is not None:
                    if not os_struct.is_bv_type(ty):
                        raise TypeCheckException("expected bitvector type for %s" % t)
                    check_type(thy, t.args[0], ctxt, ty)
                    t.type = ty
                    return ty
                else:
                    ty0 = check_type(thy, t.args[0], ctxt)
                    if ty0 is None:
                        return None
                    elif not os_struct.is_bv_type(ty0):
                        raise TypeCheckException("expected bitvector type for %s" % t.args[0])
                    else:
                        t.type = ty0
                        return ty0
            else:
                raise AssertionError("unrecognized unary operator %s" % t.op)
        if len(t.args) != 2:
            raise AssertionError("wrong number of arguments for operator %s" % t.op)

        if t.op in ['<<', '>>', '&', '^', '|']:
            # Return type and both arguments are bitvector types
            if ty is not None:
                if not os_struct.is_bv_type(ty):
                    raise TypeCheckException("expected bitvector type for %s" % t)
                check_type(thy, t.args[0], ctxt, ty)
                check_type(thy, t.args[1], ctxt, ty)
                t.type = ty
                return ty
            else:
                ty0 = check_type(thy, t.args[0], ctxt)
                if ty0 is None:
                    ty1 = check_type(thy, t.args[1], ctxt)
                    if ty1 is None:
                        return None
                    else:
                        if not os_struct.is_bv_type(ty1):
                            raise TypeCheckException("expected bitvector type for %s" % t.args[1])
                        t.type = ty1
                        return check_type(thy, t.args[0], ctxt, ty1)
                else:
                    if not os_struct.is_bv_type(ty0):
                        raise TypeCheckException("expected bitvector type for %s" % t.args[0])
                    t.type = ty0
                    return check_type(thy, t.args[1], ctxt, ty0)
        elif t.op in ["+", "-", "*", "/"]:
            # Return type and both arguments are numeric types
            if ty is not None:
                if not os_struct.is_num_type(ty):
                    raise TypeCheckException("expected numeric type for %s" % t)
                check_type(thy, t.args[0], ctxt, ty)
                check_type(thy, t.args[1], ctxt, ty)
                t.type = ty
                return ty
            else:
                ty0 = check_type(thy, t.args[0], ctxt)
                if ty0 is None:
                    ty1 = check_type(thy, t.args[1], ctxt)
                    if ty1 is None:
                        return None
                    else:
                        if not os_struct.is_num_type(ty1):
                            raise TypeCheckException("expected numeric type for %s" % t.args[1])
                        t.type = ty1
                        return check_type(thy, t.args[0], ctxt, ty1)
                else:
                    if not os_struct.is_num_type(ty0):
                        raise TypeCheckException("expected numeric type for %s" % t.args[0])
                    t.type = ty0
                    return check_type(thy, t.args[1], ctxt, ty0)
        elif t.op in ['<', '<=', '>', '>=']:
            # Both arguments are numeric types, return type is bool
            if ty is not None and ty != os_struct.Bool:
                raise TypeCheckException("expected boolean type for %s" % t)
            ty0 = check_type(thy, t.args[0], ctxt)
            if ty0 is None:
                ty1 = check_type(thy, t.args[1], ctxt)
                if ty1 is None:
                    raise TypeCheckException("unable to derive type for %s" % t.args[0])
                else:
                    if not os_struct.is_num_type(ty1):
                        raise TypeCheckException("expected numeric type for %s" % t.args[1])
                    t.type = ty1
                    check_type(thy, t.args[0], ctxt, ty1)
                    return os_struct.Bool
            else:
                if not os_struct.is_num_type(ty0):
                    raise TypeCheckException("expected bitvector type for %s" % t.args[0])
                t.type = ty0
                check_type(thy, t.args[1], ctxt, ty0)
                return os_struct.Bool
        elif t.op in ['&&', '||', '->']:
            # Return type and both arguments are boolean
            if ty is not None and ty != os_struct.Bool:
                raise TypeCheckException("expected boolean type for %s" % t)
            check_type(thy, t.args[0], ctxt, os_struct.Bool)
            check_type(thy, t.args[1], ctxt, os_struct.Bool)
            t.type = os_struct.Bool
            return os_struct.Bool
        elif t.op in ['==', '!=']:
            # Return type is boolean, arguments must have equal type
            if ty is not None and ty != os_struct.Bool:
                raise TypeCheckException("expected boolean type for %s" % t)
            t.type = os_struct.Bool
            ty0 = check_type(thy, t.args[0], ctxt)
            if ty0 is None:
                ty1 = check_type(thy, t.args[1], ctxt)
                if ty1 is None:
                    raise TypeCheckException("unable to derive type for %s" % t.args[0])
                else:
                    check_type(thy, t.args[0], ctxt, ty1)
                    return os_struct.Bool
            else:
                check_type(thy, t.args[1], ctxt, ty0)
                return os_struct.Bool
        else:
            raise AssertionError("unrecognized binary operator %s" % t.op)
    elif isinstance(t, os_term.OSFun):
        if t.func_name == "ite":
            # Special function: if-then-else.
            # The condition must have type bool, type of if-branch, else-branch and
            # return type must be the same.
            assert len(t.args) == 3
            check_type(thy, t.args[0], ctxt, os_struct.Bool)
            if ty is not None:
                check_type(thy, t.args[1], ctxt, ty)
                check_type(thy, t.args[2], ctxt, ty)
                t.type = ty
                return ty
            else:
                ty0 = check_type(thy, t.args[1], ctxt)
                if ty0 is None:
                    ty1 = check_type(thy, t.args[2], ctxt)
                    if ty1 is None:
                        return None
                    else:
                        t.type = ty1
                        return check_type(thy, t.args[1], ctxt, ty1)
                else:
                    t.type = ty0
                    return check_type(thy, t.args[2], ctxt, ty0)
        elif t.func_name == "int":
            # Coersion from bitvector type to integer
            assert len(t.args) == 1
            ty0 = check_type(thy, t.args[0], ctxt)
            if not os_struct.is_bv_type(ty0):
                raise TypeCheckException("%s should have bitvector type" % t.args[0])
            t.type = os_struct.Int
            return t.type
        elif t.func_name == "nat":
            # Coersion from bitvector type to natural number
            assert len(t.args) == 1
            ty0 = check_type(thy, t.args[0], ctxt)
            if not os_struct.is_bv_type(ty0):
                raise TypeCheckException("%s should have bitvector type" % t.args[0])
            t.type = os_struct.Nat
            return t.type
        elif t.func_name == "nth":
            assert len(t.args) == 2
            ty0 = check_type(thy, t.args[0], ctxt)
            if not isinstance(ty0, os_struct.OSArrayType):
                raise TypeCheckException("%s should have array type" % t.args[0])
            ty1 = check_type(thy, t.args[1], ctxt)
            if not os_struct.is_num_type(ty1):
                raise TypeCheckException("%s should have numeric type" % t.args[1])
            t.type = ty0.base_type
            return t.type
        elif t.func_name == "K":
            ty = check_type(thy, t.args[0], ctxt)
            t.type = os_struct.OSArrayType(ty)
            return t.type
        elif t.func_name == "Store":
            assert len(t.args) == 3
            ty0 = check_type(thy, t.args[0], ctxt)
            if not isinstance(ty0, os_struct.OSArrayType):
                raise TypeCheckException("%s should have array type" % t.args[0])
            ty1 = check_type(thy, t.args[1], ctxt)
            if not os_struct.is_num_type(ty1):
                raise TypeCheckException("%s should have numeric type" % t.args[1])
            ty2 = check_type(thy, t.args[2], ctxt)
            if ty0.base_type != ty2:
                raise TypeCheckException("stored value %s should have type %s" % (t.args[2], ty0.base_type))
            t.type = ty0
            return t.type
        elif t.func_name in thy.constr_types or t.func_name in thy.fixps or t.func_name in ctxt or t.func_name in thy.axiom_func:
            if t.func_name in thy.constr_types:
                constr_type = thy.constr_types[t.func_name]
            elif t.func_name in thy.fixps:
                constr_type = thy.fixps[t.func_name].get_func_type()
            elif t.func_name in thy.axiom_func:
                constr_type = thy.axiom_func[t.func_name].type
            else:
                constr_type = ctxt[t.func_name]
            # Change all type variables in constr_type to schematic
            constr_type = constr_type.make_schematic(constr_type.get_vars())
            if isinstance(constr_type, os_struct.OSHLevelType):
                if len(t.args) > 0:
                    raise TypeCheckException("function %s does not take arguments" % t.func_name)
                if ty is None:
                    vars = constr_type.get_vars()
                    if vars:
                        return None  # unable to infer type
                    t.type = constr_type
                else:
                    if not match_type(thy, constr_type, ty, dict()):
                        raise TypeCheckException("type mismatch for %s: expected %s, actual %s" % (t, ty, constr_type))
                    t.type = ty
                return t.type
            elif isinstance(constr_type, os_struct.OSFunctionType):
                if len(t.args) != len(constr_type.arg_types):
                    raise TypeCheckException("check_type on %s: function %s should take %s arguments" % (
                        t, t.func_name, len(constr_type.arg_types)))
                vars = constr_type.get_vars()
                tyinst = dict()
                # First, perform preliminary matching
                for i in range(len(t.args)):
                    param_ty = check_type(thy, t.args[i], ctxt)
                    if param_ty is not None:
                        if not match_type(thy, constr_type.arg_types[i], param_ty, tyinst):
                            raise TypeCheckException("type mismatch on %s: expected %s, actual %s" % (
                                t.args[i], constr_type.arg_types[i], param_ty))
                if ty is not None:
                    if not match_type(thy, constr_type.ret_type, ty, tyinst):
                        raise TypeCheckException("type mismatch: expected %s, actual %s" % (
                            ty, constr_type.ret_type))
                if t.type is not None:
                    if not match_type(thy, constr_type.ret_type, t.type, tyinst):
                        raise TypeCheckException("type mismatch: expected %s, actual %s" % (
                            t.type, constr_type.ret_type))

                # Now we expect all type variables have been instantiated
                if len(vars) != len(tyinst):
                    return None  # unable to infer type

                # Perform a second round of type checking with instantiated types
                for i in range(len(t.args)):
                    check_type(thy, t.args[i], ctxt, constr_type.arg_types[i].subst(tyinst))
                if ty is not None:
                    if not equal_type(thy, ty, constr_type.ret_type.subst(tyinst)):
                        raise TypeCheckException("type mismatch: expected %s, actual %s" % (
                            ty, constr_type.ret_type.subst(tyinst)))
                if t.type is not None:
                    if not equal_type(thy, t.type, constr_type.ret_type.subst(tyinst)):
                        raise TypeCheckException("type mismatch: expected %s, actual %s" % (
                            t.type, constr_type.ret_type.subst(tyinst)))

                t.type = constr_type.ret_type.subst(tyinst)
                return t.type
            else:
                raise AssertionError
        else:
            raise AssertionError("function %s is not found" % t.func_name)
    elif isinstance(t, os_term.FieldGet):
        ty = check_type(thy, t.expr, ctxt)
        if isinstance(ty, os_struct.OSStructType):
            t.type = thy.get_field_type(ty, t.field)
            return t.type
        elif isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.datatypes:
            t.type = thy.get_field_type(ty, t.field)
            return t.type
        else:
            raise AssertionError("%s should have structure or datatype, but get %s" % (t.expr, type(ty)))
    elif isinstance(t, os_term.OSStructUpdate):
        ori_type = check_type(thy, t.ori_expr, ctxt)
        if not isinstance(ori_type, os_struct.OSStructType):
            raise TypeCheckException("%s should have structure type, but get %s" % (t.ori_expr, type(struct_type)))
        t.type = ori_type
        for field_name, expr in t.dict_updates.items():
            check_type(thy, expr, ctxt, thy.get_field_type(ori_type, field_name))
        return t.type
    elif isinstance(t, os_term.OSStructVal):
        struct_type = os_struct.OSStructType(t.struct_name)
        for field_name, expr in t.vals:
            check_type(thy, expr, ctxt, thy.get_field_type(struct_type, field_name))
        return t.type
    elif isinstance(t, os_term.OSLet):
        # First, compute the type of the bound variable, then use it to
        # infer/check type of body. 
        var_ty = check_type(thy, t.expr, ctxt)
        ctxt[t.var_name] = var_ty
        body_ty = check_type(thy, t.rhs, ctxt, ty)
        t.type = body_ty
        del ctxt[t.var_name]
        return t.type
    elif isinstance(t, os_term.OSQuant):
        for param in t.params:
            ctxt[param.name] = param.type
        check_type(thy, t.body, ctxt, os_struct.Bool)
        t.type = os_struct.Bool
        for param in t.params:
            del ctxt[param.name]
        return t.type
    elif isinstance(t, os_term.OSQuantIn):
        ctxt[t.param.name] = t.param.type
        check_type(thy, t.collection, ctxt)
        check_type(thy, t.body, ctxt, os_struct.Bool)
        t.type = os_struct.Bool
        del ctxt[t.param.name]
        return t.type
    elif isinstance(t, os_term.OSSwitch):
        # Check type of term used in switch
        switch_ty = check_type(thy, t.switch_expr, ctxt)

        for branch in t.branches:
            if isinstance(branch, os_term.OSSwitchBranchCase):
                # Obtain types of bound variables
                _, bound_vars = branch.pattern.get_vars()
                for bound_var in bound_vars:
                    ctxt[bound_var.name] = bound_var.type
                check_type(thy, branch.pattern, ctxt, switch_ty)
                # Use type of bound variables to check type of expr
                ty = check_type(thy, branch.expr, ctxt, ty)
                for bound_var in bound_vars:
                    del ctxt[bound_var.name]
            elif isinstance(branch, os_term.OSSwitchBranchDefault):
                # Default case: just check type is correct
                ty = check_type(thy, branch.expr, ctxt, ty)
            else:
                raise AssertionError
        assert ty is not None, "branch.expr = %s" % repr(branch.expr)
        t.type = ty
        return t.type
    else:
        raise NotImplementedError("check_type: %s" % type(t))

def is_standard_switch(thy: OSTheory, t: os_term.OSSwitch) -> bool:
    """Check whether the switch expression is in standard form.
    
    The standard form is a list of constructors with variable parameters,
    followed optionally by a default at the end. If no default is present,
    the list of constructors must be full.
    
    Any switch expression can be simplified into one in standard form
    (using the simplify_switch function).

    """
    ty = expand_type(thy, t.switch_expr.type)
    if not (isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.datatypes):
        return False
    datatype = thy.datatypes[ty.name]

    if len(t.branches) == 0:
        return False

    constrs: Set[str] = set()

    def is_standard_branch(branch: os_term.OSSwitchBranch) -> bool:
        nonlocal constrs
        if not isinstance(branch, os_term.OSSwitchBranchCase):
            return False
        pat = branch.pattern
        if not (isinstance(pat, os_term.OSFun) and
                all(isinstance(arg, (os_term.OSVar, os_term.OSWildcard)) for arg in pat.args)):
            return False
        if pat.func_name in constrs:
            return False
        constrs.add(pat.func_name)
        return True

    if isinstance(t.branches[-1], os_term.OSSwitchBranchDefault):
        return all(is_standard_branch(branch) for branch in t.branches[:-1])    
    else:
        return all(is_standard_branch(branch) for branch in t.branches) and \
            len(t.branches) == len(datatype.branches)

class OSContext:
    """Represents context of the current query."""
    def __init__(self, thy: OSTheory):
        # Associated theory
        self.thy = thy

        # Mapping from variables to their type
        self.var_decls: Dict[str, OSType] = dict()

        # Other bound variables
        self.bound_vars: List[str] = list()

        # Default structure
        self.default_struct: List[str] = list()

        # Temporary label for recursive datatype
        self.datatype_decl: Optional[str] = None

        # Temporary type parameters
        self.type_params: List[str] = list()

    def add_var_decl(self, var_name: str, type: OSType = os_struct.OSVoidType):
        """Add variable declaration"""
        if var_name in self.var_decls:
            raise AssertionError("add_var_decl: variable %s already defined" % var_name)
 
        self.var_decls[var_name] = type

    def lookup_field(self, field_name: str) -> Optional[OSType]:
        """Return type of a field from default structure."""
        if not self.default_struct:
            return None  # no structure is set

        if self.default_struct[-1] not in self.thy.structs:
            raise AssertionError("lookup_field: default structure %s not found in theory" % self.default_struct[-1])

        struct = self.thy.structs[self.default_struct[-1]]
        if field_name not in struct.field_map:
            return None  # field not found

        return struct.field_map[field_name]

class OSImports:
    """Theory import information.
    
    Attributes
    ----------
    imports: Tuple[str]
        List of imported theories.

    """
    def __init__(self, imports: Iterable[str]):
        self.imports = tuple(imports)

    def __str__(self):
        return "imports %s" % (", ".join(self.imports))

    def __repr__(self):
        return "OSImports(%s)" % (", ".join(self.imports))

class OSAttribDecl:
    """Attribute add/delete declaration.
    
    Attributes
    ----------
    operation: str
        indicates direction of operation, one of "add" or "del"
    attrib_name: str
        name of the attribute to add/delete
    th_names: Tuple[str]
        list of theorems to add/delete

    """
    def __init__(self, operation: str, attrib_name: str, th_names: Iterable[str]):
        assert operation in ["add", "del"]
        self.operation = operation
        self.attrib_name = attrib_name
        self.th_names = tuple(th_names)

    def __str__(self):
        return "%s_attrib %s for %s" % (self.operation, self.attrib_name, ", ".join(self.th_names))

    def __repr__(self):
        return "OSAttribDecl(%s, %s, %s)" % (self.operation, self.attrib_name, self.th_names)
