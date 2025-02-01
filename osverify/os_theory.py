"""Theory definitions"""

from typing import Iterable, Optional, TypeGuard

from osverify import os_struct
from osverify import os_term
from osverify import os_fixp
from osverify import os_query
from osverify.os_struct import OSType
from osverify.os_term import OSTerm, OSOp, VarContext, GenField
from osverify.os_util import indent


class Theorem:
    """Represents a proved theorem.
    
    A theorem is given by a list of type parameters, list of parameters,
    and a proposition.

    The input prop is a single statement with free variables, but not
    without schematic variables (any assumptions of the theorem are
    changed to implies beforehand). The schematic version of the theorem
    and the forall version of the theorem are obtained by calling the
    respective methods.
    
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
        """Obtain version of the theorem with forall-quantification.
        
        Parameters
        ----------
        tys: Iterable[OSType]
            list of type parameters, in order to instantiate the type
            variables of the theorem.

        """
        if len(self.type_params) != len(tys):
            raise AssertionError(
                f"get_forall_theorem: expect {len(self.type_params)} type"
                 "parameters for {self.name}.")
        tyinst = dict(zip(self.type_params, tys))
        res = self.prop.subst_type(tyinst)
        params = [param.subst_type(tyinst) for param in self.params]
        if params:
            return os_term.OSQuant("forall", params, res)
        else:
            return res


class OSTheory:
    """Represents the current theory"""
    def __init__(self):
        # List of declarations
        self.decls = []

        # Mapping from structure to their definitions
        self.structs: dict[str, os_struct.Struct] = dict()

        # Mapping from functions to their definition
        self.fixps: dict[str, os_fixp.OSFunction] = dict()

        # Mapping of type alias definitions
        self.typedefs: dict[str, OSType] = dict()

        # Mapping of datatype definitions
        self.datatypes: dict[str, os_struct.Datatype] = dict()

        # Mapping of axiomatic datatype definitions
        self.axiom_types: dict[str, os_struct.AxiomType] = dict()

        # Mapping from constructors to their datatype
        self.constr_datatype: dict[str, str] = dict()

        # Mapping from constructors to their types
        self.constr_types: dict[str, OSType] = dict()

        # Mapping of axiomatic function definitions
        self.axiom_func: dict[str, os_struct.AxiomDef] = dict()

        # Mapping from theorem (query) names to queries
        self.queries: dict[str, os_query.Query] = dict()

        # Mapping from theorem names to statements
        self.theorems: dict[str, Theorem] = dict()

        # List of type parameters for each theorem.
        self.type_params: dict[str, tuple[str]] = dict()

        # Mapping from attributes to list of theorem having that attribute.
        self.attribute_map: dict[str, list[str]] = dict()

        # List of equality theorems used for rewriting
        self.attribute_map["rewrite"] = list()

    def __str__(self):
        res = ""
        for _, ty_def in self.axiom_types.items():
            res += f"{ty_def}\n"
        for _, func_def in self.axiom_func.items():
            res += f"{func_def}\n"
        for name, func_def in self.fixps.items():
            res += f"{name}: {func_def.get_func_type()}\n"
        return res

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
        elif isinstance(fixp.body, os_term.OSSwitch) and \
            fixp.body.switch_expr in fixp.params and \
            is_standard_switch(self, fixp.body):
            # Otherwise, if the function body is switch on one of the input parameters,
            # add 'rewrite' attribute for simplification rules
            switch_id = fixp.params.index(fixp.body.switch_expr)
            for i, branch in enumerate(fixp.body.branches):
                if isinstance(branch, os_term.OSSwitchBranchCase):
                    # Left side: replace the switched variable with the pattern
                    lhs = os_term.OSFun(
                        fixp.name, *(fixp.params[:switch_id] + (branch.pattern,) + fixp.params[switch_id+1:]),
                        type=fixp.ret_type)
                    eq = os_term.eq(lhs, branch.expr)
                    # List of parameters: just get variables from the left side
                    ty_params, params = lhs.get_vars()
                    fixp_simp = fixp.name + "_simps" + str(i+1)
                    self.add_theorem(fixp_simp, Theorem(fixp_simp, ty_params, params, eq))
                    self.attribute_map['rewrite'].append(fixp_simp)
                else:
                    # TODO: add default cases
                    pass

    def get_func_type(self, func_name: str) -> tuple[OSType, tuple[str]]:
        """Obtain the parameterized type of the function.
        
        Functions in the theory are divided into the following classes:
        
        - Fixpoint function, stored in fixps.
        - Axiomatic functions, stored in axiom_func.
        - Constructors of datatypes.
        - Field accessors of structures and datatypes (including .id).

        Returns
        -------
        OSType
            type of the function
        tuple[str]
            ordered list of type parameters in the returned type

        """
        # Fixpoint functions
        if func_name in self.fixps:
            fixp = self.fixps[func_name]
            return fixp.get_func_type(), fixp.type_params

        # Axiomatic functions
        if func_name in self.axiom_func:
            ax_func = self.axiom_func[func_name]
            return ax_func.type, ax_func.type_params

        # Constructor
        if func_name in self.constr_datatype:
            ty_name = self.constr_datatype[func_name]
            datatype = self.datatypes[ty_name]
            branch = datatype.branch_map[func_name]
            branch_tys = [ty for _, ty in branch.params]
            param_tys = [os_struct.OSBoundType(param) for param in datatype.params]
            if len(branch_tys) > 0:
                res_ty = os_struct.OSFunctionType(*(branch_tys + [os_struct.OSHLevelType(ty_name, *param_tys)]))
            else:
                res_ty = os_struct.OSHLevelType(ty_name, *param_tys)
            return res_ty, datatype.params

        dot_pos = func_name.find(".")
        # Field of a structure or datatype
        if dot_pos != -1:
            ty_name = func_name[:dot_pos]
            if ty_name in self.structs:
                # Field of a structure
                struct = self.structs[ty_name]
                field = func_name[dot_pos+1:]
                assert field in struct.field_map, \
                    "get_func_type: field %s not found in structure %s" % (field, ty_name)
                res_ty = os_struct.OSFunctionType(os_struct.OSStructType(ty_name), struct.field_map[field])
                return res_ty, tuple()

            if ty_name in self.datatypes:
                # Field of datatype
                datatype = self.datatypes[ty_name]
                field = func_name[dot_pos+1:]
                param_tys = [os_struct.OSBoundType(param) for param in datatype.params]
                if field == "id":
                    res_ty = os_struct.OSFunctionType(os_struct.OSHLevelType(ty_name, *param_tys), os_struct.Int)
                else:
                    assert field in datatype.field_map, \
                        "get_func_type: field %s not found in structure %s" % (field, ty_name)
                    res_ty = os_struct.OSFunctionType(os_struct.OSHLevelType(ty_name, *param_tys), datatype.field_map[field])
                return res_ty, datatype.params

        raise AssertionError("get_func_type: %s" % func_name)

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
        return name in self.typedefs or name in self.datatypes or name in self.axiom_types

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
        """Obtain type of the given field of structure or datatype.
        
        This function automatically instantiates the type parameters according
        to the input type.

        Parameters
        ----------
        ty: OSType
            type of the overall term, either structure type or datatype
        field_name: str
            name of the field to query for
        
        """
        if isinstance(ty, os_struct.OSStructType):
            struct = self.structs[ty.name]
            if field_name not in struct.field_map:
                raise AssertionError(
                    "get_field_type: field %s not found in structure %s" % (field_name, ty.name))
            return struct.field_map[field_name]
        elif isinstance(ty, os_struct.OSHLevelType) and ty.name in self.datatypes:
            datatype = self.datatypes[ty.name]
            # Note we need to instantiate the types
            tyinst = dict(zip(datatype.params, ty.params))
            if field_name == "id":
                return os_struct.Int
            elif field_name not in datatype.field_map:
                raise AssertionError(
                    "get_field_type: field %s not found in datatype %s" % (field_name, ty.name))
            return datatype.field_map[field_name].subst(tyinst)
        else:
            raise NotImplementedError(f"get_field_type: try to get field {field_name} from {ty}")


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
    if isinstance(ty, (os_struct.OSPrimType, os_struct.OSStructType, os_struct.OSBoundType)):
        return ty
    elif isinstance(ty, os_struct.OSHLevelType):
        if ty.name in thy.typedefs:
            return expand_type(thy, thy.typedefs[ty.name])
        else:
            return os_struct.OSHLevelType(ty.name, *(expand_type(thy, param) for param in ty.params))
    elif isinstance(ty, os_struct.OSFunctionType):
        return os_struct.OSFunctionType(
            *([expand_type(thy, arg) for arg in ty.arg_types] + [expand_type(thy, ty.ret_type)]))
    else:
        raise NotImplementedError("expand_type on %s: %s" % (type(ty), ty))

def check_type_gen_field(thy: OSTheory, base_ty: OSType,
                         gen_field: GenField,
                         ctxt: VarContext,
                         ty: Optional[OSType] = None) -> Optional[OSType]:
    """Perform type checking on a generalized field, fill in unknown types.
    
    Meaning of parameters is similar to `check_type`.

    """
    # print("check_type_gen_field: base_ty = %s, gen_field = %s, ty = %s, ctxt = %s" % (base_ty, gen_field, ty, ctxt))
    if gen_field.type is not None and ty is not None:
        if ty != gen_field.type:
            raise TypeCheckException(
                f"type mismatch for {gen_field}. Expected {ty}, actual {gen_field.type}")
    elif gen_field.type is not None and ty is None:
        ty = gen_field.type

    if isinstance(gen_field, os_term.AtomGenField):
        gen_field.type = thy.get_field_type(base_ty, gen_field.name)
        return gen_field.type
    elif isinstance(gen_field, os_term.IndexGenField):
        base_ty = check_type_gen_field(thy, base_ty, gen_field.base, ctxt)
        if isinstance(base_ty, os_struct.OSHLevelType) and base_ty.name == "Map":
            key_ty, val_ty = base_ty.params
            check_type(thy, gen_field.index, ctxt, key_ty)
            gen_field.type = val_ty
            return val_ty
        elif isinstance(base_ty, os_struct.OSHLevelType) and base_ty.name == "Seq":
            ele_ty = base_ty.params[0]
            check_type(thy, gen_field.index, ctxt, os_struct.Int)
            gen_field.type = ele_ty
            return ele_ty
        else:
            raise TypeCheckException("expected Map or Seq type, found %s" % base_ty)
    elif isinstance(gen_field, os_term.FieldGetGenField):
        base_ty = check_type_gen_field(thy, base_ty, gen_field.base, ctxt)
        gen_field.type = thy.get_field_type(base_ty, gen_field.field)
        return gen_field.type
    else:
        raise NotImplementedError("check_type_gen_field: %s" % type(gen_field))

def check_type(thy: OSTheory, t: OSTerm,
               ctxt: VarContext,
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
    ctxt : VarContext
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
        if ty != t.type:
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
            elif ty is not None and t.type is not None and ty != t.type:
                raise TypeCheckException(f"type mismatch for {t}. Expected {ty}, actual {t.type}")
            return t.type
        else:
            # Lookup type of variables from context
            if not ctxt.contains_var(t.name):
                raise TypeCheckException(f"variable {t.name} not found")
            t.type = ctxt.get_var_type(t.name)
            if ty is not None and t.type is None:
                ctxt.update_var_decl(t.name, ty)
                t.type = ty
            if ty is not None and ty != t.type:
                raise TypeCheckException(f"type mismatch for {t}. Expected {ty}, actual {t.type}")
            return t.type
    elif isinstance(t, os_term.OSNumber):
        # Numbers can use provided type
        if ty is not None:
            if os_struct.is_num_type(ty) and isinstance(t.val, bool):
                raise TypeCheckException(f"type mismatch for {t}. Expected {ty}, actual bool")
            if ty == os_struct.Bool and not (t == os_term.true or t == os_term.false):
                raise TypeCheckException(f"type mismatch for {t}. Expected bool, actual numeric type")
        if t.type is None and ty is None:
            return None
        elif t.type is None:
            t.type = ty
            return ty
        elif ty is None:
            return t.type
        elif ty != t.type:
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
            elif t.op == '-':
                if ty is not None and not os_struct.is_num_type(ty):
                    raise TypeCheckException("expected number type for %s" % t)
                check_type(thy, t.args[0], ctxt, ty)
                t.type = ty
                return ty
            else:
                raise AssertionError("unrecognized unary operator %s" % t.op)
        if len(t.args) != 2:
            raise AssertionError("wrong number of arguments for operator %s" % t.op)

        if t.op in ['<<', '>>', '&', '^', '|']:
            # Return type and both arguments are bitvector types
            if ty is not None:
                if not os_struct.is_bv_type(ty):
                    raise TypeCheckException("%s: expected bitvector type for %s" % (t.op, t))
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
                            raise TypeCheckException("%s: expected bitvector type for %s" % (t.op, t.args[1]))
                        t.type = ty1
                        return check_type(thy, t.args[0], ctxt, ty1)
                else:
                    if not os_struct.is_bv_type(ty0):
                        raise TypeCheckException("%s: expected bitvector type for %s" % (t.op, t.args[0]))
                    t.type = ty0
                    return check_type(thy, t.args[1], ctxt, ty0)
        elif t.op in ["+", "-", "*", "/", "%", "**"]:
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
                    t.type = os_struct.Bool
                    check_type(thy, t.args[0], ctxt, ty1)
                    return os_struct.Bool
            else:
                if not os_struct.is_num_type(ty0):
                    raise TypeCheckException("expected bitvector type for %s" % t.args[0])
                t.type = os_struct.Bool
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
        if t.func_name == "default":
            # Special case: default value
            if t.type is None and ty is None:
                return None
            elif t.type is None:
                t.type = ty
                return ty
            elif ty is None:
                return t.type
            elif ty != t.type:
                raise TypeCheckException("type mismatch for %s. Expected %s, actual %s" % (t, ty, t.type))
            else:
                return t.type
        elif t.func_name == "ite":
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
                raise TypeCheckException(f"{t.args[0]} in {t} should have bitvector type")
            if ty is not None and ty != os_struct.Int:
                raise TypeCheckException(f"{t} should have integer type")
            t.type = os_struct.Int
            return t.type
        elif t.func_name == "int32u":
            # Coersion from integer to bitvector type
            assert len(t.args) == 1
            check_type(thy, t.args[0], ctxt, os_struct.Int)
            if ty is not None and ty != os_struct.Int32U:
                raise TypeCheckException(f"{t} should have int32u type")
            t.type = os_struct.Int32U
            return t.type
        elif t.func_name == "int16u":
            # Coersion from integer to bitvector type
            assert len(t.args) == 1
            check_type(thy, t.args[0], ctxt, os_struct.Int)
            if ty is not None and ty != os_struct.Int16U:
                raise TypeCheckException(f"{t} should have int16u type")
            t.type = os_struct.Int16U
            return t.type
        elif t.func_name == "int8u":
            # Coersion from integer to bitvector type
            assert len(t.args) == 1
            check_type(thy, t.args[0], ctxt, os_struct.Int)
            if ty is not None and ty != os_struct.Int8U:
                raise TypeCheckException(f"{t} should have int8u type")
            t.type = os_struct.Int8U
            return t.type
        elif t.func_name in thy.constr_types or t.func_name in thy.fixps or \
             ctxt.contains_var(t.func_name) or t.func_name in thy.axiom_func:
            if t.func_name in thy.constr_types:
                constr_type = thy.constr_types[t.func_name]
            elif t.func_name in thy.fixps:
                constr_type = thy.fixps[t.func_name].get_func_type()
            elif t.func_name in thy.axiom_func:
                constr_type = thy.axiom_func[t.func_name].type
            else:
                constr_type = ctxt.get_var_type(t.func_name)
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
                    if not constr_type.match(ty, dict()):
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
                        if not constr_type.arg_types[i].match(param_ty, tyinst):
                            raise TypeCheckException("type mismatch on %s: expected %s, actual %s" % (
                                t.args[i], constr_type.arg_types[i].subst(tyinst), param_ty))
                if ty is not None:
                    if not constr_type.ret_type.match(ty, tyinst):
                        raise TypeCheckException("type mismatch: expected %s, actual %s" % (
                            ty, constr_type.ret_type.subst(tyinst)))
                if t.type is not None:
                    if not constr_type.ret_type.match(t.type, tyinst):
                        raise TypeCheckException("type mismatch: expected %s, actual %s" % (
                            t.type, constr_type.ret_type.subst(tyinst)))

                # Now we expect all type variables have been instantiated
                if len(vars) != len(tyinst):
                    return None  # unable to infer type

                # Perform a second round of type checking with instantiated types
                for i in range(len(t.args)):
                    check_type(thy, t.args[i], ctxt, constr_type.arg_types[i].subst(tyinst))
                if ty is not None:
                    if ty != constr_type.ret_type.subst(tyinst):
                        raise TypeCheckException("type mismatch: expected %s, actual %s" % (
                            ty, constr_type.ret_type.subst(tyinst)))
                if t.type is not None:
                    if t.type != constr_type.ret_type.subst(tyinst):
                        raise TypeCheckException("type mismatch: expected %s, actual %s" % (
                            t.type, constr_type.ret_type.subst(tyinst)))

                t.type = constr_type.ret_type.subst(tyinst)
                return t.type
            else:
                if len(t.args) > 0:
                    raise TypeCheckException("function %s does not take arguments" % t.func_name)
                if ty is None:
                    t.type = constr_type
                else:
                    if constr_type != ty:
                        raise TypeCheckException("type mismatch for %s: expected %s, actual %s" % (t, ty, constr_type))
                    t.type = ty
                return t.type
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
            raise TypeCheckException("%s should have structure type, but get %s" % (t.ori_expr, type(ori_type)))
        t.type = ori_type
        for field_name, expr in t.dict_updates.items():
            check_type(thy, expr, ctxt, thy.get_field_type(ori_type, field_name))
        return t.type
    elif isinstance(t, os_term.OSStructUpdateGen):
        ori_type = check_type(thy, t.ori_expr, ctxt)
        if not isinstance(ori_type, os_struct.OSStructType):
            raise TypeCheckException("%s should have structure type, but get %s" % (t.ori_expr, type(ori_type)))
        t.type = ori_type
        expr_type = check_type_gen_field(thy, ori_type, t.gen_field, ctxt, t.expr.type)
        check_type(thy, t.expr, ctxt, expr_type)
        return t.type
    elif isinstance(t, os_term.OSStructVal):
        struct_type = os_struct.OSStructType(t.struct_name)
        for field_name, expr in t.vals:
            check_type(thy, expr, ctxt, thy.get_field_type(struct_type, field_name))
        return t.type
    elif isinstance(t, os_term.SeqLiteral):
        if ty is None:
            if len(t.exprs) == 0:
                return None
            expr_type = None
            for expr in t.exprs:
                expr_type = check_type(thy, expr, ctxt, None)
                if expr_type is not None:
                    break
            if expr_type is None:
                return None
            for expr in t.exprs:
                check_type(thy, expr, ctxt, expr_type)
            t.type = os_struct.SeqType(expr_type)
            return t.type
        else:
            if not os_struct.is_seq_type(ty):
                raise TypeCheckException(f"{t} should have sequence type, get {ty}")
            ele_ty = ty.params[0]
            for expr in t.exprs:
                check_type(thy, expr, ctxt, ele_ty)
            t.type = ty
            return t.type
    elif isinstance(t, os_term.OSLet):
        # First, compute the type of the bound variable, then use it to
        # infer/check type of body. 
        var_ty = check_type(thy, t.expr, ctxt)
        ctxt.add_var_decl(t.var_name, var_ty)
        body_ty = check_type(thy, t.body, ctxt, ty)
        t.type = body_ty
        ctxt.del_var_decl(t.var_name)
        return t.type
    elif isinstance(t, os_term.OSQuant):
        for param in t.params:
            ctxt.add_var_decl(param.name, param.type)
        check_type(thy, t.body, ctxt, os_struct.Bool)
        t.type = os_struct.Bool
        for param in t.params:
            ctxt.del_var_decl(param.name)
        return t.type
    elif isinstance(t, os_term.OSQuantIn):
        check_type(thy, t.collection, ctxt)
        if os_struct.is_seq_type(t.collection.type):
            val_ty = t.collection.type.params[0]
            if val_ty != t.param.type:
                raise TypeCheckException(
                    f"expected value type {t.param.type} for {t.collection}, actual {val_ty}")
        elif os_struct.is_map_type(t.collection.type):
            key_ty = t.collection.type.params[0]
            if key_ty != t.param.type:
                raise TypeCheckException(
                    f"expected key type {t.param.type} for {t.collection}, actual {key_ty}")

        ctxt.add_var_decl(t.param.name, t.param.type)
        check_type(thy, t.body, ctxt, os_struct.Bool)
        t.type = os_struct.Bool
        ctxt.del_var_decl(t.param.name)
        return t.type
    elif isinstance(t, os_term.OSSwitch):
        # Check type of term used in switch
        switch_ty = check_type(thy, t.switch_expr, ctxt)

        for branch in t.branches:
            if isinstance(branch, os_term.OSSwitchBranchCase):
                # Obtain types of bound variables
                _, bound_vars = branch.pattern.get_vars()
                for bound_var in bound_vars:
                    ctxt.add_var_decl(bound_var.name, bound_var.type)
                check_type(thy, branch.pattern, ctxt, switch_ty)
                # Use type of bound variables to check type of expr
                ty = check_type(thy, branch.expr, ctxt, ty)
                for bound_var in bound_vars:
                    ctxt.del_var_decl(bound_var.name)
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
    (using `normalize_switch`).

    """
    ty = t.switch_expr.type
    if not (isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.datatypes):
        return False
    datatype = thy.datatypes[ty.name]

    if len(t.branches) == 0:
        return False

    constrs: set[str] = set()

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

def is_defining_eq(thy: OSTheory, t: OSTerm) -> TypeGuard[OSOp]:
    """Return whether `t` is a defining equation.
    
    A defining equation is used for rewriting the remaining parts of
    the proof state. It does not need to be translated for SMT solving.

    """
    if not (os_term.is_eq(t) and os_term.is_atomic_term(t.lhs)):
        return False

    _, indices = os_term.dest_atomic_term(t.lhs)
    if len(indices) > 0:
        return False

    ty = t.lhs.type
    return os_struct.is_map_type(ty) or os_struct.is_seq_type(ty) or \
        isinstance(ty, os_struct.OSStructType) or \
        (isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.datatypes)

class OSContext:
    """Represents context of the current query."""
    def __init__(self, thy: OSTheory, var_ctxt: VarContext):
        # Associated theory
        self.thy = thy

        # Variable context
        self.var_ctxt = var_ctxt

        # List of equalities
        self._eqs: list[OSTerm] = list()

        # List of disequalities
        self._diseqs: list[OSTerm] = list()

    def __str__(self):
        res = "context {\n"
        for type_param in self.var_ctxt.type_params:
            res += indent("type %s;" % type_param, 2) + '\n'
        for var in self.var_ctxt.data:
            res += indent("fixes %s: %s;" % (var.name, var.type), 2) + '\n'
        if self._eqs:
            res += indent("eqs: %s" % ', '.join(str(eq) for eq in self._eqs), 2) + '\n'
        if self._diseqs:
            res += indent("diseqs: %s" % ', '.join(str(eq) for eq in self._diseqs), 2) + '\n'
        res += "}"
        return res

    def add_var_decl(self, var_name: str, var_type: OSType):
        """Add variable declaration.""" 
        self.var_ctxt.add_var_decl(var_name, var_type)

    def del_var_decl(self, var_name: str):
        """Remove variable declaration."""
        self.var_ctxt.del_var_decl(var_name)
    
    def variant_var(self, var: os_term.OSVar) -> os_term.OSVar:
        """Obtain variant of the given variable."""
        return self.var_ctxt.variant_var(var)

    def variant_vars(self, vars: Iterable[os_term.OSVar]) -> list[os_term.OSVar]:
        """Obtain variants of a list of variables."""
        return self.var_ctxt.variant_vars(vars)

    def process_fact(self, fact: OSTerm):
        """Process the given fact for the context."""
        if os_term.is_eq(fact):
            self.add_equality(fact)
        elif os_term.is_diseq(fact):
            self.add_disequality(fact)
        else:
            pass

    def add_equality(self, eq: OSTerm):
        """Add given equality to the context."""
        if not os_term.is_eq(eq):
            raise AssertionError("add_equality: input term is not an equality")
        
        self._eqs.append(eq)

    def add_disequality(self, diseq: OSTerm):
        """Add given disequality to the context."""
        if not os_term.is_diseq(diseq):
            raise AssertionError("add_disequality: input term is not a disequality")

        self._diseqs.append(diseq)

    def check_equality(self, s: OSTerm, t: OSTerm) -> bool:
        """Determine whether s == t can be derived from this context.
        
        Currently we only perform basic checking. Algorithm based
        on congruence closure is to be implemented later.

        """
        if s == t:
            return True
        for eq in self._eqs:
            if s == os_term.lhs(eq) and t == os_term.rhs(eq):
                return True
            if s == os_term.rhs(eq) and t == os_term.lhs(eq):
                return True
        return False

    def check_disequality(self, s: OSTerm, t: OSTerm) -> bool:
        """Determine whether s != t can be derived from this context.
        
        Currently we only perform basic checking. Algorithm based
        on congruence closure is to be implemented later.

        """
        for diseq in self._diseqs:
            if s == os_term.lhs(diseq) and t == os_term.rhs(diseq):
                return True
            if s == os_term.rhs(diseq) and t == os_term.lhs(diseq):
                return True
        return False


class OSImports:
    """Theory import information.
    
    Attributes
    ----------
    imports: tuple[str]
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
    th_names: tuple[str]
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
