import importlib

from typing import Dict, List, Optional, Iterable, Tuple
from osverify import os_struct
from osverify import os_term
from osverify import os_query
from osverify import os_theory
from osverify.os_struct import OSType
from osverify.os_term import OSTerm
from osverify import os_model
from osverify import os_simplify

if importlib.util.find_spec("z3"):
    import z3
    z3_loaded = True
    z3.set_param(proof=True)
else:
    z3_loaded = False

class Z3Exception(Exception):
    def __init__(self, err):
        self.err = err

    def __str__(self):
        return self.err

class Z3ConvertContext:
    """Context of Z3 conversion.
    
    Attributes
    ----------
    c_idx : int
        index of the next temporary variable
    temp_var_map : Dict[str, OSType]
        mapping from temporary variables to their types
    visited : Dict[OSTerm, z3.Z3PPObject]
        mapping from visited terms to their translations, constraints
        are not repeatedly produced for visited terms.
    constraints : List[z3.Z3PPObject]
        list of additional constraints

    """
    def __init__(self):
        self.c_idx = 0
        self.temp_var_map: Dict[str, OSType] = dict()
        self.visited: Dict[OSTerm, z3.Z3PPObject] = dict()
        self.constraints: List[z3.Z3PPObject] = list()

    def get_temp_var(self, ty: OSType) -> str:
        """Obtain next temporary variable with the given type."""
        res = "_c" + str(self.c_idx)
        self.c_idx += 1
        self.temp_var_map[res] = ty
        return res
    
    def get_temp_var_for_term(self, t: OSTerm) -> os_term.OSVar:
        """Obtain temporary variable representing the term."""
        var_name = self.get_temp_var(t)
        return os_term.OSVar(var_name, type=t.type)
    
    def add_constraint(self, constraint: z3.Z3PPObject):
        assert isinstance(constraint, z3.Z3PPObject)
        self.constraints.append(constraint)


def get_Z3type(thy: os_theory.OSTheory, ty: OSType):
    """Convert OSType to Z3 type.
    

    Parameters
    ----------
    thy : OSTheory
        the current theory.
    ty : OSType
        type to be converted.

    """
    if isinstance(ty, os_struct.OSVoidType):
        raise NotImplementedError
    elif isinstance(ty, os_struct.OSPrimType):
        if ty == os_struct.Bool:
            return z3.BoolSort()
        elif ty == os_struct.Int:
            return z3.IntSort()
        elif ty == os_struct.Int8U:
            return z3.BitVecSort(sz=8)
        elif ty == os_struct.Int16U:
            return z3.BitVecSort(sz=16)
        elif ty == os_struct.Int32U:
            return z3.BitVecSort(sz=32)
        else:
            raise NotImplementedError
    elif isinstance(ty, os_struct.OSArrayType):
        return z3.ArraySort(z3.IntSort(), get_Z3type(thy, ty.base_type))
    elif isinstance(ty, os_struct.OSHLevelType):
        if ty.name in thy.typedefs:
            return get_Z3type(thy, thy.typedefs[ty.name])
        elif ty.name in thy.structs:
            raise AssertionError("get_Z3type: attempt to convert struct type %s" % ty.name)
        elif ty.name in thy.datatypes or ty.name in thy.axiom_types:
            if len(ty.params) > 0:
                return z3.DeclareSort("%s<%s>" % (ty.name, ",".join(str(param) for param in ty.params)))
            else:
                return z3.DeclareSort(ty.name)
        else:
            raise AssertionError("get_Z3type: high-level type %s not found" % ty.name)
    elif isinstance(ty, os_struct.OSPointerType):
        return z3.BitVecSort(sz=32)
    elif isinstance(ty, os_struct.OSBoundType):
        return z3.DeclareSort(ty.name)
    elif isinstance(ty, os_struct.OSStructType):
        return z3.DeclareSort(ty.name)
    else:
        raise NotImplementedError("ty = %s, type = %s" % (ty, type(ty)))

def convert_var(t: OSTerm, thy: os_theory.OSTheory) -> z3.Z3PPObject:
    """Convert a OSVar to Z3 variable."""
    if not isinstance(t, os_term.OSVar):
        raise AssertionError("convert_var: %s is not a variable" % t)
    z3_ty = get_Z3type(thy, t.type)
    return z3.Const(t.name, z3_ty)
    
def convert_val(thy: os_theory.OSTheory, t: OSTerm):
    """Convert a OSConst to Z3 value."""
    if not isinstance(t, os_term.OSConst):
        raise AssertionError("convert_val: %s is not a constant" % t)

    val = thy.const_val[t.name]
    ty = t.type
    return z3.BitVecVal(val, get_Z3type(thy, ty))

def convert_number(t: OSTerm, thy: os_theory.OSTheory):
    """Convert a number to a Z3 value."""
    if not isinstance(t, os_term.OSNumber):
        raise AssertionError("convert_number: %s is not a number" % t)
    
    if t.type == os_struct.Bool:
        return z3.BoolVal(t.val)
    elif t.type == os_struct.Int:
        return z3.IntVal(t.val)
    elif os_struct.is_bv_type(t.type):
        return z3.BitVecVal(t.val, get_Z3type(thy, t.type))
    else:
        raise AssertionError("convert_number: unexpected type %s" % t)
    
def convert_ufunc(func_name: str, args: Iterable[OSTerm],
                  ty: OSType, thy: os_theory.OSTheory, ctxt: Z3ConvertContext) -> z3.Z3PPObject:
    """Convert to uninterpreted function call.
    
    This is used for converting actual function calls, as well as
    access to fields of structures and datatypes. Hence we accept
    function name, args, ty separately rather than as a single term.

    """
    # If function has no arguments, convert to Z3 constant
    if len(args) == 0:
        return z3.Const(func_name, get_Z3type(thy, ty))

    # Otherwise, convert to application of Z3 function
    args_type_list = [get_Z3type(thy, arg.type) for arg in args]
    args_list = [convert(thy, arg, ctxt) for arg in args]
    z3_func = z3.Function(func_name, *args_type_list, get_Z3type(thy, ty))
    return z3_func(args_list)

def convert_field_get(t: OSTerm, field: str,
                      thy: os_theory.OSTheory, ctxt: Z3ConvertContext) -> z3.Z3PPObject:
    """Convert field of a structure expression.
    
    The following cases are considered:

    - for explicit structure values, just convert the corresponding field.

    - for structure updates, check if the field exists in the update, if so
      use the updated value. Otherwise convert using the original structure.

    - in other cases, convert to uninterpreted function call.

    """
    ty = os_theory.expand_type(thy, t.type)
    if isinstance(ty, os_struct.OSStructType) and ty.name in thy.structs:
        # Other cases of structure
        field_ty = thy.get_field_type(ty, field)
        return convert_ufunc(ty.name + "." + field, [t], field_ty, thy, ctxt)
    elif isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.datatypes:
        # Datatype case
        datatype = thy.datatypes[ty.name]
        if isinstance(t, os_term.OSFun) and t.func_name in datatype.branch_map:
            field_id = datatype.get_field_id(t.func_name, field)
            return convert(thy, t.args[field_id], ctxt)
        else:
            field_ty = thy.get_field_type(ty, field)
            return convert_ufunc(ty.name + "." + field, [t], field_ty, thy, ctxt)
    else:
        raise AssertionError("convert_field_get: unknown type %s for structure" % t.type)

def convert_id(t: OSTerm,
               thy: os_theory.OSTheory, ctxt: Z3ConvertContext) -> z3.Z3PPObject:
    """Convert access to id of datatype expression.
    
    If t is a constructor, directly simplify to the corresponding value.
    Otherwise just apply id function.

    """
    ty = os_theory.expand_type(thy, t.type)
    if not (isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.datatypes):
        raise AssertionError("convert_id: unknown type %s" % ty)
    datatype = thy.datatypes[ty.name]
    if isinstance(t, os_term.OSFun) and t.func_name in datatype.branch_map:
        return z3.IntVal(datatype.get_branch_id(t.func_name))
    else:
        return convert_ufunc(ty.name + ".id", [t], os_struct.Int, thy, ctxt)

def convert_equality(t1: OSTerm, t2: OSTerm,
                     thy: os_theory.OSTheory, ctxt: Z3ConvertContext, *, recurse=False):
    """Convert equality of t1 and t2 into Z3 constraints.
    
    We consider the following cases:

    - if t1 and t2 are values of datatypes, convert into equality on ids
      and fields.

    - if t1 and t2 are structure values, convert into equality on each field.

    - otherwise, just perform the normal conversion.

    """
    constraints = []

    ty = os_theory.expand_type(thy, t1.type)
    if ty != os_theory.expand_type(thy, t2.type):
        raise AssertionError("convert_equality: input terms have unequal type.")
    
    res = convert(thy, t1, ctxt) == convert(thy, t2, ctxt)

    if isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.datatypes:
        # Datatype case
        datatype = thy.datatypes[ty.name]

        # Add constraint that id should be equal
        t1_id = convert_id(t1, thy, ctxt)
        t2_id = convert_id(t2, thy, ctxt)
        constraints.append(t1_id == t2_id)

        # Check whether id of at least one side of equality is known
        known_id = None
        if isinstance(t1, os_term.OSFun) and t1.func_name in datatype.branch_map:
            known_id = datatype.get_branch_id(t1.func_name)
        elif isinstance(t2, os_term.OSFun) and t2.func_name in datatype.branch_map:
            known_id = datatype.get_branch_id(t2.func_name)

        if isinstance(t1, os_term.OSFun) and t1.func_name in datatype.branch_map and \
           isinstance(t2, os_term.OSFun) and t2.func_name in datatype.branch_map:
            if t1.func_name != t2.func_name:
                constraints.append(z3.BoolVal(False))
            else:
                known_id = datatype.get_branch_id(t1.func_name)
                branch = datatype.branches[known_id]
                for i, (param_name, _) in enumerate(branch.params):
                    field_ty = thy.get_field_type(ty, param_name)
                    constraints.append(convert_equality(t1.args[i], t2.args[i], thy, ctxt))
            # print("Case 1: convert %s == %s into %s" % (t1, t2, z3.And(*constraints)))
        elif isinstance(t1, os_term.OSFun) and t1.func_name in datatype.branch_map:
            known_id = datatype.get_branch_id(t1.func_name)            
            branch = datatype.branches[known_id]
            for i, (param_name, _) in enumerate(branch.params):
                field_ty = thy.get_field_type(ty, param_name)
                constraints.append(convert_equality(
                    t1.args[i], os_term.FieldGet(t2, param_name, type=field_ty), thy, ctxt))
            # print("Case 2: convert %s == %s into %s" % (t1, t2, z3.And(*constraints)))
        elif isinstance(t2, os_term.OSFun) and t2.func_name in datatype.branch_map:
            known_id = datatype.get_branch_id(t2.func_name)
            branch = datatype.branches[known_id]
            for i, (param_name, _) in enumerate(branch.params):
                field_ty = thy.get_field_type(ty, param_name)
                constraints.append(convert_equality(
                    os_term.FieldGet(t1, param_name, type=field_ty), t2.args[i], thy, ctxt))
            # print("Case 3: convert %s == %s into %s" % (t1, t2, z3.And(*constraints)))
        elif not recurse:
            # No side has known id
            for i, branch in enumerate(datatype.branches):
                eqs = []
                for param_name, _ in branch.params:
                    field_ty = thy.get_field_type(ty, param_name)
                    eqs.append(convert_equality(
                        os_term.FieldGet(t1, param_name, type=field_ty),
                        os_term.FieldGet(t2, param_name, type=field_ty),
                        thy, ctxt, recurse=True))
                if len(eqs) == 1:
                    constraints.append(z3.Implies(t1_id == i, eqs[0]))
                elif len(eqs) > 1:
                    constraints.append(z3.Implies(t1_id == i, z3.And(*eqs)))
            # print("Case 4: convert %s == %s into %s" % (t1, t2, z3.And(*constraints)))
        ctxt.add_constraint(res == z3.And(*constraints))

    elif isinstance(ty, os_struct.OSStructType) and ty.name in thy.structs:
        # Structure case
        struct = thy.structs[ty.name]

        # Each field of the structure must be equal
        for field in struct.fields:
            field_ty = thy.get_field_type(ty, field.field_name)
            constraints.append(convert_equality(
                os_term.FieldGet(t1, field.field_name, type=field_ty),
                os_term.FieldGet(t2, field.field_name, type=field_ty),
                thy, ctxt
            ))
        ctxt.add_constraint(res == z3.And(*constraints))

        # t1 = os_term.OSVar("t1", type=ty)
        # t2 = os_term.OSVar("t2", type=ty)
        # z3_t1, z3_t2 = convert_var(t1, thy), convert_var(t2, thy)
        # constraints = []
        # for field in struct.fields:
        #     field_ty = thy.get_field_type(ty, field.field_name)
        #     constraints.append(
        #         convert(thy, os_term.FieldGet(t1, field.field_name, type=field_ty), ctxt) ==
        #         convert(thy, os_term.FieldGet(t2, field.field_name, type=field_ty), ctxt)
        #     )
        # constraint = (z3.ForAll([z3_t1, z3_t2], (z3_t1 == z3_t2) == z3.And(*constraints)))
        # print(constraint)
        # ctxt.add_constraint(constraint)

    elif isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.axiom_types:
        # print("convert_equality on Map:", t1, t2)
        t = os_term.OSFun("mapEq", t1, t2, type=os_struct.Bool)
        ctxt.add_constraint(res == convert(thy, os_simplify.rewrite_thm(thy, "mapEq_def", t), ctxt))

    return res

def convert(thy: os_theory.OSTheory, t: OSTerm,
            ctxt: Z3ConvertContext) -> z3.Z3PPObject:
    """Convert OSTerm to z3 term.
    
    Parameters
    ----------
    thy : OSTheory
        The current theory
    t : OSTerm
        OS term to be converted
    ctxt : Z3ConvertContext
        Context of Z3 conversion
    """
    if t in ctxt.visited:
        return ctxt.visited[t]

    res: z3.Z3PPObject
    if isinstance(t, os_term.OSConst):
        res = convert_val(thy, t)
    elif isinstance(t, os_term.OSNumber):
        res = convert_number(t, thy)
    elif isinstance(t, os_term.OSVar):
        res = convert_var(t, thy)
    elif isinstance(t, os_term.OSOp):
        if len(t.args) == 1:
            a = convert(thy, t.args[0], ctxt)
            if t.op == '!':
                res = z3.Not(a)
            elif t.op == '~':
                res = ~a
            else:
                raise NotImplementedError
        else:
            assert len(t.args) == 2
            # The case of equalities is special.
            if t.op == "==":
                res = convert_equality(t.args[0], t.args[1], thy, ctxt)
            elif t.op == "!=":
                res = z3.Not(convert_equality(t.args[0], t.args[1], thy, ctxt))
            else:
                # Now consider the case of other operators
                a, b = convert(thy, t.args[0], ctxt), convert(thy, t.args[1], ctxt)
                if t.op == "->":
                    res = z3.Implies(a, b)
                elif t.op == "||":
                    res = z3.Or(a, b)
                elif t.op == "&&":
                    res = z3.And(a, b)
                elif t.op == "<=":
                    if isinstance(a, z3.IntNumRef) or isinstance(b, z3.IntNumRef):
                        res = a <= b
                    else:
                        res = z3.ULE(a, b)
                elif t.op == "<":
                    if isinstance(a, z3.IntNumRef) or isinstance(b, z3.IntNumRef):
                        res = a < b
                    else:
                        res = z3.ULT(a, b)
                elif t.op == ">=":
                    if isinstance(a, z3.IntNumRef) or isinstance(b, z3.IntNumRef):
                        res = a >= b
                    else:
                        res = z3.UGE(a, b)
                elif t.op == ">":
                    if isinstance(a, z3.IntNumRef) or isinstance(b, z3.IntNumRef):
                        res = a > b
                    else:
                        res = z3.UGT(a, b)
                elif t.op == "+":
                    res = a + b
                elif t.op == "-":
                    res = a - b
                elif t.op == "*":
                    res = a * b
                elif t.op == "/":
                    res = z3.UDiv(a, b)
                elif t.op == "&":
                    res = z3.BitVecRef.__and__(a, b)
                elif t.op == ">>":
                    res = z3.LShR(a, b)
                elif t.op == "<<":
                    res = a << b
                elif t.op == "|":
                    res = z3.BitVecRef.__or__(a, b)
                elif t.op == "^":
                    res = z3.BitVecRef.__xor__(a, b)
                else:
                    raise NotImplementedError("convert on op")
    elif isinstance(t, os_term.OSFun):
        if t.func_name == "ite":
            # If-then-else statement 
            assert len(t.args) == 3
            cond, t1, t2 = [convert(thy, arg, ctxt) for arg in t.args]
            res = z3.If(cond, t1, t2)
        elif t.func_name == 'nth':
            # Array indexing
            assert len(t.args) == 2
            a, b = convert(thy, t.args[0], ctxt), convert(thy, t.args[1], ctxt)
            res = a[z3.BV2Int(b)]
        elif t.func_name == 'Store':
            # Array update
            assert len(t.args) == 3
            a, b, c = convert(thy, t.args[0], ctxt), convert(thy, t.args[1], ctxt), \
                      convert(thy, t.args[2], ctxt)
            res = z3.Store(a, z3.BV2Int(b), c)
        elif t.func_name in ('isEmpty', 'subseteq', 'join', 'remove',
                             'disjoint', 'merge', 'minus', 'disjUnion', 'mapUpdate'):
            res = convert(thy, os_simplify.rewrite_thm(thy, t.func_name + "_def", t), ctxt)
        else:
            res = convert_ufunc(t.func_name, t.args, t.type, thy, ctxt)
    elif isinstance(t, os_term.OSLet):
        t2 = t.rhs.subst({t.var_name: t.expr})
        res = convert(thy, t2, ctxt)
    elif isinstance(t, os_term.FieldGet):
        if t.field == "id":
            # Special: access ID of datatype
            res = convert_id(t.expr, thy, ctxt)
        else:
            # Usual case
            res = convert_field_get(t.expr, t.field, thy, ctxt)
    elif isinstance(t, os_term.OSQuant):
        var_quant_list = [convert_var(param, thy) for param in t.params]
        func = convert(thy, t.body, ctxt)
        if t.quantifier == "forall":
            # if os_term.is_eq(t.body):
            #     pattern = convert(thy, t.body.args[0], ctxt)
            #     # print("pattern", pattern)
            #     res = z3.ForAll(var_quant_list, func, patterns=[pattern])
            # else:
            res = z3.ForAll(var_quant_list, func)
        elif t.quantifier == "exists":
            res = z3.Exists(var_quant_list, func)
        else:
            raise NotImplementedError
    elif isinstance(t, os_term.OSQuantIn):
        # Simplify it into OSQuant
        ty = os_theory.expand_type(thy, t.collection.type)
        if os_struct.isMapType(ty):
            if t.quantifier == "forall":
                simp_t = os_term.OSQuant(
                    "forall", [t.param],
                    os_term.implies(os_term.indom(t.param, t.collection), t.body)
                )
            elif t.quantifier == "exists":
                simp_t = os_term.OSQuant(
                    "exists", [t.param],
                    os_term.conj(os_term.indom(t.param, t.collection), t.body)
                )
            else:
                raise NotImplementedError
            return convert(thy, simp_t, ctxt)
        elif os_struct.isListType(ty):
            if t.quantifier == "forall":
                simp_t = os_term.OSQuant(
                    "forall", [t.param],
                    os_term.implies(os_term.inlist(t.param, t.collection), t.body)
                )
            elif t.quantifier == "exists":
                simp_t = os_term.OSQuant(
                    "exists", [t.param],
                    os_term.conj(os_term.inlist(t.param, t.collection), t.body)
                )
            else:
                raise NotImplementedError
            return convert(thy, simp_t, ctxt)
        else:
            raise NotImplementedError("convert: %s (collection type %s)" % (t, t.collection.type))
    elif isinstance(t, os_term.OSStructVal):
        # Create new term with constraints
        var_t = ctxt.get_temp_var_for_term(t)
        # print("create variable %s for %s" % (var_t, t))

        # Add constraints for that term
        ty = os_theory.expand_type(thy, t.type)
        assert isinstance(ty, os_struct.OSStructType) and ty.name in thy.structs
        struct = thy.structs[ty.name]

        for field in struct.field_map:
            field_ty = thy.get_field_type(ty, field)
            if field in t.dict_vals:
                constraint = os_term.eq(os_term.FieldGet(var_t, field, type=field_ty),
                                        t.dict_vals[field])
            ctxt.add_constraint(convert(thy, constraint, ctxt))
        res = convert_var(var_t, thy)
    elif isinstance(t, os_term.OSStructUpdate):
        # Create new term with constraints
        var_t = ctxt.get_temp_var_for_term(t)
        # print("create variable %s for %s" % (var_t, t))
        
        # Add constraints for that term
        ty = os_theory.expand_type(thy, t.type)
        assert isinstance(ty, os_struct.OSStructType) and ty.name in thy.structs
        struct = thy.structs[ty.name]

        for field in struct.field_map:
            field_ty = thy.get_field_type(ty, field)
            if field in t.dict_updates:
                constraint = os_term.eq(os_term.FieldGet(var_t, field, type=field_ty),
                                        t.dict_updates[field])
            else:
                constraint = os_term.eq(os_term.FieldGet(var_t, field, type=field_ty),
                                        os_term.FieldGet(t.ori_expr, field, type=field_ty))
            ctxt.add_constraint(convert(thy, constraint, ctxt))
        res = convert_var(var_t, thy)
    elif isinstance(t, os_term.OSSwitch):
        # Convert switch expression into if-then-else statements
        ty = os_theory.expand_type(thy, t.switch_expr.type)
        if not (isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.datatypes):
            raise AssertionError("convert: switch expression has unexpected type %s" % ty)
        datatype = thy.datatypes[ty.name]
        
        if not os_theory.is_standard_switch(thy, t):
            raise AssertionError("convert: switch term %s not in standard form" % t)

        # The conversion is different for the boolean case
        is_bool = (t.type == os_struct.Bool)

        # Each branch of switch is converted to a condition, the last one
        # is always the default case
        if_branches: List[Tuple[OSTerm, OSTerm]] = list()
        else_branch: OSTerm
        for branch in t.branches[:-1]:
            assert isinstance(branch, os_term.OSSwitchBranchCase)
            assert isinstance(branch.pattern, os_term.OSFun)
            constr_name = branch.pattern.func_name
            assert constr_name in datatype.branch_map
            datatype_branch = datatype.branch_map[constr_name]
            inst: Dict[str, OSTerm] = dict()
            for (param_name, _), arg in zip(datatype_branch.params, branch.pattern.args):
                assert isinstance(arg, os_term.OSVar)
                field_ty = thy.get_field_type(ty, param_name)
                inst[arg.name] = os_term.FieldGet(t.switch_expr, param_name, type=field_ty)
            branch_id = datatype.get_branch_id(constr_name)
            new_expr = branch.expr.subst(inst)
            if is_bool:
                # In the boolean case, simply translate to cond -> new_expr
                cond = os_term.eq(os_term.FieldGet(t.switch_expr, "id", type=os_struct.Int),
                                  os_term.integer(branch_id))
                if_branches.append((cond, new_expr))
            else:
                # Otherwise, add new conditions
                raise NotImplementedError
        if isinstance(t.branches[-1], os_term.OSSwitchBranchDefault):
            else_branch = t.branches[-1].expr
        else:
            raise NotImplementedError
        
        # Finally, form the entire if-then-else expression
        res = convert(thy, else_branch, ctxt)
        for cond, expr in reversed(if_branches):
            res = z3.If(convert(thy, cond, ctxt), convert(thy, expr, ctxt), res)
    else:
        raise NotImplementedError("t = %s, type = %s" % (t, type(t)))

    ctxt.visited[t] = res

    ty = os_theory.expand_type(thy, t.type)
    if isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.datatypes:
        datatype = thy.datatypes[ty.name]

        id_t = os_term.FieldGet(t, "id", type=os_struct.Int)
        if isinstance(t, os_term.OSFun) and t.func_name in datatype.branch_map:
            known_id = datatype.get_branch_id(t.func_name)
            ctxt.add_constraint(convert(
                thy, os_term.eq(id_t, os_term.integer(known_id)), ctxt))
        else:
            # Constraint on id: for datatypes, the id of the datatype is in
            # the range [0, n), where n is the number of branches.
            ctxt.add_constraint(convert(
                thy, os_term.greater_eq(id_t, os_term.integer(0)), ctxt))
            ctxt.add_constraint(convert(
                thy, os_term.less(id_t, os_term.integer(len(datatype.branches))), ctxt))

    return res

class SolveResult:
    """Base class for Z3 solve results."""
    pass

class UnsatResult(SolveResult):
    """Unsat result."""
    def __init__(self):
        pass

    def __str__(self):
        "unsat"

class ModelResult(SolveResult):
    """Sat result with model."""
    def __init__(self, model: os_model.Model):
        self.model = model

def solve(thy: os_theory.OSTheory,
          assumes: Iterable[OSTerm], concl: OSTerm, *,
          thm_spec: Iterable[os_theory.TheoremSpec] = tuple(),
          verbose: bool = False) -> SolveResult:
    """Solve the given goal using Z3.
    
    If the goal is unsatisfiable, return the string "unsat".
    Otherwise, return the model provided by Z3.

    Parameters
    ----------
    thy : OSTheory
        The current theory
    vars : Iterable[OSVar]
        List of variables
    assumes : Iterable[OSTerm]
        List of assumptions
    concl : OSTerm
        Goal to be proved
    thms : Iterable[str], optional
        List of existing theorems that may be used
    verbose : bool, default is False
        Whether to print additional information

    Returns
    -------
    SolveResult
        If the query can be proved, return UnsatResult. Otherwise return a model
        that serves as counterexample to the query.

    """
    s = z3.Solver()

    # Add existing theorems
    for spec in thm_spec:
        if not spec.thm_name in thy.theorems:
            raise AssertionError("solve: theorem %s not found" % spec.thm_name)
        prop = thy.get_forall_theorem(spec.thm_name, spec.tys)
        if verbose:
            print("use theorem:", prop)
        z3_t = convert(thy, prop, Z3ConvertContext()) 
        # print(z3_t)
        s.add(z3_t)

    # Conversion context used for transforming assumption and goal
    ctxt = Z3ConvertContext()

    # Add each assumption
    for assume in assumes:
        simplify_t = os_simplify.simplify(thy, assume)
        if verbose:
            print('assume (after simp):', simplify_t)
        # print(simplify_t)
        z3_t = convert(thy, simplify_t, ctxt)
        # print(z3_t)
        s.add(z3_t)

    # Add conclusion
    simplify_t = os_simplify.simplify(thy, concl)
    if verbose:
        print('show (after simp):', simplify_t)
    # print(simplify_t)
    z3_t = convert(thy, simplify_t, ctxt)
    # print(z3_t)
    s.add(z3.Not(z3_t))

    # Add constraints
    for constraint in ctxt.constraints:
        s.add(constraint)

    # Solve using z3, return either unsat or the model
    ret = s.check()
    if str(ret) == 'unsat':
        return UnsatResult()
    else:
        return ModelResult(s.model())

def solve_query(thy: os_theory.OSTheory, query: os_query.Query, *,
                thm_spec: Iterable[os_theory.TheoremSpec] = tuple(),
                verbose: bool = False):
    """Solve the given query, return whether the query can be proved."""
    assumes = [assume.prop for assume in query.assumes]
    assert len(query.shows) == 1
    res = solve(thy, assumes, query.shows[0].prop, thm_spec=thm_spec, verbose=verbose)
    if isinstance(res, UnsatResult):
        return True
    elif isinstance(res, ModelResult):
        return False
    else:
        raise NotImplementedError

def solve_model(thy: os_theory.OSTheory, query: os_query.Query, *,
                verbose: bool = False):
    """Solve a list of constraints for a model."""
    assumes = [assume.prop for assume in query.assumes]
    assert len(query.shows) == 0
    res = solve(thy, assumes, os_term.false, verbose=verbose)
    if isinstance(res, UnsatResult):
        raise AssertionError("solve_model: constraints are unsatisfiable")
    elif isinstance(res, ModelResult):
        if verbose:
            print('---- Raw model ----')
            print(res.model)
        model = convert_model(thy, query.fixes, res.model)
        return model
    else:
        raise NotImplementedError


def convert_z3_expr(z3_t: Optional[z3.Z3PPObject]) -> Optional[OSTerm]:
    """Convert the Z3 expression to OS expressions"""
    if z3_t is None:
        return None

    if not isinstance(z3_t, z3.Z3PPObject):
        raise AssertionError("convert_z3_expr on %s, type %s" % (z3_t, type(z3_t)))

    if isinstance(z3_t, z3.BitVecNumRef):
        sz = z3_t.size()
        ty = None
        if sz == 8:
            ty = os_struct.Int8U
        elif sz == 16:
            ty = os_struct.Int16U
        elif sz == 32:
            ty = os_struct.Int32U
        else:
            raise NotImplementedError
        return os_term.OSNumber(z3_t.as_long(), ty)
    elif isinstance(z3_t, z3.IntNumRef):
        return os_term.OSNumber(z3_t.as_long(), os_struct.Int)
    elif isinstance(z3_t, z3.BoolRef):
        if z3.is_true(z3_t):
            return os_term.OSNumber(True)
        elif z3.is_false(z3_t):
            return os_term.OSNumber(False)
        else:
            raise AssertionError
    elif isinstance(z3_t, z3.ArrayRef):
        if z3.is_K(z3_t):
            return os_term.OSFun("K", convert_z3_expr(z3_t.children()[0]))
        elif z3.is_store(z3_t):
            a, k, v = z3_t.children()
            return os_term.OSFun("Store", convert_z3_expr(a), convert_z3_expr(k), convert_z3_expr(v))
        else:
            raise NotImplementedError("convert_z3_expr on %s, type %s" % (z3_t, type(z3_t)))
    elif isinstance(z3_t, z3.BitVecRef):
        raise AssertionError
    else:
        raise NotImplementedError("convert_z3_expr on %s, type %s" % (z3_t, type(z3_t)))

def get_func_eval(func: z3.FuncInterp, key: z3.Z3PPObject) -> z3.Z3PPObject:
    """Return evaluation of Z3 function."""
    if func.arity() != 1:
        raise NotImplementedError("get_func_eval: arity %d" % func.arity())
    for i in range(func.num_entries()):
        cur_key, cur_val = func.entry(i).arg_value(0), func.entry(i).value()
        if key == cur_key:
            return cur_val
    return func.else_value()

def get_model_for_val(thy: os_theory.OSTheory,
                      model: z3.ModelRef,
                      model_map: Dict[str, z3.Z3PPObject],
                      type_map: Dict[str, OSType],
                      z3_val: z3.Z3PPObject,
                      ty: OSType) -> Optional[OSTerm]:
    """Obtain the model value for the given variable and type.
    
    Parameters
    ----------
    thy : OSTheory
        the current theory
    model : z3.ModelRef
        Z3 model to be converted
    model_map : Dict[str, z3.Z3PPObject]
        mapping from variable name to value in the model
    type_map : Dict[str, OSType]
        mapping from variable to type
    z3_val : z3.Z3PPObject
        Z3 value to be converted
    ty : OSType
        target type of the Z3 value to be converted
    
    """
    # print("converting %s, %s" % (z3_val, ty))
    if isinstance(ty, os_struct.OSPrimType):
        return convert_z3_expr(z3_val)
    elif isinstance(ty, os_struct.OSArrayType):
        return convert_z3_expr(z3_val)
    elif isinstance(ty, os_struct.OSPointerType):
        return convert_z3_expr(z3_val)
    elif isinstance(ty, os_struct.OSStructType):
        struct = thy.structs[ty.name]
        struct_vals = list()
        for field in struct.fields:
            func_name = ty.name + "." + field.field_name
            # It is possible that values for some fields are missing in the z3 model.
            field_type = os_theory.expand_type(thy, field.type)
            if func_name in model_map:
                func = model_map[func_name]
                if func is not None:
                    val = get_func_eval(func, z3_val)
                    if val is not None:
                        struct_vals.append((
                            field.field_name,
                            get_model_for_val(thy, model, model_map, type_map, val, field_type)))
        return os_term.OSStructVal(ty.name, struct_vals)
    elif isinstance(ty, os_struct.OSHLevelType):
        if ty.name in thy.datatypes:
            datatype = thy.datatypes[ty.name]
            # First obtain the ID of the constructor
            id_func = model_map[ty.name + ".id"]
            if id_func is None:
                return None
            id_val = get_func_eval(id_func, z3_val)
            assert isinstance(id_val, z3.IntNumRef)
            id = id_val.as_long()

            # Next, create the appropriate constructor
            assert id in range(len(datatype.branches))
            branch = datatype.branches[id]
            args = list()
            for param_name, _ in branch.params:
                field_ty = thy.get_field_type(ty, param_name)
                func_name = ty.name + "." + param_name
                func = model_map[func_name]
                if func is not None:
                    val = get_func_eval(func, z3_val)
                    if val is None:
                        return None
                    args.append(get_model_for_val(thy, model, model_map, type_map, val, field_ty))
            return os_term.OSFun(branch.constr_name, *args, type=ty)
        elif ty.name in thy.typedefs:
            return get_model_for_val(thy, model, model_map, type_map, z3_val, thy.typedefs[ty.name])
        elif ty.name == "Map":
            key_ty, value_ty = ty.params
            values: List[Tuple[OSTerm, OSTerm]] = list()
            for var, var_ty in type_map.items():
                if var_ty == key_ty:
                    key_val = model_map[var]
                    indom_f = z3.Function("indom", get_Z3type(thy, key_ty), get_Z3type(thy, ty), get_Z3type(thy, os_struct.Bool))
                    indom_t = indom_f([key_val, z3_val])
                    indom_val = model.eval(indom_t)
                    assert z3.is_true(indom_val) or z3.is_false(indom_val)
                    if z3.is_false(indom_val):
                        continue
                    get_f = z3.Function("get", get_Z3type(thy, key_ty), get_Z3type(thy, ty), get_Z3type(thy, value_ty))
                    get_t = get_f([key_val, z3_val])
                    get_val = model.eval(get_t)
                    values.append((get_model_for_val(thy, model, model_map, type_map, key_val, key_ty),
                                   get_model_for_val(thy, model, model_map, type_map, get_val, value_ty)))
            return os_term.list_map(key_ty, value_ty, *values)
        else:
            raise NotImplementedError
    elif isinstance(ty, os_struct.OSBoundType):
        assert isinstance(z3_val, z3.ExprRef)
        return os_term.OSVar(z3_val.decl().name(), type=ty)
    elif isinstance(ty, os_struct.OSFunctionType):
        # TODO: get model for uninterpreted functions
        return None
    else:
        raise NotImplementedError("get_model_for_val for type %s" % ty)

def convert_model(thy: os_theory.OSTheory,
                  vars: Iterable[os_term.OSVar],
                  model: z3.ModelRef) -> os_query.Model:
    """Convert a Z3 model to a more readable form.
    
    Parameters
    ----------
    thy : OSTheory
        The current theory
    vars : Iterable[OSVar]
        List of variables, the function will try to find assignment of
        each variable in the list.
    model : z3.ModelRef
        The original Z3 model.

    """
    res = os_query.Model()

    # Mapping from variable name to value in the model
    model_map: Dict[str, z3.Z3PPObject] = dict()
    for decl in model.decls():
        assert isinstance(decl, z3.FuncDeclRef)
        model_map[decl.name()] = model[decl]

    # Mapping from variable name to type
    type_map: Dict[str, OSType] = dict()
    for var in vars:
        type_map[var.name] = os_theory.expand_type(thy, var.type)

    for var in vars:
        name, ty = var.name, os_theory.expand_type(thy, var.type)
        if name in model_map:
            z3_val = model_map[name]
            val = get_model_for_val(thy, model, model_map, type_map, z3_val, ty)
            if val is not None:
                assert isinstance(val, OSTerm), "val: %s, type: %s" % (val, type(val))
                val.assert_type_checked()
            res.data[name] = val
    return res
