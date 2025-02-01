import importlib

from typing import Iterable
from osverify import os_struct
from osverify import os_term
from osverify import os_theory
from osverify.os_theory import OSTheory
from osverify.os_struct import OSType
from osverify.os_term import OSTerm
from osverify import os_simplify
from osverify.os_proofstate import ProofState

if importlib.util.find_spec("z3"):
    import z3
    z3_loaded = True
    z3.set_param(proof=True)
else:
    z3_loaded = False

class Z3ConvertError(Exception):
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
    temp_var_map : dict[str, OSType]
        mapping from temporary variables to their types
    visited : dict[OSTerm, z3.Z3PPObject]
        mapping from visited terms to their translations, constraints
        are not repeatedly produced for visited terms.
    constraints : list[z3.Z3PPObject]
        list of additional constraints

    """
    def __init__(self):
        self.c_idx = 0
        self.temp_var_map: dict[str, OSType] = dict()
        self.visited: dict[OSTerm, z3.Z3PPObject] = dict()
        self.constraints: list[z3.Z3PPObject] = list()

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


def get_z3_name(name: str, tys: Iterable[OSType]) -> str:
    """Obtain z3 name for the given name and type parameters."""
    if len(tys) == 0:
        return name
    else:
        return "%s<%s>" % (name, ",".join(str(ty) for ty in tys))

def get_Z3type(thy: OSTheory, ty: OSType):
    """Convert OSType to Z3 type.

    Parameters
    ----------
    thy : OSTheory
        the current theory.
    ty : OSType
        type to be converted.

    """
    if isinstance(ty, os_struct.OSPrimType):
        if ty == os_struct.Bool:
            return z3.BoolSort()
        elif ty == os_struct.Int:
            return z3.IntSort()
        elif ty == os_struct.Int8U or ty == os_struct.Int8:
            return z3.BitVecSort(sz=8)
        elif ty == os_struct.Int16U or ty == os_struct.Int16:
            return z3.BitVecSort(sz=16)
        elif ty == os_struct.Int32U or ty == os_struct.Int32:
            return z3.BitVecSort(sz=32)
        elif ty == os_struct.Int64U or ty == os_struct.Int64:
            return z3.BitVecSort(sz=32)
        else:
            raise NotImplementedError
    elif isinstance(ty, os_struct.OSHLevelType):
        if ty.name in thy.typedefs:
            return get_Z3type(thy, thy.typedefs[ty.name])
        elif ty.name in thy.datatypes or ty.name in thy.axiom_types:
            return z3.DeclareSort(get_z3_name(ty.name, ty.params))
        else:
            raise AssertionError("get_Z3type: high-level type %s not found" % ty.name)
    elif isinstance(ty, os_struct.OSBoundType):
        return z3.DeclareSort(ty.name)
    elif isinstance(ty, os_struct.OSStructType):
        return z3.DeclareSort(ty.name)
    else:
        raise NotImplementedError("ty = %s, type = %s" % (ty, type(ty)))

def convert_var(t: OSTerm, thy: OSTheory) -> z3.Z3PPObject:
    """Convert a OSVar to Z3 variable."""
    if not isinstance(t, os_term.OSVar):
        raise AssertionError("convert_var: %s is not a variable" % t)
    z3_ty = get_Z3type(thy, t.type)
    return z3.Const(t.name, z3_ty)

def convert_number(t: OSTerm, thy: OSTheory):
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
        raise AssertionError("convert_number: unexpected type %s for %s" % (t.type, t))

def convert_ufunc(func_name: str, args: Iterable[OSTerm],
                  ty: OSType, thy: OSTheory, ctxt: Z3ConvertContext) -> z3.Z3PPObject:
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

def convert_equality(t1: OSTerm, t2: OSTerm,
                     thy: OSTheory, ctxt: Z3ConvertContext):
    """Convert equality of t1 and t2 into Z3 constraints.
    
    We consider the following cases:

    - if t1 and t2 are values of datatypes, convert into equality on ids
      and fields.

    - if t1 and t2 are structure values, convert into equality on each field.

    - otherwise, just perform the normal conversion.

    """
    constraints = []

    ty = t1.type
    if ty != t2.type:
        print("When converting %s == %s" % (t1, t2))
        print("t1.type = %s" % t1.type)
        print("t2.type = %s" % t2.type)
        raise AssertionError("convert_equality: input terms have unequal type.")

    if isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.datatypes:
        raise AssertionError(f"convert_equality on datatype: {t1} == {t2}")

    elif isinstance(ty, os_struct.OSStructType) and ty.name in thy.structs:
        raise AssertionError(f"convert_equality on Struct: {t1} == {t2}")

    elif isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.axiom_types:
        if ty.name == "Map":
            raise AssertionError(f"convert_equality on Map: {t1} == {t2}")
        elif ty.name == "Seq":
            raise AssertionError(f"convert_equality on Seq: {t1} == {t2}")

    elif isinstance(ty, os_struct.OSPrimType):
        constraints.append(convert(thy, t1, ctxt) == convert(thy, t2, ctxt))

    elif isinstance(ty, os_struct.OSBoundType):
        constraints.append(convert(thy, t1, ctxt) == convert(thy, t2, ctxt))

    else:
        raise AssertionError(f"convert_equality: type {ty}")

    if len(constraints) == 1:
        return constraints[0]
    else:
        return z3.And(*constraints)

def convert(thy: OSTheory, t: OSTerm,
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
    if os_term.is_atomic_term(t):
        name, indices = os_term.dest_atomic_term(t)
        res = convert_ufunc(name, indices, t.type, thy, ctxt)
        if isinstance(t, os_term.FieldGet) and t.field == "id":
            # Constraint on id: for datatypes, the id of the datatype is in
            # the range [0, n), where n is the number of branches.
            data_ty = t.expr.type
            assert isinstance(data_ty, os_struct.OSHLevelType) and data_ty.name in thy.datatypes
            datatype = thy.datatypes[data_ty.name]
            ctxt.add_constraint(res >= 0)
            ctxt.add_constraint(res < len(datatype.branches))
        elif os_term.is_fun(t, "seq_length"):
            # Constraint on length: length of any sequence is non-negative
            ctxt.add_constraint(res >= 0)
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
            elif t.op == '-':
                res = -a
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
                if t.args[0].type != t.args[1].type:
                    raise AssertionError(
                        f"convert on {t}: {t.args[0]} has type {t.args[0].type} and "
                        f"{t.args[1]} has type {t.args[1].type}"
                    )
                a, b = convert(thy, t.args[0], ctxt), convert(thy, t.args[1], ctxt)
                if t.op == "->":
                    res = z3.Implies(a, b)
                elif t.op == "||":
                    res = z3.Or(a, b)
                elif t.op == "&&":
                    res = z3.And(a, b)
                elif t.op == "<=":
                    if os_struct.is_unsigned_bv_type(t.args[0].type):
                        res = z3.ULE(a, b)
                    else:
                        res = a <= b
                elif t.op == "<":
                    if os_struct.is_unsigned_bv_type(t.args[0].type):
                        res = z3.ULT(a, b)
                    else:
                        res = a < b
                elif t.op == ">=":
                    if os_struct.is_unsigned_bv_type(t.args[0].type):
                        res = z3.UGE(a, b)
                    else:
                        res = a >= b
                elif t.op == ">":
                    if os_struct.is_unsigned_bv_type(t.args[0].type):
                        res = z3.UGT(a, b)
                    else:
                        res = a > b
                elif t.op == "**":
                    res = z3.ToInt(z3.ArithRef.__pow__(a, b))
                elif t.op == "+":
                    res = a + b
                elif t.op == "-":
                    res = a - b
                elif t.op == "*":
                    res = a * b
                elif t.op == "/":
                    if os_struct.is_bv_type(t.args[0].type):
                        res = z3.UDiv(a, b)
                    else:
                        res = z3.ArithRef.__div__(a, b)
                elif t.op == '%':
                    if os_struct.is_bv_type(t.args[0].type):
                        res = a % b
                    else:
                        res = z3.ArithRef.__mod__(a, b)
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
        elif t.func_name == "max":
            assert t.args[0].type == os_struct.Int
            t1, t2 = [convert(thy, arg, ctxt) for arg in t.args]
            res = z3.If(t1 >= t2, t1, t2)
        elif t.func_name == "min":
            assert t.args[0].type == os_struct.Int
            t1, t2 = [convert(thy, arg, ctxt) for arg in t.args]
            res = z3.If(t1 <= t2, t1, t2)
        elif t.func_name == "int":
            return z3.BV2Int(convert(thy, t.args[0], ctxt))
        elif t.func_name == "int8u":
            return z3.Int2BV(convert(thy, t.args[0], ctxt), 8)
        elif t.func_name == "int16u":
            return z3.Int2BV(convert(thy, t.args[0], ctxt), 16)
        elif t.func_name == "int32u":
            return z3.Int2BV(convert(thy, t.args[0], ctxt), 32)
        elif t.func_name == "int64u":
            return z3.Int2BV(convert(thy, t.args[0], ctxt), 64)
        elif t.func_name == "seq_length":
            raise AssertionError(f"seq_length on non-atomic term: {t.args[0]}")
        elif t.func_name == "seq_index":
            raise AssertionError(f"seq_index on non-atomic term: {t.args[1]}")
        elif t.func_name == "get":
            raise AssertionError(f"map get on non-atomic term: {t.args[1]}")
        elif t.func_name == "indom":
            raise AssertionError(f"map indom on non-atomic term: {t.args[1]}")
        elif t.func_name in thy.constr_datatype:
            res = convert_ufunc(t.func_name, t.args, t.type, thy, ctxt)
        elif t.func_name in thy.axiom_func:
            res = convert_ufunc(t.func_name, t.args, t.type, thy, ctxt)
        elif t.func_name == "default":
            res = convert_ufunc(t.func_name, t.args, t.type, thy, ctxt)
        else:
            raise AssertionError(f"convert: function {t.func_name}")
    elif isinstance(t, os_term.OSLet):
        raise AssertionError("convert: should not be called on OSLet")
    elif isinstance(t, os_term.FieldGet):
        raise AssertionError(f"convert: should not be called on FieldGet {t}")
    elif isinstance(t, os_term.OSQuant):
        raise AssertionError(f"convert: should not be called on OSQuant {t}")
    elif isinstance(t, os_term.OSQuantIn):
        raise AssertionError("convert: should not be called on OSQuantIn")
    elif isinstance(t, os_term.OSStructVal):
        raise AssertionError("convert: should not be called on OSStructVal")
    elif isinstance(t, os_term.OSStructUpdate):
        raise AssertionError("convert: should not be called on OSStructUpdate")
    elif isinstance(t, os_term.OSSwitch):
        raise AssertionError("convert: should not be called on OSSwitch")
    else:
        raise NotImplementedError("t = %s, type = %s" % (t, type(t)))

    # Record the current term as visited.
    ctxt.visited[t] = res
    return res

class SolveResult:
    """Base class for Z3 solve results."""
    pass

class UnsatResult(SolveResult):
    """Unsat result."""
    def __init__(self):
        pass

    def __str__(self):
        return "unsat"

class SatResult(SolveResult):
    """Sat result."""
    def __init__(self):
        pass

    def __str__(self):
        return "sat"

class ModelResult(SolveResult):
    """Sat result with model.
    
    Returning a ModelResult usually indicates a (potentially spurious)
    counterexample is found. In this case, the convert context is
    recorded to help debug the counterexample.
    
    """
    def __init__(self, z3_model: z3.ModelRef, convert_ctxt: Z3ConvertContext):
        self.z3_model = z3_model
        self.convert_ctxt = convert_ctxt

    def __str__(self):
        return "sat"
    
class SMTException(Exception):
    """Exception indicating SMT solving has failed."""
    def __init__(self, z3_model: z3.ModelRef, state, convert_ctxt: Z3ConvertContext):
        self.z3_model = z3_model
        self.state = state
        self.convert_ctxt = convert_ctxt

    def __str__(self):
        return "Z3 is unable to solve query"

def solve_impl(thy: OSTheory, assumes: Iterable[OSTerm], concl: OSTerm) -> SolveResult:
    """Solve the given goal using Z3.

    Parameters
    ----------
    thy: OSTheory
        current theory
    assumes: Iterable[OSTerm]
        the list of assumptions
    concl: OSTerm
        the goal to prove

    Returns
    -------
    SolveResult
        If the query can be proved, return UnsatResult. Otherwise return a model
        that serves as counterexample to the query.

    """
    s = z3.Solver()

    # Conversion context used for transforming assumption and goal
    convert_ctxt = Z3ConvertContext()

    # Add each assumption
    for assume in assumes:
        z3_t = convert(thy, assume, convert_ctxt)
        # print(z3_t)
        s.add(z3_t)

    # Add conclusion
    z3_t = convert(thy, concl, convert_ctxt)
    # print(z3_t)
    s.add(z3.Not(z3_t))

    # Add constraints
    for constraint in convert_ctxt.constraints:
        s.add(constraint)

    # Solve using z3, return either unsat or the model
    ret = s.check()
    if str(ret) == 'unsat':
        return UnsatResult()
    else:
        return ModelResult(s.model(), convert_ctxt)

def simplify_state(thy: OSTheory, state: ProofState) -> tuple[list[OSTerm], list[OSTerm], OSTerm]:
    """Perform standard simplifications on a state.

    First, split the assumptions in the state into defining equations
    (`define_eqs`) and other assumptions. The other assumptions are then
    simplified using the defining equations. Further simplifications
    are performed on update of sequences and maps.

    Returns
    -------
    define_eq: list[OSTerm]
        list of defining equations
    assumes: list[OSTerm]
        list of (simplified) assumptions
    concl: OSTerm
        (simplified) goal

    """
    var_ctxt = state.get_var_context()
    define_eqs = []

    # Collect rewrite rules that are defining equations
    for assume in state.assumes:
        if os_theory.is_defining_eq(thy, assume.prop):
            define_eqs.append(assume.prop)
    
    # Expand remaining facts and goal using the defining equations
    assumes: list[OSTerm] = []
    for assume in state.assumes:
        if not os_theory.is_defining_eq(thy, assume.prop):
            assumes.append(os_simplify.simplify_define_eqs(var_ctxt, define_eqs, assume.prop))
    concl: OSTerm = os_simplify.simplify_define_eqs(var_ctxt, define_eqs, state.concl.prop)

    # Expand equations on structures and datatypes
    normalize = os_simplify.Normalize(thy)
    for i in range(len(assumes)):
        assumes[i] = assumes[i].transform(var_ctxt, normalize)
    concl = concl.transform(var_ctxt, normalize)

    # Perform standard simplifications after expansion
    thm_list = ["get_update", "indom_update", "seq_append_length", "seq_append_index"]
    for i in range(len(assumes)):
        assumes[i] = os_simplify.rewrite_thms(thy, var_ctxt, thm_list, assumes[i])
        assumes[i] = assumes[i].transform(var_ctxt, os_simplify.Normalize(thy))
    concl = os_simplify.rewrite_thms(thy, var_ctxt, thm_list, concl)
    concl = concl.transform(var_ctxt, os_simplify.Normalize(thy))

    return define_eqs, assumes, concl

def solve(thy: OSTheory, state) -> SolveResult:
    """Solve the given goal using Z3.

    Parameters
    ----------
    thy: OSTheory
        current theory
    state: ProofState
        current proof state

    Returns
    -------
    SolveResult
        If the query can be proved, return UnsatResult. Otherwise return a model
        that serves as counterexample to the query.

    """
    _, assumes, concl = simplify_state(thy, state)
    # print("--- After simplification ---")
    # print("Defining equations")
    # for define_eq in define_eqs:
    #     print(define_eq)
    # print()
    # print("Assumptions")
    # for assume in assumes:
    #     print(assume)
    # print()
    # print("Conclusion")
    # print(concl)
    return solve_impl(thy, assumes, concl)

def convert_z3_expr(z3_t: z3.Z3PPObject) -> OSTerm:
    """Convert the Z3 expression to OS expressions"""
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
    elif isinstance(z3_t, z3.BitVecRef):
        raise AssertionError("convert_z3_expr on %s, type %s" % (z3_t, type(z3_t)))
    else:
        raise NotImplementedError("convert_z3_expr on %s, type %s" % (z3_t, type(z3_t)))
