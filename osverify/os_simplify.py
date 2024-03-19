"""Simplification procedures"""

from typing import Set

from osverify import os_struct
from osverify import os_term
from osverify.os_term import OSTerm
from osverify import os_theory
from osverify.os_theory import OSTheory
from osverify import os_match

def rewrite(thy: OSTheory, eq_th: OSTerm, t: OSTerm) -> OSTerm:
    """Perform rewrite once using given theorem.

    If rewrite fails, the original term t is returned.

    """
    assert os_term.is_eq(eq_th), "rewrite: theorem is not equality."
    lhs, rhs = eq_th.args
    tyinst, inst = dict(), dict()
    if not os_match.match(thy, lhs, t, tyinst, inst):
        return t
    else:
        return rhs.subst_type(tyinst).subst(inst)

def rewrite_thm(thy: OSTheory, th_name: str, t: OSTerm) -> OSTerm:
    """Perform rewrite once using theorem with the given name.
    
    If rewrite fails, the original term t is returned.
    
    """
    if th_name not in thy.theorems:
        raise AssertionError("rewrite_thm: theorem %s not found" % th_name)
    th = thy.get_sch_theorem(th_name)
    if os_term.is_eq(th):
        t = rewrite(thy, th, t)
    return t

def simplify_rewrite(thy: OSTheory, t: OSTerm) -> OSTerm:
    """Simplify using all rewrite rules in the theory."""
    for th_name in thy.attribute_map['rewrite']:
        th = thy.get_sch_theorem(th_name)
        if os_term.is_eq(th):
            t = rewrite(thy, th, t)
    return t

def simplify_switch_once(thy: OSTheory, t: OSTerm) -> OSTerm:
    """Simplify switch statement for one step.
    
    This function makes the use of the following reduction rules:

    - if there are no branches in the switch statement, rewrite to
      "undefined" (this should indicate incomplete cases).

    - if the first branch is the default branch, rewrite to the expression
      for the default branch.

    - if the first branch is a variable, perform substitution on the
      corresponding expression.

    - if the first branch is a numerical constant, change to if-then-else
      expression.

    - finally, handle the cases for tuples, structure values, and
      datatype constructors.
    
    """
    if not isinstance(t, os_term.OSSwitch):
        return t  # not a switch term

    if len(t.branches) == 0:
        return os_term.OSFun("undefined", type=t.type)

    # Default case
    if isinstance(t.branches[0], os_term.OSSwitchBranchDefault):
        return t.branches[0].expr
    assert isinstance(t.branches[0], os_term.OSSwitchBranchCase)

    # Now obtain the first pattern and expression 
    pattern, expr = t.branches[0].pattern, t.branches[0].expr

    # Matching on variable: substitute variable for the matched expression
    # in the body of switch
    if isinstance(pattern, os_term.OSVar):
        return expr.subst({pattern.name: t.switch_expr})
    
    elif isinstance(pattern, os_term.OSWildcard):
        return expr

    # Matching on numerical constants: convert to if-then-else expression
    elif isinstance(pattern, os_term.OSNumber):
        return os_term.OSFun("ite", os_term.eq(t.switch_expr, pattern), expr,
                             os_term.OSSwitch(t.switch_expr, t.branches[1:], type=t.type),
                             type=t.type)

    # Matching on structure literals: the general form is
    #
    # switch (expr) {
    #   case Struct{{field1: val1, field2: val2, ...}}:
    #     expr1;
    #   ... other cases ...
    # }
    # 
    # This should be converted into:
    # switch (expr.field1) {
    #   case val1:
    #     switch (expr) {
    #       case Struct{{field2: val2, ...}}:
    #         expr1;
    #       ... other cases ...
    #     }
    #   ... other cases
    # }   
    elif isinstance(pattern, os_term.OSStructVal):
        # No matched fields remaining
        if len(pattern.vals) == 0:
            return expr

        # field1, val1
        field, val = pattern.vals[0]

        # case Struct{{field2: val2, ...}}: expr1
        remain_case = os_term.OSSwitchBranchCase(
            os_term.OSStructVal(pattern.struct_name, pattern.vals[1:]), expr)

        # Expression for case val1:
        case1_expr = os_term.OSSwitch(t.switch_expr, (remain_case,) + t.branches[1:], type=t.type)

        # Case val1:
        case1 = os_term.OSSwitchBranchCase(val, case1_expr)

        # Entire expression
        return os_term.OSSwitch(os_term.FieldGet(t.switch_expr, field, type=val.type),
                                (case1,) + t.branches[1:], type=t.type)

    # Matching on product: the general form is
    #
    # switch (t1, t2) {
    #   case (p1, p2):
    #     expr1;
    #   ... other cases ...        
    # }
    #
    # This is rewritten into
    # switch (t1) {
    #   case p1:
    #     switch (t2) {
    #       case p2:
    #         expr1;
    #       default:
    #         switch (t1, t2) {
    #           ... other cases ...
    #         }
    #     }
    #   default:
    #     switch (t1, t2) {
    #       ... other cases ...
    #     }
    # }
    elif os_term.is_pair(pattern) and os_term.is_pair(t.switch_expr):
        t1, t2 = t.switch_expr.args
        p1, p2 = pattern.args
        default = os_term.OSSwitchBranchDefault(os_term.OSSwitch(t.switch_expr, t.branches[1:], type=t.type))
        case_p2 = os_term.OSSwitchBranchCase(p2, expr)
        switch_t2 = os_term.OSSwitch(t2, [case_p2, default], type=t.type)
        case_p1 = os_term.OSSwitchBranchCase(p1, switch_t2)
        return os_term.OSSwitch(t1, [case_p1, default], type=t.type)

    # Matching on constructor: the general form is:
    #
    # switch (expr) {
    #   case constr(args):
    #     expr1;
    #   ... other cases ...
    # }
    #
    # If expression has the same function name as constr, then rewrite to
    # switching on each argument of the expression:
    #
    # switch (expr.args) {
    #   case args:
    #     expr1;
    #   default:
    #     switch (expr) {
    #       ... other cases ...
    #     }
    # }
    #
    # Otherwise, simply remove the first case:
    #
    # switch (expr) {
    #   ... other cases ...
    # }
    #
    # One more case need to be considered: if expr is not a constructor, but
    # the case is not in reduced form, then replace non-reduced parts by
    # variables and match on those variable.
    elif isinstance(pattern, os_term.OSFun):
        ty = os_theory.expand_type(thy, t.switch_expr.type)
        if not (isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.datatypes):
            raise AssertionError
        datatype = thy.datatypes[ty.name]

        # Constructor of the pattern, make sure it is one of the datatype constructors
        if pattern.func_name not in datatype.branch_map:
            raise AssertionError
        
        default = os_term.OSSwitchBranchDefault(os_term.OSSwitch(t.switch_expr, t.branches[1:], type=t.type))

        # If t.expr is not one of the constructors, attempt to reduce arguments
        if not isinstance(t.switch_expr, os_term.OSFun) or \
            t.switch_expr.func_name not in datatype.branch_map:
            branch = datatype.branch_map[pattern.func_name]
            reduce_params, reduce_args = list(), list()
            pat_params = list()
            for arg, (param_name, _) in zip(pattern.args, branch.params):
                if not isinstance(arg, os_term.OSVar):
                    reduce_params.append(os_term.OSVar(param_name, type=arg.type))
                    reduce_args.append(arg)
                    pat_params.append(os_term.OSVar(param_name, type=arg.type))
                else:
                    pat_params.append(arg)
            pat = os_term.OSFun(pattern.func_name, *pat_params, type=pattern.type)
            if reduce_params:
                case_args = os_term.OSSwitchBranchCase(os_term.list_pair(*reduce_args), expr)
                inner = os_term.OSSwitch(os_term.list_pair(*reduce_params), [case_args, default], type=t.type)
                case_params = os_term.OSSwitchBranchCase(pat, inner)
                outer = os_term.OSSwitch(t.switch_expr, [case_params, default], type=t.type)
                return outer
            else:
                return t

        # If t.expr is one of the constructors, compare with first pattern
        if t.switch_expr.func_name == pattern.func_name:
            if len(pattern.args) == 0:
                return expr
            else:
                case_args = os_term.OSSwitchBranchCase(os_term.list_pair(*pattern.args), expr)
                return os_term.OSSwitch(os_term.list_pair(*t.switch_expr.args), [case_args, default], type=t.type)
        else:
            return os_term.OSSwitch(t.switch_expr, t.branches[1:], type=t.type)

    return t  # argument is not datatype
    
def simplify_switch(thy: OSTheory, t: OSTerm) -> OSTerm:
    """Simplify switch statement.
    
    This function repeatedly applies simplify_switch_once until no more
    rewrites can be done. The result should be a switch statement in
    standard form (satisfy the test by `is_standard_switch`).
    
    """
    t2 = simplify_switch_once(thy, t)
    if t2 != t:
        return t2.apply_subterm(lambda t: simplify_switch(thy, t))
    else:
        return t2
    
def simplify_let(thy: OSTheory, t: OSTerm) -> OSTerm:
    """Simplify let expression.
    
    Rewrite "let x = t in body" to "body[t/x]".
    
    """
    if isinstance(t, os_term.OSLet):
        return t.rhs.subst({t.var_name: t.expr})
    
    return t

def simplify_field_get(thy: OSTheory, t: OSTerm) -> OSTerm:
    if isinstance(t, os_term.FieldGet):
        if isinstance(t.expr, os_term.OSStructVal):
            return t.expr.dict_vals[t.field]
        elif isinstance(t.expr, os_term.OSStructUpdate):
            if t.field in t.expr.dict_updates:
                return t.expr.dict_updates[t.field]
            else:
                return os_term.FieldGet(t.expr.ori_expr, t.field, type=t.type)
        else:
            return t
        
    return t

def simplify_consts(thy: OSTheory, t: OSTerm) -> OSTerm:
    """Evaluate operations on constants."""
    if isinstance(t, os_term.OSOp):
        if len(t.args) == 2:
            a, b = t.args
            if isinstance(a, os_term.OSNumber) and isinstance(b, os_term.OSNumber):
                if t.op == "==":
                    return os_term.OSNumber(a.val == b.val, type=os_struct.Bool)
    
    if isinstance(t, os_term.OSFun):
        if t.func_name == "ite":
            if t.args[0] == os_term.OSNumber(True, os_struct.Bool):
                return t.args[1]
            if t.args[0] == os_term.OSNumber(False, os_struct.Bool):
                return t.args[2]

    return t

def simplify(thy: OSTheory, t: OSTerm) -> OSTerm:
    """Perform simplification."""
    max_round = 10
    while max_round > 0:
        old_t = t
        t = t.apply_subterm(lambda t2: simplify_let(thy, t2))
        t = t.apply_subterm(lambda t2: simplify_switch(thy, t2))
        t = t.apply_subterm(lambda t2: simplify_field_get(thy, t2))
        t = t.apply_subterm(lambda t2: simplify_consts(thy, t2))
        t = t.apply_subterm(lambda t2: simplify_rewrite(thy, t2))

        if t == old_t:
            return t
        max_round -= 1

    raise AssertionError("simplify: maximum number of rounds reached")
