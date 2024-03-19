"""
Matching procedures
"""

from typing import Dict

from osverify.os_struct import OSType
from osverify import os_term
from osverify.os_term import OSTerm
from osverify import os_theory
from osverify.os_theory import OSTheory, match_type


def match(thy: OSTheory, pat: OSTerm, t: OSTerm,
          tyinst: Dict[str, OSType], inst: Dict[str, OSTerm]) -> bool:
    """Matching given pattern and term.

    Performs first-order matching of pattern against term. Schematic
    variables in the pattern can be instantiated with term of the
    same type.

    Parameters
    ----------
    thy : OSTheory
        The current theory
    pat : OSTerm
        Pattern to be matched
    t : OSTerm
        Concrete term to match pat
    tyinst : Dict[str, OSType]
        Existing instantiation of schematic type variables. This may be
        updated during matching.
    inst : Dict[str, OSTerm]
        Existing instantiation of schematic variables. This may be updated
        during matching.
    
    Returns
    -------
    bool
        Whether a matching is successful.
    """
    if isinstance(pat, os_term.OSWildcard):
        return match_type(thy, pat.type, t.type, tyinst)
    elif isinstance(pat, os_term.OSVar):
        if not pat.is_sch_var():
            return pat == t
        elif pat.name not in inst:
            if not match_type(thy, pat.type, t.type, tyinst):
                return False
            inst[pat.name] = t
            return True
        else:
            return inst[pat.name] == t
    elif isinstance(pat, (os_term.OSConst, os_term.OSNumber)):
        if not match_type(thy, pat.type, t.type, tyinst):
            return False
        return pat == t
    elif isinstance(pat, os_term.OSFun):
        if not isinstance(t, os_term.OSFun):
            return False
        if pat.func_name != t.func_name:
            return False
        if len(pat.args) != len(t.args):
            return False
        if not match_type(thy, pat.type, t.type, tyinst):
            return False
        for pat_arg, t_arg in zip(pat.args, t.args):
            if not match(thy, pat_arg, t_arg, tyinst, inst):
                return False
        return True
    elif isinstance(pat, os_term.OSOp):
        if not isinstance(t, os_term.OSOp):
            return False
        if pat.op != t.op:
            return False
        if len(pat.args) != len(t.args):
            return False
        if not match_type(thy, pat.type, t.type, tyinst):
            return False
        for pat_arg, t_arg in zip(pat.args, t.args):
            if not match(thy, pat_arg, t_arg, tyinst, inst):
                return False
        return True
    elif isinstance(pat, os_term.FieldGet):
        if not isinstance(t, os_term.FieldGet):
            return False
        if pat.field != t.field:
            return False
        return match(thy, pat.expr, t.expr, tyinst, inst)
    elif isinstance(pat, os_term.OSSwitch):
        if not isinstance(t, os_term.OSSwitch):
            return False
        if not match(thy, pat.switch_expr, t.switch_expr, tyinst, inst):
            return False
        for pat_branch, t_branch in zip(pat.branches, t.branches):
            if isinstance(pat_branch, os_term.OSSwitchBranchCase):
                if not isinstance(t_branch, os_term.OSSwitchBranchCase):
                    return False
                pat_inst = dict()
                if not match(thy, pat_branch.pattern, t_branch.pattern, tyinst, pat_inst):
                    return False
                # Rename bound variables
                expr2 = pat_branch.expr.subst(pat_inst)
                if not match(thy, expr2, t_branch.expr, tyinst, inst):
                    return False
            elif isinstance(pat_branch, os_term.OSSwitchBranchDefault):
                if not isinstance(t_branch, os_term.OSSwitchBranchDefault):
                    return False
                if not match(thy, pat_branch.expr, t_branch.expr, tyinst, inst):
                    return False
        return True
    elif isinstance(pat, os_term.OSQuant):
        if not isinstance(t, os_term.OSQuant):
            return False
        if pat.quantifier != t.quantifier:
            return False
        # Rename pat.params into t.params
        param_inst = dict(zip([param.name for param in pat.params], t.params))
        pat2 = pat.body.subst(param_inst)
        if not match(thy, pat2, t.body, tyinst, inst):
            return False
        return True
    else:
        raise NotImplementedError("match: %s" % pat)
