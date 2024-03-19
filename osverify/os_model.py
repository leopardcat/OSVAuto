from typing import Dict, Iterable, Tuple, List, Type

from osverify import os_theory
from osverify import os_term
from osverify import os_struct
from osverify import os_simplify
from osverify.os_query import Model
from osverify.os_term import OSTerm

def evaluate_term(thy: os_theory.OSTheory, t: OSTerm) -> OSTerm:
    """Evaluate the given term."""
    if isinstance(t, os_term.OSFun):
        if t.func_name == 'nth':
            array, idx = evaluate_term(thy, t.args[0]), evaluate_term(thy, t.args[1])
            if isinstance(array, os_term.OSFun) and array.func_name == "K":
                return array.args[0]
            elif isinstance(array, os_term.OSFun) and array.func_name == "Store":
                if isinstance(array.args[1], os_term.OSNumber) and isinstance(idx, os_term.OSNumber):
                    if array.args[1].val != idx.val:
                        return evaluate_term(thy, os_term.OSFun("nth", array.args[0], idx))
                    else:
                        return evaluate_term(thy, array.args[2])
            else:
                return os_term.OSFun("nth", array, idx)
        elif t.func_name == "indom":
            k, map = t.args
            map = os_term.strip_map(map)
            return os_term.OSNumber(k in map)
        elif t.func_name == "get":
            k, map = t.args
            map = os_term.strip_map(map)
            if k not in map:
                raise AssertionError("evaluate_term: %s" % t)
            return map[k]
        elif t.func_name == "mapUpdate":
            k, v, map, new_map = t.args
            map = os_term.strip_map(map)
            new_map = os_term.strip_map(new_map)
            map[k] = v
            return os_term.OSNumber(map == new_map)
        elif t.func_name in thy.fixps:
            # Case of invariant or predicate
            return evaluate_term(thy, os_simplify.rewrite(thy, thy.get_definition(t.func_name), t))
        else:
            return os_term.OSFun(t.func_name, *(evaluate_term(thy, arg) for arg in t.args), type=t.type)
    elif isinstance(t, os_term.OSLet):
        return evaluate_term(thy, t.rhs.subst({t.var_name: t.expr}))
    elif isinstance(t, os_term.OSNumber):
        return t
    elif isinstance(t, os_term.OSConst):
        return os_term.OSNumber(thy.const_val[t.name], t.type)
    elif isinstance(t, os_term.OSOp):
        if len(t.args) == 1:
            a = evaluate_term(thy, t.args[0])
            if t.op == "!" and a == os_term.OSNumber(False):
                return os_term.OSNumber(True)
            elif t.op == "!" and a == os_term.OSNumber(True):
                return os_term.OSNumber(False)
            else:
                raise NotImplementedError("evaluate term on %s" % t)

        assert len(t.args) == 2, "evaluate term on %s" % t

        a, b = evaluate_term(thy, t.args[0]), evaluate_term(thy, t.args[1])
        
        # Short-circuit evaluations
        if t.op == "->" and a == os_term.OSNumber(False):
            return os_term.OSNumber(True)
        if t.op == "->" and b == os_term.OSNumber(True):
            return os_term.OSNumber(True)
        if t.op == "&&" and a == os_term.OSNumber(False):
            return os_term.OSNumber(False)
        if t.op == "&&" and b == os_term.OSNumber(False):
            return os_term.OSNumber(False)
        if t.op == "||" and a == os_term.OSNumber(True):
            return os_term.OSNumber(True)
        if t.op == "||" and a == os_term.OSNumber(True):
            return os_term.OSNumber(True)

        if isinstance(a, os_term.OSNumber) and isinstance(b, os_term.OSNumber):
            if t.op == '==':
                return os_term.OSNumber(a.val == b.val)
            if t.op == "->":
                return os_term.OSNumber(not a.val or b.val)
            elif t.op == "||":
                return os_term.OSNumber(a.val or b.val)
            elif t.op == "&&":
                return os_term.OSNumber(a.val and b.val)
            elif t.op == "<=":
                return os_term.OSNumber(a.val <= b.val)
            elif t.op == "<":
                return os_term.OSNumber(a.val < b.val)
            elif t.op == ">=":
                return os_term.OSNumber(a.val >= b.val)
            elif t.op == ">":
                return os_term.OSNumber(a.val > b.val)
            elif t.op == "&":
                return os_term.OSNumber(a.val & b.val)
            elif t.op == ">>":
                return os_term.OSNumber(a.val >> b.val)
            elif t.op == "<<":
                return os_term.OSNumber(a.val << b.val)
            elif t.op == "|":
                return os_term.OSNumber(a.val | b.val)
            else:
                return os_term.OSOp(t.op, a, b)
        elif t.op == '==' and isinstance(a, os_term.OSFun) and isinstance(b, os_term.OSFun) and \
            a.func_name in thy.constr_types and b.func_name in thy.constr_types:
            if a.func_name != b.func_name:
                return os_term.OSNumber(False)
            else:
                assert len(a.args) == len(b.args)
                for arg1, arg2 in zip(a.args, b.args):
                    eval_res = evaluate_term(thy, os_term.OSOp("==", arg1, arg2))
                    if eval_res == os_term.OSNumber(False):
                        return os_term.OSNumber(False)
                    elif eval_res == os_term.OSNumber(True):
                        continue
                    else:
                        # Unknown
                        return os_term.OSOp("==", a, b)
                # All arguments are equal
                return os_term.OSNumber(True)
        else:
            return os_term.OSOp(t.op, a, b)
    elif isinstance(t, os_term.FieldGet):
        struct = evaluate_term(thy, t.expr)
        assert isinstance(struct, os_term.OSStructVal)
        if t.field in struct.dict_vals:
            return evaluate_term(thy, struct.dict_vals[t.field])
        else:
            return os_term.FieldGet(struct, t.field)
    elif isinstance(t, os_term.OSStructVal):
        ty = t.type
        assert isinstance(ty, os_struct.OSStructType) and ty.name in thy.structs
        struct_vals = list()
        for field in thy.structs[ty.name].fields:
            name = field.field_name
            if name in t.dict_vals:
                struct_vals.append((name, evaluate_term(thy, t.dict_vals[name])))
        return os_term.OSStructVal(ty.name, struct_vals)
    elif isinstance(t, os_term.OSStructUpdate):
        struct = evaluate_term(thy, t.ori_expr)
        ty = struct.type
        assert isinstance(struct, os_term.OSStructVal) and isinstance(ty, os_struct.OSStructType)
        struct_vals = list()
        for field in thy.structs[ty.name].fields:
            name = field.field_name
            if name in t.dict_updates:
                struct_vals.append((name, evaluate_term(thy, t.dict_updates[name])))
            elif field.field_name in struct.dict_vals:
                struct_vals.append((name, struct.dict_vals[name]))
        return os_term.OSStructVal(struct.struct_name, struct_vals)
    elif isinstance(t, os_term.OSSwitch):
        if not os_theory.is_standard_switch(thy, t):
            return evaluate_term(thy, os_simplify.simplify_switch(thy, t))

        switch_expr = evaluate_term(thy, t.switch_expr)
        ty = os_theory.expand_type(thy, t.switch_expr.type)
        if not (isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.datatypes):
            raise AssertionError
        datatype = thy.datatypes[ty.name]

        if not isinstance(switch_expr, os_term.OSFun) or switch_expr.func_name not in datatype.branch_map:
            raise AssertionError
        for branch in t.branches[:-1]:
            assert isinstance(branch, os_term.OSSwitchBranchCase)
            assert isinstance(branch.pattern, os_term.OSFun)
            constr_name = branch.pattern.func_name
            assert constr_name in datatype.branch_map
            datatype_branch = datatype.branch_map[constr_name]
            if constr_name == switch_expr.func_name:
                inst: Dict[str, OSTerm] = dict()
                for (param_name, _), arg in zip(datatype_branch.params, branch.pattern.args):
                    assert isinstance(arg, os_term.OSVar)
                    field_ty = thy.get_field_type(ty, param_name)
                    inst[arg.name] = os_term.FieldGet(switch_expr, param_name, type=field_ty)
                new_expr = branch.expr.subst(inst)
                return evaluate_term(thy, new_expr)
        assert isinstance(t.branches[-1], os_term.OSSwitchBranchDefault)
        return evaluate_term(thy, t.branches[-1].expr)
    elif isinstance(t, os_term.OSQuantIn):
        collection = evaluate_term(thy, t.collection)
        collection_ty = os_theory.expand_type(thy, collection.type)
        keys: Tuple[OSTerm]
        if os_struct.isMapType(collection_ty):
            map = os_term.strip_map(collection)
            keys = tuple(map.keys())
        elif os_struct.isListType(collection_ty):
            keys = os_term.strip_list(collection)
        else:
            raise NotImplementedError

        if t.quantifier == "forall":
            for k in keys:
                cur_body = evaluate_term(thy, t.body.subst({t.param.name: k}))
                cur_val = evaluate_term(thy, cur_body)
                if cur_val == os_term.false:
                    return os_term.false
                elif cur_val == os_term.true:
                    continue
                else:
                    return cur_val
            return os_term.true
        elif t.quantifier == "exists":
            for k in keys:
                cur_body = evaluate_term(thy, t.body.subst({t.param.name: k}))
                cur_val == evaluate_term(thy, cur_body)
                if cur_val == os_term.true:
                    return os_term.true
                elif cur_val == os_term.false:
                    continue
                else:
                    return cur_val
            return os_term.false
        else:
            raise NotImplementedError("evaluating: %s" % t)

    else:
        raise NotImplementedError("evaluating: %s" % t)

def diagnose_predicate(thy: os_theory.OSTheory, t: OSTerm, inst: Dict[str, OSTerm]):
    res = evaluate_term(thy, t.subst(inst))
    if res == os_term.OSNumber(True):
        print("OK: %s" % t)
    elif res == os_term.OSNumber(False):
        print("Fail: %s" % t)
        if isinstance(t, os_term.OSFun) and t.func_name in thy.fixps:
            pred = os_simplify.rewrite(thy, thy.get_definition(t.func_name), t)
            if os_term.is_conj(pred):
                for comp in os_term.split_conj(pred):
                    diagnose_predicate(thy, comp, inst)
    else:
        print("Evaluated as %s" % res)
        print("Unknown: %s" % t)

def diagnose_query(thy: os_theory.OSTheory,
                   assumes: Iterable[OSTerm], concl: OSTerm,
                   model: Model):
    """Print diagnosis information for a model."""
    for assume in assumes:
        diagnose_predicate(thy, assume, model.data)
    diagnose_predicate(thy, concl, model.data)
