from typing import Dict, Iterable, Tuple, List, Type

from osverify import os_theory
from osverify import os_term
from osverify import os_struct
from osverify import os_simplify
from osverify.os_query import Model
from osverify.os_term import OSTerm
from osverify.os_util import indent

class EvaluateTermException(Exception):
    def __init__(self, msg: str):
        self.msg = msg

    def __str__(self):
        return self.msg


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
                        return evaluate_term(thy, os_term.OSFun("nth", array.args[0], idx, type=t.type))
                    else:
                        return evaluate_term(thy, array.args[2])
            else:
                raise EvaluateTermException("nth: array %s not in standard form" % array)
        elif t.func_name == "ite":
            cond, t1, t2 = [evaluate_term(thy, arg) for arg in t.args]
            if cond == os_term.true:
                return t1
            elif cond == os_term.false:
                return t2
            else:
                raise EvaluateTermException("ite: condition is %s" % cond)
        elif t.func_name == "indom":
            k, map = t.args
            eval_k = evaluate_term(thy, k)
            map = os_term.strip_map(map)
            return os_term.OSNumber(eval_k in map)
        elif t.func_name == "get":
            k, map = t.args
            eval_k = evaluate_term(thy, k)
            map = os_term.strip_map(map)
            if eval_k not in map:
                raise AssertionError("evaluate_term: %s (key %s not found)" % (t, k))
            return map[eval_k]
        elif t.func_name == "mapUpdate":
            k, v, map, new_map = t.args
            eval_k, eval_v = evaluate_term(thy, k), evaluate_term(thy, v)
            map = os_term.strip_map(map)
            new_map = os_term.strip_map(new_map)
            map[eval_k] = eval_v
            return os_term.OSNumber(map == new_map)
        elif t.func_name == "join":
            k, v, map, new_map = t.args
            eval_k, eval_v = evaluate_term(thy, k), evaluate_term(thy, v)
            map = os_term.strip_map(map)
            new_map = os_term.strip_map(new_map)
            if eval_k in map:
                return os_term.false
            map[eval_k] = eval_v
            return os_term.OSNumber(map == new_map)
        elif t.func_name in thy.fixps:
            # Case of invariant or predicate
            return evaluate_term(thy, os_simplify.rewrite(thy, thy.get_definition(t.func_name), t))
        elif t.func_name in thy.constr_datatype:
            # Case of constructor
            return os_term.OSFun(t.func_name, *(evaluate_term(thy, arg) for arg in t.args), type=t.type)
        elif t.func_name in ('emptyMap', 'updateMap', 'K', 'Store', 'range'):
            # Constructor for arrays and maps
            return os_term.OSFun(t.func_name, *(evaluate_term(thy, arg) for arg in t.args), type=t.type)
        else:
            raise EvaluateTermException("Unable to evaluate function %s" % t.func_name)
    elif isinstance(t, os_term.OSLet):
        return evaluate_term(thy, t.rhs.subst({t.var_name: t.expr}))
    elif isinstance(t, os_term.OSNumber):
        return t
    elif isinstance(t, os_term.OSConst):
        return os_term.OSNumber(thy.const_val[t.name], t.type)
    elif isinstance(t, os_term.OSOp):
        if len(t.args) == 1:
            a = evaluate_term(thy, t.args[0])
            if t.op == "!" and a == os_term.false:
                return os_term.true
            elif t.op == "!" and a == os_term.true:
                return os_term.false
            elif t.op == "~":
                if isinstance(a, os_term.OSNumber):
                    return os_term.OSNumber(~a.val, type=t.type)
                else:
                    raise NotImplementedError("evaluate term on ~%s" % a)
            else:
                raise NotImplementedError("evaluate term on %s" % t)

        assert len(t.args) == 2, "evaluate term on %s" % t
        
        a = evaluate_term(thy, t.args[0])

        # Short-circuit evaluations:
        if t.op == "->" and a == os_term.false:
            return os_term.true
        if t.op == "&&" and a == os_term.false:
            return os_term.false
        if t.op == "||" and a == os_term.true:
            return os_term.true

        b = evaluate_term(thy, t.args[1])

        if isinstance(a, os_term.OSNumber) and isinstance(b, os_term.OSNumber):
            if t.op == '==':
                return os_term.OSNumber(a.val == b.val)
            elif t.op == '!=':
                return os_term.OSNumber(a.val != b.val)
            elif t.op == "->":
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
                return os_term.OSNumber(a.val & b.val, type=t.type)
            elif t.op == ">>":
                return os_term.OSNumber(a.val >> b.val, type=t.type)
            elif t.op == "<<":
                return os_term.OSNumber(a.val << b.val, type=t.type)
            elif t.op == "|":
                return os_term.OSNumber(a.val | b.val, type=t.type)
            else:
                raise EvaluateTermException("Unable to evaluate %s" % t)
        elif t.op == '==' and isinstance(a, os_term.OSStructVal) and isinstance(b, os_term.OSStructVal):
            if a.struct_name != b.struct_name:
                return os_term.false
            else:
                assert a.dict_vals.keys() == b.dict_vals.keys(), (
                    "Comparing two OSStructVal: set of keys not the same. %s vs %s" % (
                        a.dict_vals.keys(), b.dict_vals.keys())
                )
                for k in a.dict_vals.keys():
                    eval_res = evaluate_term(thy, os_term.eq(a.dict_vals[k], b.dict_vals[k]))
                    if eval_res == os_term.false:
                        return os_term.false
                    elif eval_res == os_term.true:
                        continue
                    else:
                        raise AssertionError
                # All values are equal
                return os_term.true
        elif t.op == '==' and isinstance(a, os_term.OSFun) and isinstance(b, os_term.OSFun) and \
            a.func_name in thy.constr_types and b.func_name in thy.constr_types:
            if a.func_name != b.func_name:
                return os_term.false
            else:
                assert len(a.args) == len(b.args)
                for arg1, arg2 in zip(a.args, b.args):
                    eval_res = evaluate_term(thy, os_term.OSOp("==", arg1, arg2))
                    if eval_res == os_term.false:
                        return os_term.false
                    elif eval_res == os_term.true:
                        continue
                    else:
                        raise EvaluateTermException("%s on %s and %s" % (t.op, a, b))
                # All arguments are equal
                return os_term.true
        elif t.op == '==' and isinstance(a, os_term.OSVar) and isinstance(b, os_term.OSVar):
            return os_term.OSNumber(a.name == b.name)
        elif t.op == '==' and isinstance(a, os_term.OSFun) and isinstance(b, os_term.OSFun) and \
            a.func_name in ('K', 'Store') and b.func_name in ('K', 'Store'):
            default_a, updates_a = os_term.strip_array(a)
            default_b, updates_b = os_term.strip_array(b)
            eval_default = evaluate_term(thy, os_term.eq(default_a, default_b))
            if eval_default == os_term.false:
                return os_term.false
            if eval_default != os_term.true:
                raise AssertionError
            if len(updates_a) != len(updates_b):
                return os_term.false
            for k in updates_a:
                if k not in updates_b:
                    return os_term.false
                eval_val = evaluate_term(thy, os_term.eq(updates_a[k], updates_b[k]))
                if eval_val == os_term.false:
                    return os_term.false
                if eval_val != os_term.true:
                    raise AssertionError
            return os_term.true
        elif t.op == '!=':
            return evaluate_term(thy, os_term.OSOp("!", os_term.eq(t.args[0], t.args[1]), type=os_struct.Bool))
        else:
            raise EvaluateTermException("%s on %s and %s" % (t.op, a, b))
    elif isinstance(t, os_term.FieldGet):
        # Obtain the value at some field. There are two cases:
        # 1. t is a structure literal.
        # 2. t is a constructor 

        t_expr = evaluate_term(thy, t.expr)
        ty = os_theory.expand_type(thy, t.expr.type)

        if isinstance(ty, os_struct.OSStructType) and ty.name in thy.structs:
            # Case of structure literal
            if isinstance(t_expr, os_term.OSStructVal):
                if t.field in t_expr.dict_vals:
                    return evaluate_term(thy, t_expr.dict_vals[t.field])
                else:
                    raise EvaluateTermException("FieldGet: field %s not found in %s" % (t.field, struct))
            else:
                raise EvaluateTermException("FieldGet: %s is not a structure literal")
        elif isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.datatypes:
            # Case of datatype
            datatype = thy.datatypes[ty.name]
            if not isinstance(t_expr, os_term.OSFun):
                raise EvaluateTermException("FieldGet: %s is not in constructor form")
            if t_expr.func_name not in datatype.branch_map:
                raise EvaluateTermException("FieldGet: %s is not in constructor form")
            datatype_branch = datatype.branch_map[t_expr.func_name]
            for i, (param_name, _) in enumerate(datatype_branch.params):
                if param_name == t.field:
                    return evaluate_term(thy, t_expr.args[i])
            raise EvaluateTermException("FieldGet: %s is not a field for branch %s" % (
                t.field, datatype_branch
            ))
        else:
            raise EvaluateTermException("FieldGet: unknown type %s" % ty)
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

        if not isinstance(switch_expr, os_term.OSFun):
            raise EvaluateTermException("OSSwitch: switch expression %s is not in constructor form")
        if switch_expr.func_name not in datatype.branch_map:
            raise EvaluateTermException("OSSwitch: switch expression %s is not in constructor form")
        for branch in t.branches:
            if isinstance(branch, os_term.OSSwitchBranchCase):
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
            else:
                assert isinstance(branch, os_term.OSSwitchBranchDefault)
                return evaluate_term(thy, branch.expr)
    elif isinstance(t, os_term.OSQuantIn):
        collection = evaluate_term(thy, t.collection)
        collection_ty = os_theory.expand_type(thy, collection.type)
        keys: Tuple[OSTerm]
        if os_struct.isMapType(collection_ty):
            map = os_term.strip_map(collection)
            keys = tuple(map.keys())
        elif os_struct.isListType(collection_ty):
            if isinstance(collection, os_term.OSFun) and collection.func_name == "range" and \
                isinstance(collection.args[0], os_term.OSNumber) and \
                isinstance(collection.args[1], os_term.OSNumber):
                min_val = collection.args[0].val
                max_val = collection.args[1].val
                keys = [os_term.OSNumber(v, os_struct.Int32U) for v in range(min_val, max_val)]
            else:
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
                cur_val = evaluate_term(thy, cur_body)
                if cur_val == os_term.true:
                    return os_term.true
                elif cur_val == os_term.false:
                    continue
                else:
                    return cur_val
            return os_term.false
        else:
            raise NotImplementedError("evaluating: %s" % t)
    elif isinstance(t, os_term.OSVar):
        return t
    elif isinstance(t, os_term.OSUnknown):
        return t
    else:
        raise NotImplementedError("evaluating: %s" % t)

def diagnose_predicate(thy: os_theory.OSTheory, t: OSTerm, inst: Dict[str, OSTerm], level: int = 0):
    """Print diagnosis for a given term with respect to model.

    If the term evaluates to True, print OK for the term. Otherwise, if the
    term can be expanded further, perform diagnosis for the components at
    one level deeper.
    
    Parameters
    ----------
    thy : OSTheory
        current theory
    t : OSTerm
        term to evaluate
    inst : Dict[str, OSTerm]
        current model, as a mapping from variable name to term
    level : int
        depth of diagnoses, used for printing
    
    """
    res = evaluate_term(thy, t.subst(inst))
    if res == os_term.true:
        print(indent("OK: %s" % t, level * 2))
    elif res == os_term.false:
        print(indent("Fail: %s" % t, level * 2))
        if isinstance(t, os_term.OSFun) and t.func_name in thy.fixps:
            pred = os_simplify.rewrite(thy, thy.get_definition(t.func_name), t)
            if os_term.is_conj(pred):
                conjs = os_term.split_conj(pred)
                for comp in conjs:
                    diagnose_predicate(thy, comp, inst, level+1)
            if os_term.is_implies(pred):
                assums, concl = os_term.strip_implies(pred)
                concls = os_term.split_conj(concl)
                for comp in assums:
                    diagnose_predicate(thy, comp, inst, level+1)
                for comp in concls:
                    diagnose_predicate(thy, comp, inst, level+1)
    else:
        raise AssertionError

def diagnose_query(thy: os_theory.OSTheory,
                   assumes: Iterable[OSTerm], concl: OSTerm,
                   model: Model):
    """Print diagnosis information for a model."""
    for assume in assumes:
        diagnose_predicate(thy, assume, model.data)
    diagnose_predicate(thy, concl, model.data)
