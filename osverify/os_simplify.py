"""Simplification procedures"""

from typing import Iterable

from osverify import os_struct
from osverify import os_term
from osverify.os_term import OSTerm, VarContext, Transformer
from osverify import os_theory
from osverify.os_theory import OSTheory
from osverify import os_match
from osverify import os_util


class ReplaceTerm(Transformer):
    """Replace lhs by rhs.
    
    Unlike Rewrite, we only rewrite concrete terms here, so no matching
    is necessary.
    
    """
    def __init__(self, lhs: OSTerm, rhs: OSTerm):
        self.lhs = lhs
        self.rhs = rhs

    def visit(self, var_ctxt: VarContext, t: OSTerm) -> OSTerm:
        if t == self.lhs:
            return self.rhs
        else:
            return t

def check_simplify_eqs(var_ctxt: VarContext, define_eqs: list[OSTerm]) -> list[int]:
    """Check a list of defining equations for validity, return
    simplifying order.
    
    """
    def is_prefix(name1: str, idx1: list[OSTerm], name2: str, idx2: list[OSTerm]) -> bool:
        """Determine whether name1, idx1 is a prefix of name2, idx2.
        
        The prefix relation holds only if name1 is a prefix of name2
        and idx1 is a prefix of idx2 (including equality).

        """
        parts1 = name1.split('.')
        parts2 = name2.split('.')
        return len(parts1) <= len(parts2) and parts1 == parts2[:len(parts1)] and \
            len(idx1) <= len(idx2) and idx1 == idx2[:len(idx1)]

    # Check each lhs is an atomic term, and obtain destructed (name, idx) pair
    dest_ts: list[tuple[str, list[OSTerm]]] = []
    for eq in define_eqs:
        if not os_term.is_eq(eq):
            raise AssertionError(f"simplify_defining_eqs: {eq} is not an equation")
        lhs, _ = eq.lhs, eq.rhs
        if not os_term.is_atomic_term(lhs):
            raise AssertionError(f"simplify_defining_eqs: {eq} not a defining equation")
        dest_ts.append(os_term.dest_atomic_term(lhs))

    # Check for prefix conditions
    for i, (name1, idx1) in enumerate(dest_ts):
        for j, (name2, idx2) in enumerate(dest_ts):
            if i != j and is_prefix(name1, idx1, name2, idx2):
                raise AssertionError(
                    f"simplify_defining_eqs: {define_eqs[i].lhs} is a prefix of {define_eqs[j].lhs}")

    # Form graph of containment relations
    graph: dict[int, list[int]] = dict()
    for i in range(len(define_eqs)):
        graph[i] = list()
    for i, eq in enumerate(define_eqs):
        free_ts = os_term.get_all_free_subterms(var_ctxt, eq.rhs)
        for j, eq2 in enumerate(define_eqs):
            if i != j and eq2.lhs in free_ts:
                graph[i].append(j)

    # Perform topological sort on the graph.
    return os_util.topological_sort(graph)

def simplify_define_eqs(var_ctxt: VarContext, define_eqs: list[OSTerm], t: OSTerm) -> OSTerm:
    """Simplify using a list of defining equations.

    The following wellformedness properties should be satisfied by
    the defining equations:

    - The lhs of the defining equations must have type array, map,
      structure, or algebraic datatype.
    - There must not be inclusion relation (including equality) between
      lhs of any two equations. For example, there cannot be two equations
      whose lhs are `m` and `m[0]`, or `a` and `a.x`.
    - There are no cycles in rewriting. That is, consider the graph where
      each node corresponds to lhs of an equation, and edge `s -> t` if
      `t` appears on the right side of equation for `s`, then there is no
      cycle in this graph.

    Since there is no cycle, we can form topological order of the defining
    equations, and use this order for rewriting.
    
    Parameters
    ----------
    var_ctxt : VarContext
        current variable context
    define_eqs : list[OSTerm]
        list of defining equations
    t : OSTerm
        starting term

    """
    # Check the defining equations and perform topological sort
    topo_sort = check_simplify_eqs(var_ctxt, define_eqs)

    # Finally, perform writing
    for idx in topo_sort:
        eq = define_eqs[idx]
        t = t.transform(var_ctxt, ReplaceTerm(eq.lhs, eq.rhs))
    return t


def normalize_field_get(thy: OSTheory, t: OSTerm) -> OSTerm:
    """Compute the normalization of a FieldGet expression.
    
    We consider the following cases:

    - obtaining field of structure literal value.
    - obtaining field of structure update.
    - obtaining field of constructor of algebraic datatype (including id case).
    - obtaining field of if-then-else expression.

    """
    assert isinstance(t, os_term.FieldGet)

    # Structure literal case
    if isinstance(t.expr, os_term.OSStructVal):
        return normalize(thy, t.expr.dict_vals[t.field])
    
    # Structure update case
    elif isinstance(t.expr, os_term.OSStructUpdate):
        if t.field in t.expr.dict_updates:
            return normalize(thy, t.expr.dict_updates[t.field])
        else:
            return normalize(thy, os_term.FieldGet(t.expr.ori_expr, t.field, type=t.type))
    
    # if-then-else
    elif os_term.is_fun(t.expr, "ite"):
        cond, t1, t2 = t.expr.args
        return os_term.ite(cond, normalize(thy, os_term.FieldGet(t1, t.field, type=t.type)),
                           normalize(thy, os_term.FieldGet(t2, t.field, type=t.type)))

    # Datatype constructor case
    elif isinstance(t.expr, os_term.OSFun) and \
            isinstance(t.expr.type, os_struct.OSHLevelType) and \
            t.expr.type.name in thy.datatypes:
        datatype = thy.datatypes[t.expr.type.name]
        if t.expr.func_name in datatype.branch_map:
            branch_id = datatype.get_branch_id(t.expr.func_name)
            if t.field == "id":
                return os_term.OSNumber(branch_id, os_struct.Int)
            else:
                branch = datatype.branches[branch_id]
                for i, (param_name, _) in enumerate(branch.params):
                    if param_name == t.field:
                        return normalize(thy, t.expr.args[i])
                # Known access of a field that does not exist, get default value
                # for the type.
                return os_term.OSFun("default", type=t.type)
        else:
            return t

    else:
        return t

def normalize_eq(thy: OSTheory, t1: OSTerm, t2: OSTerm) -> OSTerm:
    """Compute the normal form of equality.
    
    We consider the following cases:

    - equality between two structures
    - equality between two datatypes
    
    """
    ty = t1.type

    # Structure case
    if isinstance(ty, os_struct.OSStructType):
        struct = thy.structs[ty.name]
        conjs: list[OSTerm] = list()
        for field in struct.fields:
            field_name = field.field_name
            field_ty = thy.get_field_type(ty, field_name)
            conjs.append(normalize_eq(thy,
                normalize_field_get(thy, os_term.FieldGet(t1, field_name, type=field_ty)),
                normalize_field_get(thy, os_term.FieldGet(t2, field_name, type=field_ty))
            ))
        return os_term.list_conj(conjs)

    # Datatype case
    elif isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.datatypes:
        datatype = thy.datatypes[ty.name]

        t1_id = normalize_field_get(thy, os_term.FieldGet(t1, "id", type=os_struct.Int))
        t2_id = normalize_field_get(thy, os_term.FieldGet(t2, "id", type=os_struct.Int))
        
        # Check whether id of at least one side of equality is known
        known_t1, known_t2 = None, None
        if isinstance(t1, os_term.OSFun) and t1.func_name in datatype.branch_map:
            known_t1 = datatype.get_branch_id(t1.func_name)
        elif isinstance(t2, os_term.OSFun) and t2.func_name in datatype.branch_map:
            known_t2 = datatype.get_branch_id(t2.func_name)

        if known_t1 is not None and known_t2 is not None:
            # Both sides are constructors
            if known_t1 == known_t2:
                branch = datatype.branches[known_t1]
                conjs = []
                for i, _ in enumerate(branch.params):
                    conjs.append(normalize_eq(thy, t1.args[i], t2.args[i]))
                return os_term.list_conj(conjs)
            else:
                return os_term.false
        elif known_t1 is not None:
            # Left side is constructor
            conjs = []
            conjs.append(os_term.eq(t2_id, os_term.integer(known_t1)))
            branch = datatype.branches[known_t1]
            for i, (param_name, _) in enumerate(branch.params):
                field_ty = thy.get_field_type(ty, param_name)
                conjs.append(normalize_eq(
                    thy, t1.args[i], normalize_field_get(thy, os_term.FieldGet(t2, param_name, type=field_ty))))
            return os_term.list_conj(conjs)
        elif known_t2 is not None:
            # Right side is constructor
            conjs = []
            conjs.append(os_term.eq(os_term.integer(known_t2), t1_id))
            branch = datatype.branches[known_t2]
            for i, (param_name, _) in enumerate(branch.params):
                field_ty = thy.get_field_type(ty, param_name)
                conjs.append(normalize_eq(
                    thy, normalize_field_get(thy, os_term.FieldGet(t1, param_name, type=field_ty)), t2.args[i]))
            return os_term.list_conj(conjs)
        else:
            # Neither sides are constructors. Enumerate the branches, and
            # construct case for each branch
            conjs = []
            conjs.append(os_term.eq(t1_id, t2_id))
            for i, branch in enumerate(datatype.branches):
                eqs = []
                cond = os_term.eq(t1_id, os_term.integer(i))
                for param_name, _ in branch.params:
                    field_ty = thy.get_field_type(ty, param_name)
                    eqs.append(normalize_eq(
                        thy,
                        normalize_field_get(thy, os_term.FieldGet(t1, param_name, type=field_ty)),
                        normalize_field_get(thy, os_term.FieldGet(t2, param_name, type=field_ty))))
                conjs.append(os_term.implies(cond, os_term.list_conj(eqs)))
            return os_term.list_conj(conjs)
    
    else:
        return os_term.eq(t1, t2)

def normalize_ite(thy: OSTheory, t: OSTerm) -> OSTerm:
    """Normalize an if-then-else expression.
    
    We make the following simplifications:

    - if (true) { t1 } else { t2 }   => t1
    - if (false) { t1 } else { t2 }  => t2
    - if (b) { true } else { false } => b
    - if (b) { t1 } else { true }    => b -> t1
    - if (b) { t1 } else { t1 }      => t1
    - if (v == x) { t[v] } else { t[x] } => t[x]
    - if (x == v) { t[v] } else { t[x] } => t[x]

    """
    assert os_term.is_fun(t, "ite")
    cond, t1, t2 = t.args
    if cond == os_term.true:
        return t1
    elif cond == os_term.false:
        return t2
    elif os_term.is_eq(cond) and cond.lhs == cond.rhs:
        return t1
    elif os_term.is_diseq(cond) and cond.lhs == cond.rhs:
        return t1
    elif t1 == os_term.true and t2 == os_term.false:
        return cond
    elif t2 == os_term.true:
        return os_term.implies(cond, t1)
    elif t1 == t2:
        return t1
    elif os_term.is_eq(cond) and isinstance(cond.lhs, os_term.OSVar) and \
        t1.subst({cond.lhs.name: cond.rhs}) == t2:
        return t2
    elif os_term.is_eq(cond) and isinstance(cond.rhs, os_term.OSVar) and \
        t1.subst({cond.rhs.name: cond.lhs}) == t2:
        return t2
    else:
        # If any component is a quantifier, just rewrite to implies
        imps = os_term.strip_implies_gen(t)
        if any(isinstance(C, os_term.OSQuant) for _, C in imps):
            return os_term.list_implies_gen(imps)
        else:
            return t

def normalize_implies(t1: OSTerm, t2: OSTerm) -> OSTerm:
    """Normalize implication t1 -> t2."""
    if os_term.is_conj(t2):
        # If right side is a conjunction, take out those with quantifiers
        ts2 = os_term.split_conj(t2)
        ts2_n = list(filter(lambda t: not isinstance(t, os_term.OSQuant), ts2))
        ts2_q = list(filter(lambda t: isinstance(t, os_term.OSQuant), ts2))
        if len(ts2_q) > 0:
            res = []
            if len(ts2_n) > 0:
                res.append(os_term.implies(t1, os_term.list_conj(ts2_n)))
            for t2_q in ts2_q:
                res.append(normalize_implies(t1, t2_q))
            return os_term.list_conj(res)
        else:
            return os_term.implies(t1, t2)
    elif isinstance(t2, os_term.OSQuant):
        # a -> exists/forall b, P(b)    to  exists/forall b, a -> P(b)
        body = normalize_implies(t1, t2.body)
        return os_term.OSQuant(t2.quantifier, t2.params, body)
    elif isinstance(t1, os_term.OSQuant):
        # (exists/forall b, P(b)) -> a  to  forall/exists b, P(b) -> a
        body = normalize_implies(t1.body, t2)
        quantifier = 'forall' if t1.quantifier == 'exists' else 'exists'
        return os_term.OSQuant(quantifier, t1.params, body)
    else:
        return os_term.implies(t1, t2)

def normalize_disj(t1: OSTerm, t2: OSTerm) -> OSTerm:
    """Normalize t1 || t2."""
    if isinstance(t2, os_term.OSQuant):
        body = os_term.disj(t1, t2.body)
        return os_term.OSQuant(t2.quantifier, t2.params, body)
    elif isinstance(t1, os_term.OSQuant):
        body = os_term.disj(t1.body, t2)
        return os_term.OSQuant(t1.quantifier, t1.params, body)
    else:
        return os_term.disj(t1, t2)

def normalize_not(t: OSTerm) -> OSTerm:
    """Normalize negation applied to quantifiers."""
    assert isinstance(t, os_term.OSOp) and t.op == "!"

    if isinstance(t.args[0], os_term.OSQuant):
        quantifier = 'forall' if t.args[0].quantifier == 'exists' else 'exists'
        body = os_term.get_negation(t.args[0].body)
        return os_term.OSQuant(quantifier, t.args[0].params, body)
    else:
        return t

def normalize_index(thy: OSTheory, t: OSTerm) -> OSTerm:
    """Normalize terms of form `a[i]`, where `a` is one of the
    sequence operations.
    
    """
    assert os_term.is_fun(t, "seq_index")
    _, xs = os_term.dest_index(t)
    if os_term.is_fun(xs, "seq_append"):
        return normalize(thy, rewrite_thm(thy, "seq_append_index", t))
    elif os_term.is_fun(xs, "seq_cons"):
        return normalize(thy, rewrite_thm(thy, "seq_cons_index", t))
    elif os_term.is_fun(xs, "seq_repeat"):
        return normalize(thy, rewrite_thm(thy, "seq_repeat_index", t))
    elif os_term.is_fun(xs, "seq_slice"):
        return normalize(thy, rewrite_thm(thy, "seq_slice_index", t))
    elif os_term.is_fun(xs, "seq_update"):
        return normalize(thy, rewrite_thm(thy, "seq_update_index", t))
    elif os_term.is_fun(xs, "seq_remove"):
        return normalize(thy, rewrite_thm(thy, "seq_remove_index", t))
    elif os_term.is_fun(xs, "seq_rev"):
        return normalize(thy, rewrite_thm(thy, "seq_rev_index", t))
    elif os_term.is_fun(xs, "ite"):
        return normalize(thy, rewrite_thm(thy, "seq_ite_index", t))
    else:
        return t

def normalize_length(thy: OSTheory, t: OSTerm) -> OSTerm:
    """Normalize terms of the form `|a|`, where `a` is one of the
    sequence operations.
    
    """
    assert os_term.is_fun(t, "seq_length")
    xs = t.args[0]
    if os_term.is_fun(xs, "seq_append"):
        return normalize(thy, rewrite_thm(thy, "seq_append_length", t))
    elif os_term.is_fun(xs, "seq_cons"):
        return normalize(thy, rewrite_thm(thy, "seq_cons_length", t))
    elif os_term.is_fun(xs, "seq_repeat"):
        return normalize(thy, rewrite_thm(thy, "seq_repeat_length", t))
    elif os_term.is_fun(xs, "seq_slice"):
        return normalize(thy, rewrite_thm(thy, "seq_slice_length", t))
    elif os_term.is_fun(xs, "seq_update"):
        return normalize(thy, rewrite_thm(thy, "seq_update_length", t))
    elif os_term.is_fun(xs, "seq_remove"):
        return normalize(thy, rewrite_thm(thy, "seq_remove_length", t))
    elif os_term.is_fun(xs, "seq_rev"):
        return normalize(thy, rewrite_thm(thy, "seq_rev_length", t))
    elif os_term.is_fun(xs, "ite"):
        return normalize(thy, rewrite_thm(thy, "seq_ite_length", t))
    else:
        return t

def normalize_get(thy: OSTheory, t: OSTerm) -> OSTerm:
    """Normalize terms of the form `get(k, m)`, where `m` is one of the
    map operations.
    
    """
    assert os_term.is_fun(t, "get")
    _, m = os_term.dest_map_get(t)
    if os_term.is_fun(m, "updateMap"):
        return normalize(thy, rewrite_thm(thy, "get_update", t))
    elif os_term.is_fun(m, "ite"):
        return normalize(thy, rewrite_thm(thy, "get_ite", t))
    else:
        return t

def normalize_indom(thy: OSTheory, t: OSTerm) -> OSTerm:
    """Normalize terms of the form `indom(k, m)`, where `m` is one of the
    map operations.
    
    """
    assert os_term.is_fun(t, "indom")
    _, m = os_term.dest_map_indom(t)
    if os_term.is_fun(m, "updateMap"):
        return normalize(thy, rewrite_thm(thy, "indom_update", t))
    elif os_term.is_fun(m, "ite"):
        return normalize(thy, rewrite_thm(thy, "indom_ite", t))
    else:
        return t

def normalize(thy: OSTheory, t: OSTerm) -> OSTerm:
    """Compute the normal form with respect to field access and equality
    on structures and datatypes.
    
    """
    if isinstance(t, os_term.FieldGet):
        return normalize_field_get(thy, t)
    elif isinstance(t, os_term.OSLet):
        return normalize(thy, t.body.subst({t.var_name: t.expr}))
    elif isinstance(t, os_term.OSStructUpdateGen):
        return normalize(thy, expand_process_update_gen(thy, t))
    elif isinstance(t, os_term.OSSwitch):
        return normalize(thy, normalize_switch(thy, t))
    elif isinstance(t, os_term.OSQuantIn):
        constraint = t.get_constraint()
        if t.quantifier == "forall":
            return os_term.OSQuant("forall", [t.param], os_term.implies(constraint, t.body))
        elif t.quantifier == "exists":
            return os_term.OSQuant("exists", [t.param], os_term.conj(constraint, t.body))
        else:
            raise AssertionError
    elif os_term.is_eq(t):
        return normalize_eq(thy, t.lhs, t.rhs)
    elif os_term.is_diseq(t):
        return os_term.get_negation(normalize_eq(thy, t.lhs, t.rhs))
    elif os_term.is_implies(t):
        return normalize_implies(t.args[0], t.args[1])
    elif os_term.is_disj(t):
        return normalize_disj(t.args[0], t.args[1])
    elif isinstance(t, os_term.OSOp) and t.op == "!":
        return normalize_not(t)
    elif isinstance(t, os_term.OSFun) and t.func_name in thy.fixps:
        return normalize(thy, rewrite_thm(thy, f"{t.func_name}_def", t))
    elif os_term.is_fun(t, "ite"):
        return normalize_ite(thy, t)
    elif os_term.is_fun(t, "seq_index"):
        return normalize_index(thy, t)
    elif os_term.is_fun(t, "seq_length"):
        return normalize_length(thy, t)
    elif os_term.is_fun(t, "get"):
        return normalize_get(thy, t)
    elif os_term.is_fun(t, "indom"):
        return normalize_indom(thy, t)
    else:
        return t


class Normalize(Transformer):
    """Perform normalization on the term."""
    def __init__(self, thy: OSTheory):
        self.thy = thy

    def visit(self, var_ctxt: VarContext, t: OSTerm) -> OSTerm:
        return normalize(self.thy, t)


def rewrite_def(thy: OSTheory, t: OSTerm) -> OSTerm:
    """Rewrite definition on the given tern."""
    assert isinstance(t, os_term.OSFun) and t.func_name in thy.fixps

    thm_name = t.func_name + "_def"
    eq_th = thy.get_sch_theorem(thm_name)
    tyinst, inst = dict(), dict()
    os_match.match(eq_th.lhs, t, tyinst, inst)
    return eq_th.rhs.subst_type(tyinst).subst(inst)

def rewrite_thm(thy: OSTheory, thm_name: str, t: OSTerm) -> OSTerm:
    """Rewrite using the given theorem."""

    eq_th = thy.get_sch_theorem(thm_name)
    tyinst, inst = dict(), dict()
    os_match.match(eq_th.lhs, t, tyinst, inst)
    return eq_th.rhs.subst_type(tyinst).subst(inst)

class Rewrite(Transformer):
    """Perform rewrite once using given theorem.

    Assume the theorem is already in schematic form. Match the term
    with left side of the theorem, and return the instantiation of the
    right side if a match is found. Otherwise, the rewrite fails and
    the original term t is returned.

    """
    def __init__(self, eq_th: OSTerm):
        assert os_term.is_eq(eq_th), "Rewrite: theorem is not equality."
        self.eq_th = eq_th

    def visit(self, var_ctxt: VarContext, t: OSTerm) -> OSTerm:
        tyinst, inst = dict(), dict()
        if not os_match.match(self.eq_th.lhs, t, tyinst, inst):
            return t
        else:
            return self.eq_th.rhs.subst_type(tyinst).subst(inst)

def RewriteThm(thy: OSTheory, th_name: str) -> Transformer:
    """Perform rewrite once with theorem of given name."""
    if th_name not in thy.theorems:
        raise AssertionError("Rewrite: theorem %s not found" % th_name)
    eq_th = thy.get_sch_theorem(th_name)
    return Rewrite(eq_th)

def rewrite_thms(thy: OSTheory, var_ctxt: VarContext, th_names: Iterable[str], t: OSTerm) -> OSTerm:
    """Perform rewrite using all theorems in the list."""
    transformers = [RewriteThm(thy, th_name) for th_name in th_names]
    while True:
        old_t = t
        for transformer in transformers:
            t = t.transform(var_ctxt, transformer)
        if t == old_t:
            return t

def get_access_expr(thy: OSTheory, ori_expr: OSTerm, gen_field: os_term.GenField) -> OSTerm:
    """Obtain the expression to access the given generalized field."""
    if isinstance(gen_field, os_term.AtomGenField):
        field_ty = thy.get_field_type(ori_expr.type, gen_field.name)
        return os_term.FieldGet(ori_expr, gen_field.name, type=field_ty)
    elif isinstance(gen_field, os_term.IndexGenField):
        base_expr = get_access_expr(thy, ori_expr, gen_field.base)
        base_ty = base_expr.type
        if isinstance(base_ty, os_struct.OSHLevelType) and base_ty.name == "Map":
            _, val_ty = base_ty.params
            return os_term.OSFun("get", gen_field.index, base_expr, type=val_ty)
        elif isinstance(base_ty, os_struct.OSHLevelType) and base_ty.name == "Seq":
            ele_ty = base_ty.params[0]
            return os_term.OSFun("seq_index", gen_field.index, base_expr, type=ele_ty)
        else:
            raise AssertionError("get_access_expr: %s" % base_ty)
    elif isinstance(gen_field, os_term.FieldGetGenField):
        base_expr = get_access_expr(thy, ori_expr, gen_field.base)
        base_ty = base_expr.type
        field_ty = thy.get_field_type(base_ty, gen_field.field)
        return os_term.FieldGet(base_expr, gen_field.field, type=field_ty)
    else:
        raise NotImplementedError("get_access_expr: %s" % type(gen_field))

def expand_process_update_gen(thy: OSTheory, t: os_term.OSStructUpdateGen) -> OSTerm:
    """Expand OSStructUpdateGen terms."""
    if isinstance(t.gen_field, os_term.AtomGenField):
        # Atomic case, access a field
        return os_term.OSStructUpdate(
            t.ori_expr, [os_term.FieldUpdate(t.gen_field.name, t.expr)])

    elif isinstance(t.gen_field, os_term.IndexGenField):
        # Accessing index in Map or Seq
        base_expr = get_access_expr(thy, t.ori_expr, t.gen_field.base)
        base_ty = base_expr.type
        if isinstance(base_ty, os_struct.OSHLevelType) and base_ty.name == "Map":
            t2 = os_term.OSStructUpdateGen(
                t.ori_expr, t.gen_field.base,
                os_term.OSFun("updateMap", t.gen_field.index, t.expr, base_expr, type=base_ty))
        elif isinstance(base_ty, os_struct.OSHLevelType) and base_ty.name == "Seq":
            t2 = os_term.OSStructUpdateGen(
                t.ori_expr, t.gen_field.base,
                os_term.OSFun("seq_update", t.gen_field.index, t.expr, base_expr, type=base_ty))
        else:
            raise AssertionError(f"expand_process_update_gen: {base_ty}")
        return expand_process_update_gen(thy, t2)

    elif isinstance(t.gen_field, os_term.FieldGetGenField):
        # Accessing a field
        base_expr = get_access_expr(thy, t.ori_expr, t.gen_field.base)
        t2 = os_term.OSStructUpdateGen(
            t.ori_expr, t.gen_field.base,
            os_term.OSStructUpdate(base_expr, [os_term.FieldUpdate(t.gen_field.field, t.expr)]))
        return expand_process_update_gen(thy, t2)

    else:
        raise NotImplementedError(f"expand_process_update_gen: {type(t.gen_field)}")

def get_cond_and_inst(thy: OSTheory, pat: OSTerm,
                      switch_expr: OSTerm) -> tuple[list[OSTerm], dict[str, OSTerm]]:
    """Helper function for `normalize_switch`.
    
    Given a pattern, return the list of corresponding conditions
    and instantiations of variables in the pattern (in terms of
    `switch_expr`).
    
    """
    if isinstance(pat, os_term.OSVar):
        # Variable case, simply associate variable with switch_expr
        return [], {pat.name: switch_expr}
    
    elif isinstance(pat, os_term.OSWildcard):
        # Wildcard case
        return [], dict()
    
    elif isinstance(pat, os_term.OSNumber):
        # Constant case
        return [os_term.eq(switch_expr, pat)], dict()
    
    elif isinstance(pat, os_term.OSStructVal):
        # Structure literal, consider each field of the structure
        all_cond = []
        all_inst = dict()
        for field, val in pat.vals:
            field_ty = thy.get_field_type(switch_expr.type, field)
            cond, inst = get_cond_and_inst(
                thy, val, os_term.FieldGet(switch_expr, field, type=field_ty))
            all_cond.extend(cond)
            all_inst.update(inst)
        return all_cond, all_inst
    
    elif isinstance(pat, os_term.OSFun):
        ty = switch_expr.type
        if not (isinstance(ty, os_struct.OSHLevelType) and ty.name in thy.datatypes):
            raise AssertionError(f"simplify_switch: {ty} is not datatype")
        datatype = thy.datatypes[ty.name]

        # Constructor of the pattern
        if pat.func_name not in datatype.branch_map:
            raise AssertionError(
                f"simplify_switch: {pat.func_name} is not a constructor of {ty.name}")

        all_cond = []
        all_inst = dict()

        branch_id = datatype.get_branch_id(pat.func_name)
        id_cond = os_term.eq(os_term.FieldGet(switch_expr, "id", type=os_struct.Int),
                             os_term.OSNumber(branch_id, type=os_struct.Int))
        all_cond.append(id_cond)

        branch = datatype.branches[branch_id]
        for (param, _), pat_arg in zip(branch.params, pat.args):
            field_ty = thy.get_field_type(switch_expr.type, param)
            cond, inst = get_cond_and_inst(
                thy, pat_arg, os_term.FieldGet(switch_expr, param, type=field_ty))
            all_cond.extend(cond)
            all_inst.update(inst)
        return all_cond, all_inst
    
    else:
        raise AssertionError(f"simplify_switch: {type(pat)}")

def normalize_switch(thy: OSTheory, t: OSTerm) -> OSTerm:
    assert isinstance(t, os_term.OSSwitch)
        
    conds, exprs = list(), list()
    for branch in t.branches:
        if isinstance(branch, os_term.OSSwitchBranchCase):
            cond, inst = get_cond_and_inst(thy, branch.pattern, t.switch_expr)
            vars: list[os_term.OSVar] = list()
            for name, val in inst.items():
                vars.append(os_term.OSVar(name, type=val.type))
            expr = branch.expr.subst(inst)
            if not cond:
                exprs.append(expr)
                break
            else:
                conds.append(os_term.list_conj(cond))
                exprs.append(expr)
        elif isinstance(branch, os_term.OSSwitchBranchDefault):
            exprs.append(branch.expr)
            break
        else:
            raise AssertionError
    return os_term.list_ite(conds, exprs)


class SimplifySwitch(Transformer):
    """Simplify switch statement.
    
    This function converts a general switch statement to equivalent
    if-then-else form. Each pattern is converted into a condition
    and a list of instantiations for variables in the pattern (using
    helper function `get_cond_and_inst`).
    
    """
    def __init__(self, thy: OSTheory):
        self.thy = thy

    def visit(self, var_ctxt: VarContext, t: OSTerm) -> OSTerm:
        if not isinstance(t, os_term.OSSwitch):
            return t
        return normalize_switch(self.thy, t)


class SimplifySwitchOnConstructor(Transformer):
    """Simplify switch statements applied to constructors.
    
    This function only performs the obvious rewrites when switch_expr
    is in constructor form, and the switch is in standard form.

    """
    def __init__(self, thy: OSTheory):
        self.thy = thy

    def visit(self, var_ctxt: VarContext, t: OSTerm) -> OSTerm:
        if not isinstance(t, os_term.OSSwitch):
            return t
        if not os_theory.is_standard_switch(self.thy, t):
            return t

        ty = t.switch_expr.type
        assert isinstance(ty, os_struct.OSHLevelType) and ty.name in self.thy.datatypes
        datatype = self.thy.datatypes[ty.name]

        if not isinstance(t.switch_expr, os_term.OSFun):
            return t
        if t.switch_expr.func_name not in datatype.branch_map:
            return t
        for branch in t.branches:
            if isinstance(branch, os_term.OSSwitchBranchCase):
                assert isinstance(branch.pattern, os_term.OSFun)
                if branch.pattern.func_name == t.switch_expr.func_name:
                    inst = dict()
                    for pat_arg, arg in zip(branch.pattern.args, t.switch_expr.args):
                        if isinstance(pat_arg, os_term.OSVar):
                            inst[pat_arg.name] = arg
                    return branch.expr.subst(inst)
            elif isinstance(branch, os_term.OSSwitchBranchDefault):
                return branch.expr
        # Should not reach here
        raise AssertionError

class SimplifyConsts(Transformer):
    """Evaluate operations on constants."""
    def visit(self, var_ctxt: VarContext, t: OSTerm) -> OSTerm:
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

def normalize_arith(t: OSTerm) -> OSTerm:
    """Simplify arithmetic term.
    
    Here we only implement simple functionality, decomposing the term
    into sums of terms.
    
    """
    ty = t.type
    if ty != os_struct.Int:
        raise AssertionError(f"normalize_arith: {t} with type {ty}")
    coeff_map: dict[OSTerm, int] = dict()
    const = 0
    def extract_coeff(t: OSTerm, coeff: int):
        nonlocal const
        if isinstance(t, os_term.OSNumber):
            const += t.val * coeff
        elif os_term.is_plus(t):
            extract_coeff(t.lhs, coeff)
            extract_coeff(t.rhs, coeff)
        elif os_term.is_minus(t):
            extract_coeff(t.lhs, coeff)
            extract_coeff(t.rhs, -coeff)
        elif os_term.is_uminus(t):
            extract_coeff(t.args[0], -coeff)
        else:
            if t not in coeff_map:
                coeff_map[t] = 0
            coeff_map[t] += coeff
    extract_coeff(t, 1)
    sorted_keys = sorted(coeff_map.keys(), key=lambda t: str(t))
    res = None
    for key in sorted_keys:
        if coeff_map[key] == 0:
            continue
        if coeff_map[key] == 1:
            sign, cur_t = False, key
        elif coeff_map[key] == -1:
            sign, cur_t = True, key
        elif coeff_map[key] > 0:
            sign, cur_t = False, os_term.OSOp("*", os_term.OSNumber(coeff_map[key], type=key.type), key, type=ty)
        else:
            sign, cur_t = True, os_term.OSOp("*", os_term.OSNumber(-coeff_map[key], type=key.type), key, type=ty)
        if res is None:
            if sign:
                res = os_term.OSOp("-", cur_t, type=ty)
            else:
                res = cur_t
        else:
            if sign:
                res = os_term.OSOp("-", res, cur_t, type=ty)
            else:
                res = os_term.OSOp("+", res, cur_t, type=ty)
    if const == 0:
        if res is None:
            res = os_term.OSNumber(0, type=ty)
        else:
            pass
    elif const < 0:
        if res is None:
            res = os_term.OSNumber(const, type=ty)
        else:
            res = os_term.OSOp("-", res, os_term.OSNumber(-const, type=ty), type=ty)
    else:
        if res is None:
            res = os_term.OSNumber(const, type=ty)
        else:
            res = os_term.OSOp("+", res, os_term.OSNumber(const, type=ty), type=ty)
    return res


class SimplifyArith(Transformer):
    def visit(self, var_ctxt: VarContext, t: OSTerm) -> OSTerm:
        if t.type != os_struct.Int:
            return t
        return normalize_arith(t)


class SimplifyITE(Transformer):
    """Simplify if-then-else expressions.
    
    Given a condition `cond`, perform the following rewrites:
     - if (cond) { t1 } else { t2 } -> t1
     - if (!cond) { t1 } else { t2 } -> t2

    """
    def __init__(self, cond: OSTerm):
        self.cond = cond

    def visit(self, var_ctxt: VarContext, t: OSTerm) -> OSTerm:
        if os_term.is_fun(t, "ite"):
            cond, t1, t2 = t.args
            if cond == self.cond:
                return t1
            elif cond == os_term.get_negation(self.cond):
                return t2
        return t

def extract_const_fact(var_ctxt: VarContext, t: OSTerm) -> OSTerm:
    """Given a forall term, extract the part that does not depend
    on the quantified variable.

    If there are no facts that does not depend on the quantified
    variable, return true.
    
    """
    if not isinstance(t, os_term.OSQuant):
        raise AssertionError("extract_const_fact")
    
    facts: list[tuple[tuple[OSTerm], OSTerm]] = []

    def extract(conds: tuple[OSTerm], t: OSTerm):
        if os_term.is_conj(t):
            t1, t2 = t.args
            extract(conds, t1)
            extract(conds, t2)
        elif os_term.is_implies(t):
            t1, t2 = t.args
            extract(conds + (t1,), t2)
        elif os_term.is_ite(t):
            cond, t1, t2 = t.args
            extract(conds + (cond,), t1)
            extract(conds + (os_term.get_negation(cond),), t2)
        else:
            if var_ctxt.is_free(t) and all(var_ctxt.is_free(cond) for cond in conds):
                facts.append((conds, t))
    
    _, body, _ = os_term.strip_forall1(var_ctxt, t)
    extract(tuple(), body)
    
    # Now build up facts
    return os_term.list_conj(
        os_term.list_implies(conds, t) for (conds, t) in facts)
