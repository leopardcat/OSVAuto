"""Theory of sequences."""

from typing import Iterable

from osverify import os_struct
from osverify.os_struct import is_seq_type
from osverify import os_term
from osverify.os_term import OSTerm, OSVar, VarContext, Visitor, dest_index
from osverify import os_tactics
from osverify import os_theory
from osverify.os_theory import OSTheory
from osverify.os_query import Assumes, Meta
from osverify.os_tactics import EmptyProofState, ProofState, Tactic
from osverify import os_simplify
from osverify import auto_tactics
from osverify.auto_tactics import ApplyAll
from osverify.graph import ClassificationGraph, QuantifierNode, \
    GraphNode, SeqNode, MapNode, ConditionalTerm, filter_cond


def validity_check(thy: OSTheory, state: ProofState) -> bool:
    """Check basic validity conditions on the state."""
    return True

class RewriteDefineSeq(Tactic):
    """Perform rewrite of definitional equations.
     
    We apply all definitions `v = t`, where `v` is an atomic term.
    Note this is an extension of the rule in the original paper,
    which assumes `v` is a variable, and only considers `Seq` type.
    
    """
    def __str__(self):
        return "RewriteDefineSeq()"

    def exec(self, thy: OSTheory, state: ProofState) -> ProofState:
        # First find the list of assumptions to rewrite
        define_eqs: list[str] = []
        for assume in state.assumes:
            if os_theory.is_defining_eq(thy, assume.prop):
                define_eqs.append(assume.name)

        for assume_name in define_eqs:
            if os_theory.is_defining_eq(thy, state.assume_map[assume_name]):
                state = os_tactics.RewriteDefine(assume_name).exec(thy, state)

        return state


def is_free(idx_vars: list[OSVar], t: OSTerm) -> bool:
    """Return whether t does not contain any index variable."""
    _, vars = t.get_vars()
    for var in vars:
        if var in idx_vars:
            return False
    return True

def is_index_var(idx_vars: list[OSVar], t: OSTerm) -> bool:
    """Determine whether `t` is an index variable among `idx_vars`.
    
    The basic case is where `t` directly belongs to `idx_vars`.
    A special case is where `t` has form `int(t')`, where `t'`
    belongs to `idx_vars`. 

    """
    if isinstance(t, OSVar) and t in idx_vars:
        return True
    if isinstance(t, os_term.OSFun) and t.func_name == "int" and \
       is_index_var(idx_vars, t.args[0]):
        return True
    return False

def dest_index_var(t: OSTerm) -> OSVar:
    """Deconstruct indes variable.
    
    If input `t` is a variable, return itself. Otherwise, `t` must
    have form int(t').
    
    """
    if isinstance(t, OSVar):
        return t
    if isinstance(t, os_term.OSFun) and t.func_name == "int":
        return dest_index_var(t.args[0])
    raise AssertionError("dest_index_var: %s" % t)


class VisitIndex(Visitor):
    """Look for terms of the form `seq_index(i, t)`."""
    def __init__(self):
        self.collector = list()

    def visit(self, var_ctxt: VarContext, t: OSTerm):
        if os_term.is_fun(t, "seq_index") and t not in self.collector:
            self.collector.append(t)

class VisitGet(Visitor):
    """Look for terms of the form `get(key, m)`."""
    def __init__(self):
        self.collector = list()

    def visit(self, var_ctxt: VarContext, t: OSTerm):
        if os_term.is_fun(t, "get") or os_term.is_fun(t, "indom"):
            if t not in self.collector:
                self.collector.append(t)

def is_shifted_index(idx_vars: list[OSVar], t: OSTerm) -> bool:
    """Determine whether `t` is shifted from one of `idx_vars`.
    
    There are three cases for returning true:
    - `t = i`, where `i` in `idx_vars`
    - `t = i + a`, where `i` in `idx_vars`
    - `t = i - a`, where `i` in `idx_vars`

    """
    return is_index_var(idx_vars, t) or \
        (os_term.is_plus(t) and is_shifted_index(idx_vars, t.args[0]) and
         is_free(idx_vars, t.args[1])) or \
        (os_term.is_minus(t) and is_shifted_index(idx_vars, t.args[0]) and
         is_free(idx_vars, t.args[1]))

def dest_shifted_index(idx_vars: list[OSVar], t: OSTerm) -> tuple[OSVar, OSTerm]:
    """Deconstruct shifted index. Assume t is in shifted index form.
    
    The returned results are:
    - `t = i`: return `(i, 0)`
    - `t = i + a`: return `(i, a)`
    - `t = i - a`: return `(i, -a)`

    The returned index is always a variable, and may have integer or
    bitvector type. The returned weight always have integer type.

    """
    if is_index_var(idx_vars, t):
        return dest_index_var(t), os_term.OSNumber(0, os_struct.Int)
    elif os_term.is_plus(t) and is_shifted_index(idx_vars, t.args[0]) and \
         is_free(idx_vars, t.args[1]):
        v, shift = dest_shifted_index(idx_vars, t.args[0])
        return v, os_term.get_plus(shift, t.args[1])
    elif os_term.is_minus(t) and is_shifted_index(idx_vars, t.args[0]) and \
         is_free(idx_vars, t.args[1]):
        v, shift = dest_shifted_index(idx_vars, t.args[0])
        return v, os_term.get_minus(shift, t.args[1])
    else:
        raise AssertionError(f"dest_shifted_index: {t}")

def is_pattern_index(idx_vars: list[OSVar], t: OSTerm) -> bool:
    """Determine whether `t` is more general form of index."""
    _, vars = t.get_vars()
    # Test if there is a unique variable in t that intersects idx_vars
    common_vars = [var for var in vars if var in idx_vars]
    return len(common_vars) == 1

def dest_pattern_index(idx_vars: list[OSVar], t: OSTerm) -> tuple[OSVar, OSTerm]:
    """Deconstruct more general form of index."""
    _, vars = t.get_vars()
    common_vars = [var for var in vars if var in idx_vars]
    if len(common_vars) == 1:
        return common_vars[0], t.make_schematic(tuple(), common_vars)
    else:
        raise AssertionError(f"dest_pattern_index: {t}")

def add_for_single_inequality(
        graph: ClassificationGraph, assume: Assumes,
        idx_vars: list[OSVar], t: OSTerm):
    """Helper function for classification.

    For each inequality of the form `i + n <= m` or `m <= i + n`,
    where `i` is an index variable and m, n contain only free
    variables, add `m - n` to index_inst of `i`.

    """
    # For conjunctions, process each conjunct
    if os_term.is_conj(t):
        conjs = os_term.split_conj(t)
        for conj in conjs:
            add_for_single_inequality(graph, assume, idx_vars, conj)
        return

    if not (isinstance(t, os_term.OSOp) and t.op in ('<=', '>=', '<', '>', '==', '!=')) and \
        os_struct.is_num_type(t.args[0].type):
        return

    # If both sides of inequality are bitvectors, add `int` at front
    if os_struct.is_bv_type(t.args[0].type):
        add_for_single_inequality(graph, assume, idx_vars,
                                  os_term.OSOp(t.op, os_term.convert_int(t.args[0]),
                                               os_term.convert_int(t.args[1])))
        return

    # Now we made sure t is a comparison between integers
    if os_term.is_less_eq(t) and \
        is_shifted_index(idx_vars, t.lhs) and \
        is_free(idx_vars, t.rhs):
        # i + n <= m
        i, n = dest_shifted_index(idx_vars, t.lhs)
        graph.add_index_inst(
            QuantifierNode(assume.name, i),
            os_term.get_minus(t.rhs, n)
        )
    elif os_term.is_less_eq(t) and \
        is_free(idx_vars, t.lhs) and \
        is_shifted_index(idx_vars, t.rhs):
        # m <= i + n
        i, n = dest_shifted_index(idx_vars, t.rhs)
        graph.add_index_inst(
            QuantifierNode(assume.name, i),
            os_term.get_minus(t.lhs, n)
        )
    elif os_term.is_greater_eq(t):
        add_for_single_inequality(graph, assume, idx_vars,
                                  os_term.less_eq(t.rhs, t.lhs))
    elif os_term.is_less(t):
        # a < b ==> a + 1 <= b
        add_for_single_inequality(
            graph, assume, idx_vars,
            os_term.less_eq(os_term.get_plus(t.lhs, os_term.int_one), t.rhs))
    elif os_term.is_greater(t):
        # a > b ==> b + 1 <= a
        add_for_single_inequality(
            graph, assume, idx_vars,
            os_term.less_eq(os_term.get_plus(t.rhs, os_term.int_one), t.lhs))
    elif os_term.is_eq(t):
        # i + n == m, divide into two inequalities
        add_for_single_inequality(graph, assume, idx_vars,
                                  os_term.less_eq(t.lhs, t.rhs))
        add_for_single_inequality(graph, assume, idx_vars,
                                  os_term.less_eq(t.rhs, t.lhs))
    elif os_term.is_diseq(t):
        pass

class VisitIndexEq(Visitor):
    """Collect terms of the form i + n == m or n == i + m, where i is
    an index variable.
    
    """
    def __init__(self, var_ctxt: VarContext, idx_vars: Iterable[OSVar]):
        self.var_ctxt = var_ctxt.clone()
        self.idx_vars = tuple(idx_vars)
        self.collector: list[OSTerm] = list()

    def visit(self, var_ctxt: VarContext, t: OSTerm):
        if not (self.var_ctxt.is_free(t) and os_term.is_eq(t)):
            return

        if is_shifted_index(self.idx_vars, t.lhs) and is_free(self.idx_vars, t.rhs):
            # Case i + n == m
            if t not in self.collector:
                self.collector.append(t)
        if is_free(self.idx_vars, t.lhs) and is_shifted_index(self.idx_vars, t.rhs):
            # Case n == i + m
            if t not in self.collector:
                self.collector.append(t)

def add_for_single_equality(
        graph: ClassificationGraph, assume: Assumes,
        idx_vars: list[OSVar], t: OSTerm):
    """For each equality of the form `i + n == m or `m == i + n`,
    add index_inst for variable i.
    
    """
    if not os_term.is_eq(t):
        raise AssertionError(f"add_for_single_equality: {t}")

    if is_shifted_index(idx_vars, t.lhs) and is_free(idx_vars, t.rhs):
        # i + n == m
        i, n = dest_shifted_index(idx_vars, t.lhs)
        graph.add_index_inst(
            QuantifierNode(assume.name, i),
            os_term.get_minus(t.rhs, n)
        )
    elif is_free(idx_vars, t.lhs) and is_shifted_index(idx_vars, t.rhs):
        # m == i + n
        i, n = dest_shifted_index(idx_vars, t.rhs)
        graph.add_index_inst(
            QuantifierNode(assume.name, i),
            os_term.get_minus(t.lhs, n)
        )
    else:
        raise AssertionError(f"add_for_single_equality: {t}")

class VisitAtomic(Visitor):
    """Look for terms of Seq or Map type that are free and atomic."""
    def __init__(self, var_ctxt: VarContext):
        self.var_ctxt = var_ctxt.clone()
        self.collector: list[OSTerm] = list()

    def visit(self, var_ctxt: VarContext, t: OSTerm):
        if is_seq_type(t.type) or os_struct.is_map_type(t.type):
            if not os_term.is_atomic_term(t):
                if is_seq_type(t.type):
                    raise AssertionError(f"Non-atomic sequence term {t}")
                else:
                    raise AssertionError(f"Non-atomic map term {t}")
            if not self.var_ctxt.is_free(t):
                return  # do not add free terms, handled later in VisitIndex
            if t not in self.collector:
                self.collector.append(t)

class VisitNonAtomic(Visitor):
    """Look for terms of Seq or Map type that are *not* atomic."""
    def __init__(self, var_ctxt: VarContext):
        self.var_ctxt = var_ctxt.clone()
        self.collector: list[OSTerm] = list()

    def visit(self, var_ctxt: VarContext, t: OSTerm):
        if (is_seq_type(t.type) or os_struct.is_map_type(t.type)) and \
            not os_term.is_atomic_term(t):
            if t not in self.collector:
                self.collector.append(t)

def apply_inst(graph: ClassificationGraph,
               inst_map: dict[QuantifierNode, list[ConditionalTerm]],
               state: ProofState) -> ProofState:
    """Apply instantiations computed in the previous stage.
    
    This function returns a new state, where each quantified
    assumption is replaced by concrete instantiations.

    """
    var_ctxt = state.get_var_context()
    assumes = []
    for assume in state.assumes:
        if not os_term.is_forall(assume.prop):
            assumes.append(assume)
        else:
            const_facts = os_simplify.extract_const_fact(var_ctxt, assume.prop)
            if const_facts != os_term.true:
                assumes.append(Assumes(const_facts, generation=assume.generation,
                                       conds=assume.conds,
                                       meta=Meta(initial_form=const_facts, parent=assume)))

    # For each instantiation in inst_map, add the instantiated version
    # of assumption.
    for node, insts in inst_map.items():
        body = graph.get_term_map(node)

        for ct in insts:
            if os_struct.is_bv_type(node.var.type) and ct.t.type == os_struct.Int:
                # Convert integer to bitvector
                new_inst = os_term.convert_bitvector(ct.t, node.var.type)
            else:
                new_inst = ct.t
            assume_inst = body.subst({node.var.name: new_inst}).transform(
                var_ctxt, os_simplify.SimplifyArith())
            parent = graph.get_assume_map(node)
            if os_term.is_forall(body):
                new_gen = ct.generation
            else:
                new_gen = ct.generation + 1
            new_assume = Assumes(assume_inst,
                                 generation=new_gen,
                                 conds=ct.conds,
                                 meta=Meta(initial_form=assume_inst, parent=parent,
                                           quant_inst=[(node.var.name, new_inst)]))
            assumes.append(new_assume)

    return ProofState(
        type_params=state.type_params,
        fixes=state.fixes,
        assumes=assumes,
        concl=state.concl,
        graph=state.graph
    )


def visit_index_with_cond(var_ctxt: VarContext, t: OSTerm, generation: int,
                          init_conds: tuple[OSTerm], graph: ClassificationGraph,
                          new_insts: dict[GraphNode, list[ConditionalTerm]]):
    """Obtain list of seq_index, get and indom subterms of the given
    term, where each subterm keep tracks of the list of conditions
    it is in.

    Parameters
    ----------
    graph : ClassificationGraph
        classification graph containing mapping of existing conditional terms.
    new_insts : dict[OSTerm, ConditionalTerm]
        mapping of new conditional terms, where key is the sequence/map.
    
    """
    # Current list of conditions
    conds: list[OSTerm] = list(init_conds)

    # Keep a copy of original variable context
    old_var_ctxt = var_ctxt.clone()

    def rec(t: OSTerm):
        if isinstance(t, (os_term.OSVar, os_term.OSNumber)):
            pass
        elif os_term.is_implies(t):
            assum, concl = t.args
            rec(assum)
            conds.append(assum)
            rec(concl)
            del conds[-1]
        elif os_term.is_ite(t):
            cond, t1, t2 = t.args
            rec(cond)
            conds.append(cond)
            rec(t1)
            del conds[-1]
            conds.append(os_term.get_negation(cond))
            rec(t2)
            del conds[-1]
        elif isinstance(t, os_term.OSFun):
            for arg in t.args:
                rec(arg)
            if t.func_name in ("seq_index", "get", "indom"):
                if os_term.is_fun(t, "seq_index"):
                    i, xs = dest_index(t)
                    if not old_var_ctxt.is_free(xs):
                        return
                    node = SeqNode(xs)
                    if node not in new_insts:
                        new_insts[node] = list()
                    if not old_var_ctxt.is_free(t):
                        return
                    ct = ConditionalTerm(
                        filter(lambda cond: old_var_ctxt.is_free(cond) and filter_cond(cond), conds),
                        generation, i)
                    old_insts = graph.get_all_node_insts(node)
                    for old_ct in old_insts:
                        if old_ct.shadows(ct):
                            return
                    for old_ct in new_insts[node]:
                        if old_ct.shadows(ct):
                            return
                    new_insts[node].append(ct)
                else:  # get or indom case
                    k, map = t.args
                    if not old_var_ctxt.is_free(map):
                        return
                    node = MapNode(map)
                    if node not in new_insts:
                        new_insts[node] = list()
                    if not old_var_ctxt.is_free(t):
                        return
                    ct = ConditionalTerm(
                        filter(lambda cond: old_var_ctxt.is_free(cond) and filter_cond(cond), conds),
                        generation, k)
                    old_insts = graph.get_all_node_insts(node)
                    for old_ct in old_insts:
                        if old_ct.shadows(ct):
                            return
                    for old_ct in new_insts[node]:
                        if old_ct.shadows(ct):
                            return
                    new_insts[node].append(ct)
        elif isinstance(t, os_term.OSOp):
            for arg in t.args:
                rec(arg)
        elif isinstance(t, os_term.FieldGet):
            rec(t.expr)
        elif isinstance(t, os_term.OSQuant):
            new_vars = var_ctxt.variant_vars(t.params)
            body_inst = dict()
            for bound_var, new_var in zip(t.params, new_vars):
                var_ctxt.add_var_decl(new_var.name, new_var.type)
                body_inst[bound_var.name] = new_var
            rec(t.body.subst(body_inst))
            for new_var in new_vars:
                var_ctxt.del_var_decl(new_var.name)
        else:
            raise NotImplementedError(f"visit_index_with_cond: {t}")

    rec(t)


class SolveInst(Tactic):
    """Implementation of quantifier instantiation."""
    def __init__(self, *, verbose=False):
        self.verbose = verbose

    def exec(self, thy: OSTheory, state: ProofState) -> ProofState:
        var_ctxt = state.get_var_context()

        if state.graph is not None and state.graph.frame > 5:
            raise AssertionError("Maximum number of frames reached")

        # Push a new frame of classification graph
        state.graph = ClassificationGraph(thy, parent=state.graph)

        if self.verbose:
            print(f"# Current state (frame {state.graph.frame}):")
            # print(state)
            print()

        # Add basic conditions
        for assume in state.assumes:
            if not os_theory.is_defining_eq(thy, assume.prop):
                state.graph.add_basic_conds(assume.prop)
        if state.graph.check_basic_conds():
            return EmptyProofState()

        # Add nodes corresponding to sequences and maps. We skip those
        # sequences and maps that defined in terms of others.
        new_insts: dict[GraphNode, list[ConditionalTerm]] = dict()
        for assume in state.assumes:
            if assume.generation > 1:
                continue
            if not os_theory.is_defining_eq(thy, assume.prop):
                visit_index_with_cond(var_ctxt, assume.prop, assume.generation, assume.conds, state.graph, new_insts)
        visit_index_with_cond(var_ctxt, state.concl.prop, 0, tuple(), state.graph, new_insts)

        # Add node for each sequence and map
        for node in new_insts:
            state.graph.add_node(node)
    
        # Process each assumption
        for assume in state.assumes:
            if not os_term.is_forall(assume.prop):
                continue
            if assume.generation > 1:
                continue

            var, body, var_ctxt2 = os_term.strip_forall1(var_ctxt, assume.prop)

            # Add variables corresponding to bound variable
            state.graph.add_node(QuantifierNode(assume.name, var))
            state.graph.add_term_map(assume, var, body)

            # Add edge for each appearance of sequence or map index
            body_insts: dict[GraphNode, list[ConditionalTerm]] = dict()
            visit_index_with_cond(var_ctxt2, body, assume.generation, assume.conds, state.graph, body_insts)
            for node in body_insts:
                if isinstance(node, SeqNode):
                    if not var_ctxt.is_free(node.seq_t):
                        continue
                    if node not in state.graph.get_all_nodes():
                        raise AssertionError(f"node {node} is missing") 
                    for ct in body_insts[node]:
                        if is_shifted_index([var], ct.t):
                            idx, a = dest_shifted_index([var], ct.t)
                            state.graph.add_edge(
                                source=QuantifierNode(assume.name, idx),
                                target=node,
                                weight=a,
                                generation=assume.generation,
                                conds=ct.conds
                            )
                        elif is_pattern_index([var], ct.t):
                            idx, expr = dest_pattern_index([var], ct.t)
                            state.graph.add_pattern_edge(
                                source=node,
                                target=QuantifierNode(assume.name, idx),
                                expr=expr,
                                generation=assume.generation,
                                conds=ct.conds
                            )
                        elif var_ctxt2.is_free(ct.t):
                            # index is free, this will be considered later
                            pass
                        else:
                            raise AssertionError(f"Unknown index form: {ct.t}")
                elif isinstance(node, MapNode):
                    if not var_ctxt.is_free(node.map_t):
                        continue
                    if node not in state.graph.get_all_nodes():
                        raise AssertionError(f"node {node} is missing") 
                    for ct in body_insts[node]:
                        if is_index_var([var], ct.t):
                            idx = dest_index_var(ct.t)
                            state.graph.add_edge(
                                source=QuantifierNode(assume.name, idx),
                                target=node,
                                weight=os_term.int_zero,
                                generation=assume.generation,
                                conds=ct.conds
                            )
                        elif is_pattern_index([var], ct.t):
                            idx, expr = dest_pattern_index([var], ct.t)
                            state.graph.add_pattern_edge(
                                source=node,
                                target=QuantifierNode(assume.name, idx),
                                expr=expr,
                                generation=assume.generation,
                                conds=ct.conds
                            )
                        elif var_ctxt2.is_free(ct.t):
                            # index is free, this will be considered later
                            pass
                        else:
                            raise AssertionError(f"Unknown index form: {ct.t}")
                else:
                    raise AssertionError

            # Add propagation rules for equality conditions.
            visitor = VisitIndexEq(var_ctxt2, [var])
            body.traverse(var_ctxt2, visitor)
            for t in visitor.collector:
                add_for_single_equality(state.graph, assume, [var], t)

        # Add length(xs) >= 0 to basic condition for each xs
        visitor = os_term.FuncVisitor(var_ctxt, "seq_length")
        state.traverse_skip_defining_eq(thy, visitor)
        for length_t in visitor.collector:
            state.graph.add_basic_conds(os_term.greater_eq(length_t, os_term.int_zero))

        if self.verbose:
            print("# Graph:")
            print(state.graph)
            print()

        # Initial: for each occurrence of `a[n]`, instantiate `n` for `a`
        for node in new_insts:
            for ct in new_insts[node]:
                state.graph.add_node_inst(node, ct.t, ct.generation, cur_conds=ct.conds)

        # For each new quantifier node in the graph, add initial values
        # corresponding to index_inst
        for quant_node, inst_set in state.graph.index_inst.items():
            for inst in inst_set:
                state.graph.add_node_inst(quant_node, inst, 0)

        if self.verbose:
            print("Before propagation")
            state.graph.print_instantiation()

        # Now perform propagation
        state.graph.propagate()

        if self.verbose:
            print("After propagation")
            state.graph.print_instantiation()

        new_insts = state.graph.get_new_insts()

        # Now apply instantiations
        return apply_inst(state.graph, state.graph.get_new_insts(), state)


def SeqAuto(*, verbose=False) -> Tactic:
    return ApplyAll([
        auto_tactics.SplitConjAuto(),
        auto_tactics.ProcessLet(),
        auto_tactics.ProcessExists(),
        auto_tactics.ProcessExistsGoal(),
        auto_tactics.ProcessSeqLiteral(),

        os_tactics.ApplyTransformerThy(os_simplify.Normalize),
        auto_tactics.SimplifySeqMap(),
        RewriteDefineSeq(),

        auto_tactics.SplitGoalAuto(),
        auto_tactics.IntrosAuto(),

        SolveInst(verbose=verbose),
        os_tactics.Auto(verbose=verbose)
    ])
