"""Tactics for proof automation.

Tactics defined in this module are intended for writing automation,
rather than being invoked by the user directly.

"""

from collections.abc import Iterable
from queue import Queue

from osverify import os_term
from osverify.os_query import Assumes, Shows, Meta
from osverify.os_term import OSTerm, VarContext, Visitor
from osverify.os_theory import OSTheory
from osverify import os_tactics
from osverify import os_simplify
from osverify.os_tactics import Tactic, ProofState, \
    AbstractProofState, IndexProofState, EmptyProofState, CaseProofState


class ApplyAll(Tactic):
    """Apply all tactics repeatedly.
    
    Assume all tactics return either ProofState, IndexProofState, and
    EmptyProofState. Use equality on proof states to determine whether
    to computation.

    The order on the input list `tacs` is obeyed in the following sense:
    when more than one tactic in `tacs` can be applied to the state, it
    is guaranteed that the first tactic according to order in `tacs` is
    applied.

    Attributes
    ----------
    tacs : tuple[Tactic]
        the list of tactics to apply

    """
    def __init__(self, tacs: Iterable[Tactic]):
        self.tacs: tuple[Tactic] = tuple(tacs)

    def __str__(self):
        return "ApplyAll([%s])" % ", ".join(str(tac) for tac in self.tacs)

    def exec(self, thy: OSTheory, state: ProofState) -> AbstractProofState:
        # We maintain two lists of states, one for states that
        # are known to produce no more states (finished), the other
        # for states that are still to be expanded (to_visit).

        finished: list[ProofState] = list()
        to_visit: Queue[ProofState] = Queue()
        to_visit.put(state)

        while not to_visit.empty():
            # Current state to process
            cur_state = to_visit.get()
            found = False

            # Loop through each tactic, if the tactic can be applied to the
            # state, insert the result into `to_visit` and break out of the
            # loop. If no tactic can be applied, this state is a terminal
            # state, and is put into the `finished` list.
            for tac in self.tacs:
                next_state = tac.exec(thy, cur_state)
                if next_state != cur_state:
                    if isinstance(next_state, ProofState):
                        next_state.check_vars(str(tac))
                        to_visit.put(next_state)
                    elif isinstance(next_state, IndexProofState):
                        for state in next_state.cases:
                            state.check_vars(str(tac))
                            to_visit.put(state)
                    elif isinstance(next_state, EmptyProofState):
                        pass
                    elif isinstance(next_state, CaseProofState):
                        for _, _, state in next_state.cases:
                            state.check_vars(str(tac))
                            to_visit.put(state)
                    else:
                        raise NotImplementedError(f"ApplyAll: tactic returned {type(next_state)}")
                    found = True
                    break
            if not found:
                finished.append(cur_state)

        if len(finished) == 0:
            return EmptyProofState()
        elif len(finished) == 1:
            return finished[0]
        else:
            return IndexProofState(finished)


class ApplySeq(Tactic):
    """Apply all tactics in sequence.
    
    Assume all tactics return either ProofState, EmptyState or
    IndexProofState. Apply each tactic **once** to each state, in the
    order of the input list `tacs`.

    Attributes
    ----------
    tacs : tuple[Tactic]
        the list of tactics to apply

    """
    def __init__(self, tacs: Iterable[Tactic]):
        self.tacs: tuple[Tactic] = tuple(tacs)

    def exec(self, thy: OSTheory, state: ProofState) -> AbstractProofState:
        cur_states: list[ProofState] = [state]
        for tac in self.tacs:
            next_states = list()
            # print(f"Applying {tac}, number of states: {len(cur_states)}")
            for cur_state in cur_states:
                next_state = tac.exec(thy, cur_state)
                if isinstance(next_state, ProofState):
                    next_states.append(next_state)
                elif isinstance(next_state, IndexProofState):
                    next_states.extend(next_state.cases)
                elif isinstance(next_state, EmptyProofState):
                    pass
                else:
                    raise NotImplementedError(f"ApplySeq: tactic returned {type(next_state)}")
            cur_states = next_states
        if len(cur_states) == 0:
            return EmptyProofState()
        elif len(cur_states) == 1:
            return cur_states[0]
        else:
            return IndexProofState(cur_states)


class ProcessExists(Tactic):
    """Extract variable for exists expressions that don't have bound variables.

    For each expression `exists v, body`, which is free in the current
    context, declare a fresh variable v0 for v, then replace the
    expression by body[v0/v].

    """
    def exec(self, thy: OSTheory, state: ProofState) -> ProofState:
        var_ctxt = state.get_var_context()
        assumes = []
        new_vars = []
        for assume in state.assumes:
            if os_term.is_exists(assume.prop):
                new_var, body, _ = os_term.strip_exists(var_ctxt, assume.prop)
                new_vars.extend(new_var)
                assumes.append(Assumes(
                    body,
                    generation=assume.generation,
                    conds=assume.conds,
                    meta=Meta(parent=assume, initial_form=body, new_var=new_vars)))
            else:
                assumes.append(assume)

        if new_vars:
            return ProofState(
                type_params=state.type_params,
                fixes=state.fixes + tuple(new_vars),
                assumes=assumes,
                concl=state.concl,
                graph=state.graph
            )

        return state


class VisitSeqLiteral(Visitor):
    """Collect all exists expressions that are free in context."""
    def __init__(self, var_ctxt: VarContext):
        self.var_ctxt = var_ctxt.clone()
        self.collector: list[OSTerm] = list()

    def visit(self, var_ctxt: VarContext, t: OSTerm):
        if isinstance(t, os_term.SeqLiteral):
            if t not in self.collector:
                self.collector.append(t)


class ProcessSeqLiteral(Tactic):
    """Replace SeqLiteral with an equivalent variable and add some formula.

    - [] -> seq_length(l) == 0
    - [a, b, c] -> seq_length(l) == 3 && seq_index(0, l) == a &&
                   seq_index(1, l) == b && seq_index(2, l) == c

    """
    def exec(self, thy: OSTheory, state: ProofState) -> ProofState:
        var_ctxt = state.get_var_context()
        visitor = VisitSeqLiteral(var_ctxt)
        state.traverse(visitor)

        for literal_val in visitor.collector:
            assert isinstance(literal_val, os_term.SeqLiteral)
            new_var = var_ctxt.variant_var(os_term.OSVar('l', type=literal_val.type))

            transformer = os_simplify.ReplaceTerm(literal_val, new_var)
            assumes: list[Assumes] = list()

            # Add length formula
            assumes.append(Assumes(
                os_term.eq(os_term.seq_length(new_var), os_term.integer(len(literal_val.exprs))),
                generation=0,
                conds=tuple()))
            
            # Add equality formula
            for i, expr in enumerate(literal_val.exprs):
                assumes.append(Assumes(
                    os_term.eq(os_term.seq_index(os_term.integer(i), new_var), expr),
                    generation=0,
                    conds=tuple()))
            for assume in state.assumes:
                new_assume = assume.prop.transform(var_ctxt, transformer)
                assumes.append(Assumes(new_assume, name=assume.name, generation=assume.generation,
                                       conds=assume.conds))
            new_concl = Shows(state.concl.prop.transform(var_ctxt, transformer))

            return ProofState(
                type_params=state.type_params,
                fixes=tuple(list(state.fixes) + [new_var]),
                assumes=assumes,
                concl=new_concl,
                graph=state.graph
            )

        return state


class VisitLet(Visitor):
    """Collect all let expressions that are free in context."""
    def __init__(self, var_ctxt: VarContext):
        self.var_ctxt = var_ctxt.clone()
        self.collector: list[OSTerm] = list()

    def visit(self, var_ctxt: VarContext, t: OSTerm):
        if isinstance(t, os_term.OSLet) and self.var_ctxt.is_free(t.expr):
            if t not in self.collector:
                self.collector.append(t)

class ProcessLet(Tactic):
    """Extract variable for let expressions that don't have bound variables.

    For each expression `let v = expr in body`, declare a fresh variable v0
    for v, then replace the expression by body[v0/v]. 

    """
    def exec(self, thy: OSTheory, state: ProofState) -> ProofState:
        var_ctxt = state.get_var_context()
        assumes = []
        new_vars = []
        for assume in state.assumes:
            if isinstance(assume.prop, os_term.OSLet):
                var = os_term.OSVar(assume.prop.var_name, type=assume.prop.expr.type)
                new_var = var_ctxt.variant_var(var)
                inst = {var.name: new_var}

                # Rename bound variable in let_val from var to new_var
                body = assume.prop.body.subst(inst)

                var_ctxt.add_var_decl(new_var.name, new_var.type)
                eq_rule = os_term.eq(new_var, assume.prop.expr)
                new_vars.append(new_var)
                assumes.append(Assumes(eq_rule, generation=0, conds=tuple(),
                                       meta=Meta(initial_form=eq_rule, parent=assume, new_var=[new_var])))
                assumes.append(Assumes(body, name=assume.name, generation=assume.generation,
                                       conds=assume.conds, meta=assume.meta))
            else:
                assumes.append(assume)

        if new_vars:
            return ProofState(
                type_params=state.type_params,
                fixes=state.fixes + tuple(new_vars),
                assumes=assumes,
                concl=state.concl,
                graph=state.graph
            )

        return state

class SplitConjAuto(Tactic):
    """Automatic version of SplitConj.
    
    Find assumptions of the form `A1 && A2 && ... && An`, and replace
    them by n assumptions `A1`, ..., `An`.

    Meta information:
    - The parent of each `Ai` is the original assumption.

    """
    def exec(self, thy: OSTheory, state: ProofState) -> ProofState:
        assumes = list()
        for assume in state.assumes:
            if os_term.is_conj(assume.prop):
                conjs = os_term.split_conj(assume.prop)
                for conj in conjs:
                    assumes.append(Assumes(conj, generation=assume.generation,
                                           conds=assume.conds,
                                           meta=Meta(initial_form=conj, parent=assume)))
            else:
                assumes.append(Assumes(assume.prop, name=assume.name,
                                       generation=assume.generation,
                                       conds=assume.conds, meta=assume.meta))
        return ProofState(
            type_params=state.type_params,
            fixes=state.fixes,
            assumes=assumes,
            concl=state.concl,
            graph=state.graph
        )
    
class SplitGoalAuto(Tactic):
    """Automatic version of SplitGoal.
    
    If the goal This results in an IndexProofState, where each index corresponds to
    one of the conjuncts.
    
    """
    def __init__(self):
        pass

    def exec(self, thy: OSTheory, state: ProofState) -> AbstractProofState:
        imps = os_term.strip_implies_gen(state.concl.prop)
        forall_imps = list(filter(lambda p: isinstance(p[1], os_term.OSQuant), imps))
        if len(imps) > 1 and len(forall_imps) > 0:
            other_imps = list(filter(lambda p: not isinstance(p[1], os_term.OSQuant), imps))
            cases = []
            if len(other_imps) > 0:
                cases.append(os_term.list_implies_gen(other_imps))
            for As, C in forall_imps:
                cases.append(os_term.list_implies(As, C))

            new_states = []
            for case in cases:
                new_states.append(ProofState(
                    type_params=state.type_params,
                    fixes=state.fixes,
                    assumes=state.assumes,
                    concl=Shows(case, meta=Meta(initial_form=case, parent=state.concl)),
                    graph=state.graph
                ))
            return IndexProofState(new_states)
        else:
            return state

class IntrosAuto(Tactic):
    """Automatic version of Intros."""
    def __init__(self):
        pass

    def exec(self, thy: OSTheory, state: ProofState) -> ProofState:
        if not (os_term.is_forall(state.concl.prop) or os_term.is_implies(state.concl.prop)):
            return state
        
        if os_term.is_implies(state.concl.prop):
            As, C = os_term.strip_implies(state.concl.prop)
            As_t = [Assumes(assum, generation=0, conds=tuple()) for assum in As]
            return ProofState(
                type_params=state.type_params,
                fixes=state.fixes,
                assumes=state.assumes + tuple(As_t),
                concl=Shows(C, meta=Meta(parent=state.concl, initial_form=C)),
                graph=state.graph
            )
        else:
            var_ctxt = state.get_var_context()
            new_vars, body, _ = os_term.strip_forall(var_ctxt, state.concl.prop)
            As, C = os_term.strip_implies(body)
            As_t = [Assumes(assum, generation=0, conds=tuple()) for assum in As]
            return ProofState(
                type_params=state.type_params,
                fixes=tuple(state.fixes + new_vars),
                assumes=state.assumes + tuple(As_t),
                concl=Shows(C, meta=Meta(parent=state.concl, initial_form=C,
                                        new_var=new_vars)),
                graph=state.graph
            )

def SimplifySeqMap() -> Tactic:
    """Simplify all sequence/map related operations once."""
    return ApplySeq([
        os_tactics.Rewrite("seq_equals"),
        os_tactics.Rewrite("map_equals"),
    ])

class ProcessExistsGoal(Tactic):
    """Given goal of the form `exists x. P(x)`, add fact `forall x. !P(x)`
    and change the goal to false.
    
    """
    def exec(self, thy: OSTheory, state: ProofState) -> ProofState:
        concl = state.concl.prop
        if not (isinstance(concl, os_term.OSQuant) and concl.quantifier == "exists"):
            return state
        
        assumes = list(state.assumes)
        assum = os_term.OSQuant("forall", concl.params, os_term.get_negation(concl.body))
        assumes.append(Assumes(
            assum, generation=0, conds=tuple(),
            meta=Meta(parent=state.concl, initial_form=assum, contra=True)))
        return ProofState(
            type_params=state.type_params,
            fixes=state.fixes,
            assumes=assumes,
            concl=Shows(os_term.false),
            graph=state.graph
        )
