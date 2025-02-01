from typing import Iterable, Callable
import json

from osverify import os_util
from osverify import os_struct
from osverify import os_theory
from osverify.os_theory import OSTheory
from osverify import os_query
from osverify.os_query import Assumes, Shows
from osverify.os_proofstate import AbstractProofState, ProofState, CaseProofState, \
    IndexProofState, EmptyProofState, AssertProofState
from osverify import os_term
from osverify.os_term import OSTerm, OSVar, Transformer
from osverify import os_match
from osverify.os_util import indent
from osverify import os_simplify
from osverify import os_z3wrapper
from osverify.graph import ClassificationGraph


class TacticException(Exception):
    """Exception encountered when executing a tactic."""
    pass


class Tactic:
    """Base class of tactics.
    
    Execution of a tactic results in a list of new proof states, all of
    which need to be proved. If the returned list is empty, the goal is
    resolved.

    If the tactic cannot be executed on the given ProofState, it should be
    indicated by raising TacticException.

    """
    def exec(self, thy: OSTheory, state: ProofState) -> AbstractProofState:
        """Execute the tactic on the given state."""
        raise NotImplementedError


class TacticBranch:
    """Base class for tactic branches."""
    
    # Tactic for the branch
    tactic : Tactic


class TacticBranchCase(TacticBranch):
    """Tactic branch corresponding to branches of a datatype.
    
    Each case corresponds to a branch of the datatype. The list of
    parameters introduced by the branch is recorded, and may be used
    in the ensuing tactic.

    One special case is case analysis on a boolean expression. Then
    the two branches are "true" and "false", respectively.
    
    """
    def __init__(self, constr_name: str, params: Iterable[str], tactic: Tactic):
        self.constr_name = constr_name
        self.params = tuple(params)
        self.tactic = tactic

    def __str__(self):
        if self.params:
            return "case %s(%s): %s;" % (self.constr_name, ", ".join(self.params), self.tactic)
        else:
            return "case %s: %s;" % (self.constr_name, self.tactic)

    def __repr__(self):
        if self.params:
            return "TacticBranchCase(%s, [%s], %s)" % (self.constr_name, ", ".join(self.params), repr(self.tactic))
        else:
            return "TacticBranchCase(%s, %s)" % (self.constr_name, repr(self.tactic))


class TacticBranchIndex(TacticBranch):
    """Tactic branch corresponding to index.
    
    Indices are 1-based, numbering the subgoals that result from
    a tactic application other than Cases and Induction.
    
    """
    def __init__(self, index: int, tactic: Tactic):
        self.index = index
        self.tactic = tactic

    def __str__(self):
        return "%s: %s;" % (self.index, self.tactic)
    
    def __repr__(self):
        return "TacticBranchIndex(%s, %s)" % (self.index, repr(self.tactic))

class TacticBranchDefault(TacticBranch):
    """Tactic branch corresponding to the default case."""
    def __init__(self, tactic: Tactic):
        self.tactic = tactic

    def __str__(self):
        return "default: %s;" % self.tactic
    
    def __repr__(self):
        return "TacticBranchDefault(%s)" % repr(self.tactic)


class Skip(Tactic):
    """Tactic that does nothing."""
    def __init__(self):
        pass

    def __str__(self):
        return "skip"

    def exec(self, thy: OSTheory, state: AbstractProofState) -> AbstractProofState:
        return state


class Admit(Tactic):
    """Skip the current subgoal. For debugging only."""
    def exec(self, thy: OSTheory, state: ProofState) -> EmptyProofState:
        return EmptyProofState()


class Then(Tactic):
    """Perform one tactic followed by another.
    
    The corresponding syntax is tac1 ;; tac2.
    
    Unlike in other ITPs, we place restrictions on the use of Then tactic,
    in that the first tactic (tac1) must produce exactly one proof state.

    """
    def __init__(self, tactic1: Tactic, tactic2: Tactic):
        self.tactic1 = tactic1
        self.tactic2 = tactic2

    def __str__(self):
        return "%s; %s" % (self.tactic1, self.tactic2)
    
    def __repr__(self):
        return "Then(%s, %s)" % (self.tactic1, self.tactic2)
    
    def exec(self, thy: OSTheory, state: ProofState) -> AbstractProofState:
        state2 = self.tactic1.exec(thy, state)

        if isinstance(state2, ProofState):
            return self.tactic2.exec(thy, state2)
        elif isinstance(state2, AssertProofState):
            # Handles the case assert (prop);; tac2
            return AssertProofState(state2.assert_prop, state2.assert_case,
                                    self.tactic2.exec(thy, state2.remain_case))
        else:
            raise TacticException(
                "Then: the first tactic must produce singleton (actual %s)" % type(state2)
            )

class ThenSplit(Tactic):
    """Perform one tactic, followed by tactics for each case.

    The corresponding syntax is tac1 { cases }.

    This is used when the first tactic (tac1) produces at least two proof
    states. For each resulting proof state, the corresponding tactic in
    cases is applied. The correspondence between proof states and tactic
    in cases is provided by ProofStatePath.

    """
    def __init__(self, tactic1: Tactic, cases: Iterable[TacticBranch]):
        self.tactic1 = tactic1
        self.cases = tuple(cases)

        # Form cases_map, index_map and default_tac
        self.cases_map: dict[str, TacticBranchCase] = dict()
        self.index_map: dict[int, TacticBranchIndex] = dict()
        self.default_tac: Tactic = Skip()
        for case in self.cases:
            if isinstance(case, TacticBranchCase):
                self.cases_map[case.constr_name] = case
            elif isinstance(case, TacticBranchIndex):
                self.index_map[case.index] = case
            elif isinstance(case, TacticBranchDefault):
                self.default_tac = case.tactic
            else:
                raise AssertionError("ThenSplit: %s" % type(case))

    def exec(self, thy: OSTheory, state: ProofState) -> AbstractProofState:
        state2 = self.tactic1.exec(thy, state)

        if isinstance(state2, ProofState):
            raise TacticException(
                "ThenSplit: the first tactic produces singleton."
            )
        elif isinstance(state2, CaseProofState):
            new_cases = list()
            for constr_name, param, new_state in state2.cases:
                if constr_name in self.cases_map:
                    tactic = self.cases_map[constr_name].tactic
                else:
                    tactic = self.default_tac
                new_cases.append((constr_name, param, tactic.exec(thy, new_state)))
            return CaseProofState(new_cases)
        elif isinstance(state2, IndexProofState):
            new_cases = list()
            for i, new_state in enumerate(state2.cases):
                index = i + 1  # branch is 1-based
                if index in self.index_map:
                    tactic = self.index_map[index].tactic
                else:
                    tactic = self.default_tac
                new_cases.append(tactic.exec(thy, new_state))
            return IndexProofState(new_cases)
        else:
            raise AssertionError("ThenSplit: %s" % type(state2))

class Auto(Tactic):
    """Directly call SMT solver on the assumptions and conclusion.
    
    If call to SMT is successful, return empty state indicating all goals
    are resolved. Otherwise raise exception.
    
    """
    def __init__(self, *, verbose=False):
        self.verbose = verbose

    def __str__(self):
        return "auto"

    def __repr__(self):
        return "Auto()"

    def exec(self, thy: OSTheory, state: ProofState) -> EmptyProofState:
        if self.verbose:
            print(f"solve {len(state.assumes)} facts, size = {len(str(state))}")

        # Check that all quantifiers have been removed
        for assume in state.assumes:
            if isinstance(assume.prop, (os_term.OSQuant, os_term.OSQuantIn)):
                raise TacticException(f"auto: proof state still contains quantifier {assume.prop}")
        if isinstance(state.concl.prop, (os_term.OSQuant, os_term.OSQuantIn)):
            raise TacticException(f"auto: proof state still contains quantifier {state.concl}")

        # Export json
        json_data = state.export_meta()
        with open("app/meta-viewer/src/assets/meta.json", "w", encoding='utf-8') as file:
            file.write(json.dumps(json_data, indent=4))

        # Apply Z3 solve
        assumes = []
        for assume in state.assumes:
            if not os_theory.is_defining_eq(thy, assume.prop):
                assumes.append(assume.prop)
        
        res = os_z3wrapper.solve_impl(thy, assumes, state.concl.prop)
        if isinstance(res, os_z3wrapper.UnsatResult):
            return EmptyProofState()
        elif isinstance(res, os_z3wrapper.ModelResult):
            raise os_z3wrapper.SMTException(res.z3_model, state, res.convert_ctxt)
        else:
            raise NotImplementedError(f"Z3 solve returns: {type(res)}")

def transform_defining_eq(eq: OSTerm, var_ctxt: os_term.VarContext,
                          transformer: Transformer) -> OSTerm:
    """Apply transformer to defining equation.
    
    Given equation of the form `lhs == rhs`, where `lhs` is an
    atomic term, apply transformer to each index in `lhs` as well as
    to `rhs`.

    """
    return os_term.eq(eq.lhs, eq.rhs.transform(var_ctxt, transformer))

class ApplyTransformer(Tactic):
    """Apply transformer to assumptions and goal of the state.
    
    Note defining equations are skipped in the rewriting.

    """
    def __init__(self, transformer: Transformer):
        self.transformer = transformer

    def exec(self, thy: OSTheory, state: ProofState) -> ProofState:
        var_ctxt = state.get_var_context()
        assumes = []
        for assume in state.assumes:
            if os_theory.is_defining_eq(thy, assume.prop):
                assumes.append(Assumes(transform_defining_eq(assume.prop, var_ctxt, self.transformer),
                                       generation=assume.generation,
                                       conds=assume.conds,
                                       name=assume.name, meta=assume.meta))
            else:
                assumes.append(Assumes(assume.prop.transform(var_ctxt, self.transformer),
                                       generation=assume.generation,
                                       conds=assume.conds,
                                       name=assume.name, meta=assume.meta))
        new_concl = Shows(state.concl.prop.transform(var_ctxt, self.transformer),
                          meta=state.concl.meta)
        return ProofState(
            state.type_params,
            state.fixes,
            assumes,
            new_concl,
            graph=state.graph
        )

class ApplyTransformerThy(Tactic):
    """Apply a transformer that takes theory as an argument.
    
    As with `ApplyTransformer`, the defining equations are skipped in
    the rewriting.
    
    """
    def __init__(self, transformer: Callable[[OSTheory], Transformer]):
        self.transformer = transformer

    def __str__(self):
        transformer = self.transformer(OSTheory())
        return f"ApplyTransformerThy({transformer})"

    def exec(self, thy: OSTheory, state: ProofState) -> ProofState:
        transformer = self.transformer(thy)
        var_ctxt = state.get_var_context()
        assumes = []
        for assume in state.assumes:
            if os_theory.is_defining_eq(thy, assume.prop):
                assumes.append(Assumes(transform_defining_eq(assume.prop, var_ctxt, transformer),
                                       generation=assume.generation,
                                       conds=assume.conds,
                                       name=assume.name, meta=assume.meta))
            else:
                assumes.append(Assumes(assume.prop.transform(var_ctxt, transformer),
                                       generation=assume.generation,
                                       conds=assume.conds,
                                       name=assume.name, meta=assume.meta))
        new_concl = Shows(state.concl.prop.transform(var_ctxt, transformer),
                          meta=state.concl.meta)
        return ProofState(
            state.type_params,
            state.fixes,
            assumes,
            new_concl,
            graph=state.graph
        )


class Exists(Tactic):
    """Supply witness to existence goal by hand.

    Given the current goal in the form of exists quantifier, instantiate
    the exists quantifier using supplied terms.

    """
    def __init__(self, exprs: Iterable[OSTerm]):
        self.exprs = exprs

    def exec(self, thy: OSTheory, state: ProofState) -> AbstractProofState:
        var_ctxt = state.get_var_context()

        # Extract existential variable and body statement
        vars, body, _ = os_term.strip_exists(var_ctxt, state.concl.prop)

        inst = dict()
        for var, expr in zip(vars, self.exprs):
            if var.type != expr.type:
                raise TacticException("exists: wrong type for variable %s. Expected %s, got %s" % (
                    var.name, var.type, expr.type))
            inst[var.name] = expr
        
        body = body.subst(inst)
        new_cases = list()
        shows = os_term.split_conj(body)
        for show in shows:
            # Form the goal
            new_cases.append(ProofState(
                type_params=state.type_params,
                fixes=state.fixes,
                assumes=state.assumes,
                concl=Shows(show),
                graph=state.graph
            ))

        if len(new_cases) == 1:
            return new_cases[0]
        else:
            return IndexProofState(new_cases)

class Specialize(Tactic):
    """Specialize a forall fact by hand.
    
    Given a fact in the form of forall quantifier, instantiate the
    forall quantifier using supplied terms.

    """
    def __init__(self, assume_name: str, exprs: Iterable[OSTerm]):
        self.assume_name = assume_name
        self.exprs = exprs

    def exec(self, thy: OSTheory, state: ProofState) -> ProofState:
        var_ctxt = state.get_var_context()

        assumes = list()
        if self.assume_name not in state.assume_map:
            raise TacticException(f"Specialize: fact {self.assume_name} not found")
        for assume in state.assumes:
            if assume.name == self.assume_name:
                vars, body, _ = os_term.strip_forall(var_ctxt, assume.prop)
                if len(vars) != len(self.exprs):
                    raise TacticException(
                        f"Specialize: expected {len(vars)} expressions, provided {len(self.exprs)}")
                inst: dict[str, OSTerm] = dict()
                for var, expr in zip(vars, self.exprs):
                    inst[var.name] = expr
                body = body.subst(inst)
                assumes.append(Assumes(body, generation=assume.generation, conds=assume.conds,
                                       name=assume.name))
            else:
                assumes.append(assume)

        return ProofState(
            type_params=state.type_params,
            fixes=state.fixes,
            assumes=assumes,
            concl=state.concl,
            graph=state.graph,
        )

class Skolemize(Tactic):
    """Skolemize quantifiers.
    
    Existential quantifiers in given assumption are converted into fixed
    variables. Both name of the assumption and new names for the variables
    must be provided.
    
    """
    def __init__(self, name: str, vars: Iterable[OSVar]):
        self.name = name
        self.vars = vars

    def exec(self, thy: OSTheory, state: ProofState) -> ProofState:
        var_ctxt = state.get_var_context()

        # Obtain list of existing variable names
        fixes_names = set(state.fixes_map.keys())

        # List of new variables, from existential quantifiers in assumptions
        # and universal quantifiers in the conclusion
        new_fixes = list()
        assumes = list()
        for assume in state.assumes:
            if assume.name == self.name:
                vars, body, _ = os_term.strip_exists(var_ctxt, assume.prop)
                if len(vars) != len(self.vars):
                    raise TacticException("skolemize: expected %s variable names, provided %s." % (
                        len(vars), len(self.vars)
                    ))
                inst = dict()
                for var, new_var in zip(vars, self.vars):
                    if new_var.name in fixes_names:
                        raise TacticException("skolemize: variable %s already exists" % new_var.name)
                    if var.type != new_var.type:
                        raise TacticException("skolemize: wrong type for variable %s. Expected %s, got %s" % (
                            var, var.type, new_var.type
                        ))
                    inst[var.name] = new_var
                    new_fixes.append(new_var)
                    fixes_names.add(new_var.name)
                assumes.append(Assumes(body.subst(inst), generation=assume.generation,
                                       conds=assume.conds, name=assume.name))
            else:
                assumes.append(Assumes(assume.prop, generation=assume.generation,
                                       conds=assume.conds, name=assume.name))

        return ProofState(
            type_params=state.type_params,
            fixes=tuple(list(state.fixes) + new_fixes),
            assumes=assumes,
            concl=state.concl,
            graph=state.graph
        )


class Intros(Tactic):
    """Introduce forall-quantifiers in the conclusion.

    Convert variables bounded by universal quantifiers into fixed free variables.
    Names for the new variables must be provided. 

    """
    def __init__(self, var_names: Iterable[str] = tuple()):
        self.var_names = var_names

    def exec(self, thy: OSTheory, state: ProofState) -> ProofState:
        if not os_term.is_forall(state.concl.prop):
            if len(self.var_names) > 0:
                raise TacticException("Intros: conclusion is not in forall form.")
            else:
                return state

        var_ctxt = state.get_var_context()
        try:
            new_vars, body, _ = os_term.strip_forall(
                var_ctxt, state.concl.prop, var_names=self.var_names)
        except os_term.OSTermException as e:
            raise TacticException(e.msg)

        As, C = os_term.strip_implies(body)
        As_t = [Assumes(assum, generation=0, conds=tuple()) for assum in As]
        return ProofState(
            type_params=state.type_params,
            fixes=tuple(state.fixes + new_vars),
            assumes=state.assumes + tuple(As_t),
            concl=Shows(C),
            graph=state.graph
        )


class Assert(Tactic):
    """Assert new fact with proof.

    This tactic creates an AssertProofState, where the assert case is for
    showing the asserted fact, and the remaining case is formed by adding
    the asserted fact as an assumption.
    
    Attributes
    ----------
    name : str
        name of the fact to be introduced.
    expr : OSTerm
        statement of the fact.
    tactic : Tactic
        tactic used to prove the fact.

    """
    def __init__(self, name: str, expr: OSTerm, tactic: Tactic):
        self.name = name
        self.expr = expr
        if self.expr.type != os_struct.Bool:
            raise AssertionError("assert: input expression is not of boolean type")
        self.tactic = tactic

    def exec(self, thy: OSTheory, state: ProofState) -> AssertProofState:
        # First prove assertion
        assert_state = ProofState(
            type_params=state.type_params,
            fixes=state.fixes,
            assumes=state.assumes,
            concl=Shows(self.expr),
            graph=state.graph
        )
        assert_state2 = self.tactic.exec(thy, assert_state)

        # The remainder is the proof state with assertion added
        remain_state = ProofState(
            type_params=state.type_params,
            fixes=state.fixes,
            assumes=state.assumes + (Assumes(self.expr, generation=0, conds=tuple(), name=self.name),),
            concl=state.concl,
            graph=state.graph
        )
        return AssertProofState(self.expr, assert_state2, remain_state)

class Change(Tactic):
    """Rewrite the goal using an asserted equality.
    
    This tactic creates an AssertProofState, where the assert case is for
    showing the equality, and the remaining case is formed by rewriting the
    goal using the equality.

    Attributes
    ----------
    expr : OSTerm
        statement of the equality.
    tactic : Tactic
        tactic used for proving the equality.

    """
    def __init__(self, expr: OSTerm, tactic: Tactic):
        self.expr = expr
        if not os_term.is_eq(self.expr):
            raise AssertionError("change: input expression is not equality")
        self.tactic = tactic

    def exec(self, thy: OSTheory, state: ProofState) -> AssertProofState:
        var_ctxt = state.get_var_context()

        # First prove assertion
        assert_state = ProofState(
            type_params=state.type_params,
            fixes=state.fixes,
            assumes=state.assumes,
            concl=Shows(self.expr),
            graph=state.graph
        )
        assert_state2 = self.tactic.exec(thy, assert_state)

        # Now rewrite using the new equality
        concl = Shows(state.concl.prop.transform(
            var_ctxt, os_simplify.ReplaceTerm(self.expr.lhs, self.expr.rhs)))
        remain_state = ProofState(
            type_params=state.type_params,
            fixes=state.fixes,
            assumes=state.assumes,
            concl=concl,
            graph=state.graph
        )
        return AssertProofState(self.expr, assert_state2, remain_state)

class Assumption(Tactic):
    """Find the goal in one of the assumptions."""
    def __init__(self):
        pass

    def exec(self, thy: OSTheory, state: ProofState) -> EmptyProofState:
        for assume in state.assumes:
            if assume.prop == state.concl.prop:
                return EmptyProofState()
        raise TacticException("Assumption: not found")

class SplitConj(Tactic):
    """Split conjunctions in assumptions.
    
    Assumption of the form A1 && A2 && ... && An is replaced by
    n assumptions A1, ..., An.

    Name of the assumption as well as the new assumptions must be
    provided.

    Attributes
    ----------
    name : str
        name of the assumption to be split
    new_names : tuple[str]
        name of the new assumptions

    """
    def __init__(self, name: str, new_names: Iterable[str]):
        self.name = name
        self.new_names = tuple(new_names)

    def exec(self, thy: OSTheory, state: ProofState) -> ProofState:
        assumes = list()
        if self.name not in state.assume_map:
            raise TacticException("SplitConj: fact %s not found" % self.name)
        for assume in state.assumes:
            if assume.name == self.name:
                conjs = os_term.split_conj(assume.prop)
                if len(conjs) != len(self.new_names):
                    raise TacticException("SplitConj: expected %s names, provided %s." % (
                        len(conjs), len(self.new_names)))
                for new_name, conj in zip(self.new_names, conjs):
                    assumes.append(Assumes(conj, generation=assume.generation,
                                           conds=assume.conds, name=new_name))
            else:
                assumes.append(assume)
        return ProofState(
            type_params=state.type_params,
            fixes=state.fixes,
            assumes=assumes,
            concl=state.concl,
            graph=state.graph
        )
    
class SplitGoal(Tactic):
    """Split the conjunctive goal into several parts.
    
    This results in an IndexProofState, where each index corresponds to
    one of the conjuncts.
    
    """
    def __init__(self):
        pass

    def exec(self, thy: OSTheory, state: ProofState) -> IndexProofState:
        if not os_term.is_conj(state.concl.prop):
            raise TacticException("SplitGoal: goal is not a conjunction")
        
        conjs = os_term.split_conj(state.concl.prop)
        new_cases = list()
        for conj in conjs:
            new_cases.append(ProofState(
                type_params=state.type_params,
                fixes=state.fixes,
                assumes=state.assumes,
                concl=Shows(conj),
                graph=state.graph
            ))

        return IndexProofState(new_cases)

class MatchShow(Tactic):
    """Match existential goal statement with one of the assumptions.

    For a goal of the form
        exists (v_1, ..., v_n) { Q_1 && Q_2 && ... && Q_k }
    and assumption of the form P, match one of the patterns Q_i with P in order
    to instantiate variables v_1, ..., v_n. For each match on Q_i, change the
    proof state to one subgoal for instantiation of Q_j for each j != i.

    Name of the assumption must be provided.

    Attributes
    ----------
    name : str
        Name of the assumption to match against.

    """
    def __init__(self, name: str):
        self.name = name

    def exec(self, thy: OSTheory, state: ProofState) -> IndexProofState:
        var_ctxt = state.get_var_context()

        if self.name not in state.assume_map:
            raise TacticException("MatchShow: name %s not found" % self.name)
        assume = state.assume_map[self.name]

        if not (isinstance(state.concl.prop, os_term.OSQuant) \
                and state.concl.prop.quantifier == "exists"):
            raise TacticException("MatchShow: goal not in exists form.")

        # Extract existential variable and body statement
        vars, body, _ = os_term.strip_exists(var_ctxt, state.concl.prop)

        # Replace variables by schematic variables
        inst = dict()
        for var in vars:
            inst[var.name] = OSVar("?" + var.name, type=var.type)
        body = body.subst(inst)
        body_pats = os_term.split_conj(body)

        # Match each conjunction with the given assumption. For the first
        # match, return the resulting goals.
        for pat in body_pats:
            tyinst, inst = dict(), dict()
            if os_match.match(pat, assume, tyinst, inst):
                # print("--- instantiation ---")
                # print("pat =", pat)
                # print("assume =", assume)
                # print("tyinst =", tyinst)
                # print("inst =", inst)

                # Instantiate the remaining parts of body
                body_inst = os_term.list_conj([pat2 for pat2 in body_pats if pat != pat2])
                body_inst = body_inst.subst_type(tyinst).subst(inst)
                if body_inst.has_sch_var():
                    # Incomplete instantiation
                    raise TacticException("MatchShow: incomplete instantiation")
                else:
                    # Complete instantiation
                    new_cases = list()
                    shows = os_term.split_conj(body_inst)
                    for show in shows:
                        # Form the goal
                        new_cases.append(ProofState(
                            type_params=state.type_params,
                            fixes=state.fixes,
                            assumes=state.assumes,
                            concl=Shows(show),
                            graph=state.graph
                        ))

                    return IndexProofState(new_cases)
        
        # No match found
        raise TacticException("MatchShow: match failed.")

class ApplyParam:
    """Parameters for applying a theorem.
    
    Attributes
    ----------
    thm_name : str
        Name of the theorem to be applied.
    facts : tuple[str], default to ()
        List of assumptions that also need to be matched.

    """
    def __init__(self, thm_name: str, facts: Iterable[str]):
        self.thm_name = thm_name
        self.facts = tuple(facts)

class ApplyTheorem(Tactic):
    """Apply previously proved theorem on the given query.

    Attributes
    ----------
    param: ApplyParam
        Parameters for applying theorem

    """
    def __init__(self, param: ApplyParam):
        self.param = param

    def exec(self, thy: OSTheory, state: ProofState) -> AbstractProofState:
        if self.param.thm_name in thy.theorems:
            thm = thy.get_sch_theorem(self.param.thm_name)
            assumes, concl = os_term.strip_implies(thm)
        elif self.param.thm_name in state.assume_map:
            assume = state.assume_map[self.param.thm_name]

            if not (os_term.is_forall(assume)):
                raise TacticException(
                    "ApplyTheorem: assumption %s is not in forall form" % self.param.thm_name)

            # Extract forall variable and body statement
            var_ctxt = state.get_var_context()
            vars, body, _ = os_term.strip_forall(var_ctxt, assume)

            # Replace variables by schematic variables
            inst = dict()
            for var in vars:
                inst[var.name] = OSVar("?" + var.name, type=var.type)
            body = body.subst(inst)
            assumes, concl = os_term.strip_implies(body)
        else:
            raise AssertionError("ApplyTheorem: theorem %s not found" % self.param.thm_name)

        # Match conclusion of theorem with current goal
        tyinst, inst = dict(), dict()
        if not os_match.match(concl, state.concl.prop, tyinst, inst):
            raise TacticException("ApplyTheorem: match %s with %s failed" % (concl, state.concl.prop))
        
        # Match assumptions of the theorem with the existing facts
        for i, fact in enumerate(self.param.facts):
            if fact == "_":
                continue  # skip assumption
            elif fact not in state.assume_map:
                raise TacticException("ApplyTheorem: fact %s not found" % fact)
            elif not os_match.match(assumes[i], state.assume_map[fact], tyinst, inst):
                raise TacticException("ApplyTheorem: match %s with %s failed" % (
                    assumes[i], state.assume_map[fact]))

        # print("--- instantiation ---")
        # print("concl =", concl)
        # print("state.concl =", state.concl)
        # print("tyinst =", tyinst)
        # print("inst =", inst)

        new_cases = list()
        for i, assume in enumerate(assumes):
            if i < len(self.param.facts) and self.param.facts[i] != "_":
                continue  # already matched fact
            new_concl = assume.subst_type(tyinst).subst(inst)
            if new_concl.has_sch_var():
                # Incomplete instantiation
                raise TacticException("ApplyTheorem: incomplete instantiation")
            else:
                # Form the goal
                new_cases.append(ProofState(
                    type_params=state.type_params,
                    fixes=state.fixes,
                    assumes=state.assumes,
                    concl=Shows(new_concl),
                    graph=state.graph
                ))
        
        if len(new_cases) == 0:
            return EmptyProofState()
        elif len(new_cases) == 1:
            return new_cases[0]
        else:
            return IndexProofState(new_cases)

class DefineVar(Tactic):
    """Define new variable `u` for a given expression `t`.

    This tactic adds equation `u == t` to the list of assumptions,
    and replaces `t` by `u` in the other parts of the state.
    
    """
    def __init__(self, var_name: str, expr: OSTerm):
        self.var_name = var_name
        self.expr = expr

    def __str__(self):
        return "define %s for %s" % (self.var_name, self.expr)
    
    def __repr__(self):
        return "DefineVar(%s, %s)" % (self.var_name, self.expr)

    def exec(self, thy: OSTheory, state: ProofState) -> ProofState:
        var_ctxt = state.get_var_context()
        if var_ctxt.contains_var(self.var_name):
            raise TacticException(f"DefineVar: variable {self.var_name} already used")

        new_var = OSVar(self.var_name, type=self.expr.type)
        transformer = os_simplify.ReplaceTerm(self.expr, new_var)

        assumes: list[Assumes] = list()
        for assume in state.assumes:
            new_assume = assume.prop.transform(var_ctxt, transformer)
            assumes.append(Assumes(new_assume, generation=assume.generation,
                                   conds=assume.conds, name=assume.name))
        assumes.append(Assumes(os_term.eq(new_var, self.expr), generation=0, conds=tuple()))

        new_concl = Shows(state.concl.prop.transform(var_ctxt, transformer))
        return ProofState(
            type_params=state.type_params,
            fixes=state.fixes + (new_var,),
            assumes=assumes,
            concl=new_concl,
            graph=state.graph
        )


class RewriteDefine(Tactic):
    """Rewrite using defining equation.

    This tactic rewrites using a defining equation `v = t`. Note
    it is unnecessary for the lhs `v` to be a variable.

    Attributes
    ----------
    name: str
        Name of the defining equation.

    """
    def __init__(self, name: str):
        self.name = name

    def __str__(self):
        return "rewrite define %s" % self.name

    def __repr__(self):
        return "RewriteDefine(%s)" % self.name

    def exec(self, thy: OSTheory, state: ProofState) -> ProofState:
        if self.name not in state.assume_map:
            raise AssertionError("RewriteDefine: fact %s not found" % self.name)

        eq = state.assume_map[self.name]
        if not os_term.is_eq(eq):
            raise AssertionError("RewriteDefine: fact %s is not an equality" % self.name)

        if not os_term.is_atomic_term(eq.lhs):
            raise AssertionError("RewriteDefine: lhs %s is not atomic" % eq.lhs)

        var_ctxt = state.get_var_context()
        transformer = os_simplify.ReplaceTerm(eq.lhs, eq.rhs)
        assumes = []
        for assume in state.assumes:
            if assume.name == self.name:
                assumes.append(assume)
            else:
                assumes.append(Assumes(assume.prop.transform(var_ctxt, transformer),
                                       generation=assume.generation,
                                       conds=assume.conds,
                                       name=assume.name, meta=assume.meta))
        
        new_concl = Shows(state.concl.prop.transform(var_ctxt, transformer),
                          meta=state.concl.meta)
        
        return ProofState(
            type_params=state.type_params,
            fixes=state.fixes,
            assumes=assumes,
            concl=new_concl,
            graph=state.graph
        )


class Rewrite(Tactic):
    """Rewrite using a theorem."""

    def __init__(self, th_name: str):
        self.th_name = th_name

    def __str__(self):
        return "rewrite %s" % self.th_name
    
    def __repr__(self):
        return "Rewrite(%s)" % self.th_name
    
    def exec(self, thy: OSTheory, state: ProofState) -> AbstractProofState:
        return ApplyTransformer(os_simplify.RewriteThm(thy, self.th_name)).exec(thy, state)


class Cases(Tactic):
    """Perform case analysis on an expression.

    Attributes
    ----------
    expr: OSTerm
        Expression on which to perform case analysis. The type of this
        expression should be a datatype. Case analysis is performed on
        the different branches of the datatype.
    cases : tuple[TacticBranch]
        List of tactics applied to each case of the datatype. Each element
        of cases should either TacticBranchCase of TacticBranchDefault.
    default : Tactic
        Tactic for default cases.
    cases_map : dict[str, TacticBranchCase]
        Mapping from constructor name to corresponding tactic.
    default_tac : Tactic
        Tactic for the default case

    The procedure for case analysis on expression t is as follows:

    - If t is a boolean expression, generate cases for true and false,
      respectively. Simplify corresponding if-then-else expressions.

    - If t is already a variable, generate one case for each constructor
      for the type of t. For each case, replace t by the given constructor.
      Simplify corresponding switch expressions.

    - If t is not a variable, pick a fresh variable u and add equation
      u = t to the list of assumptions. Then perform the above procedure
      on variable u.

    """
    def __init__(self, expr: OSTerm, *,
                 cases: Iterable[TacticBranch] = tuple()):
        self.expr = expr
        self.cases = tuple(cases)

        # Form cases_map and default_tac
        self.cases_map: dict[str, TacticBranchCase] = dict()
        self.default_tac: Tactic = Skip()
        for case in self.cases:
            if isinstance(case, TacticBranchCase):
                self.cases_map[case.constr_name] = case
            elif isinstance(case, TacticBranchDefault):
                self.default_tac = case.tactic
            else:
                raise AssertionError(
                    "Cases: each branch must be either TacticBranchCase "
                    "or TacticBranchDefault")

    def __str__(self):
        res = "cases (%s) {" % self.expr
        for case in self.cases:
            res += indent(str(case)) + "\n"
        res += "}"
        return res

    def __repr__(self):
        if not self.cases:
            return "Cases(%s)" % self.expr
        else:
            return "Cases(%s, [%s])" % (
                self.expr, ", ".join(str(case) for case in self.cases))

    def exec(self, thy: OSTheory, state: ProofState) -> AbstractProofState:
        # Type of the expression
        var_type = self.expr.type

        if var_type == os_struct.Bool:
            # Special case: boolean
            new_cases = list()

            for case_name in ("true", "false"):
                if case_name == "true":
                    new_assume = self.expr
                else:
                    new_assume = os_term.get_negation(self.expr)

                state2 = ProofState(
                    type_params=state.type_params,
                    fixes=state.fixes,
                    assumes=state.assumes + (Assumes(new_assume, generation=0, conds=tuple()),),
                    concl=state.concl,
                    graph=state.graph
                )

                # Simplify corresponding if-then-else expressions
                state2 = ApplyTransformer(
                    os_simplify.SimplifyITE(new_assume)).exec(thy, state2)

                if case_name in self.cases_map:
                    tactic = self.cases_map[case_name].tactic
                else:
                    tactic = self.default_tac

                new_cases.append((case_name, tuple(), tactic.exec(thy, state2)))
            
            return CaseProofState(new_cases)

        if isinstance(self.expr, OSVar):
            # Expression is already a variable
            var_name = self.expr.name
        else:
            # Create new variable name for the expression, and apply DefineVar
            # tactic to replace expression by the variable throughout. Note
            # the resulting variable u does not appear in the end-result.
            names = set(state.fixes_map.keys())
            var_name = os_util.variant_names(names, "u")
            state = DefineVar(var_name, self.expr).exec(thy, state)

        if not (isinstance(var_type, os_struct.OSHLevelType) and var_type.name in thy.datatypes):
            raise AssertionError("cases: expression %s has type %s is not datatype" % (self.expr, var_type))
        
        # Obtain datatype of the variable for case analysis, and find instantiation
        # of type parameters.
        datatype = thy.datatypes[var_type.name]
        branches = datatype.branches
        type_inst = dict(zip(datatype.params, var_type.params))

        # List of resulting proof states
        new_cases = list()

        for branch in branches:
            # Name of the constructor
            constr_name = branch.constr_name

            # Form fixes: the list of fixed variables are the original variables
            # minus the variable on which to conduct case analysis, plus parameters
            # for the case.
            fixes = []
            for fix in state.fixes:
                if fix.name != var_name:
                    fixes.append(fix)
            
            arg_list = list()
            if constr_name in self.cases_map:
                # Use parameter names provided in cases
                case = self.cases_map[constr_name]
                for case_param, (_, param_type) in zip(case.params, branch.params):
                    arg_list.append(OSVar(case_param, type=param_type.subst(type_inst)))
            else:
                # Create fresh names
                names = set(state.fixes_map.keys())
                for param_name, param_type in branch.params:
                    new_name = os_util.variant_names(names, param_name)
                    names.add(new_name)
                    arg_list.append(OSVar(new_name, type=param_type.subst(type_inst)))
            fixes.extend(arg_list)

            # For each existing assumption, make the corresponding assumption
            # by substitution
            assumes = []
            for assume in state.assumes:
                inst = dict()
                inst[var_name] = os_term.OSFun(constr_name, *arg_list, type=var_type)
                assumes.append(Assumes(assume.prop.subst(inst), generation=assume.generation,
                                       conds=assume.conds, name=assume.name))

            # Form the goal
            inst = dict()
            inst[var_name] = os_term.OSFun(constr_name, *arg_list, type=var_type)
            concl = Shows(state.concl.prop.subst(inst))

            state2 = ProofState(
                type_params=state.type_params,
                fixes=fixes,
                assumes=assumes,
                concl=concl,
                graph=state.graph
            )

            # Simplify corresponding switch expressions
            state2 = ApplyTransformer(
                os_simplify.SimplifySwitchOnConstructor(thy)).exec(thy, state2)
            
            if constr_name in self.cases_map:
                tactic = self.cases_map[constr_name].tactic
            else:
                tactic = self.default_tac

            new_cases.append((constr_name, arg_list, tactic.exec(thy, state2)))

        return CaseProofState(new_cases)


class InductionParam:
    """Parameters for induction.
    
    Attributes
    ----------
    induct_var : str
        Variable on which to perform induction. The type of this variable
        should be a datatype.
    arbitraries : tuple[str]
        List of generalized variables.

    """
    def __init__(self, induct_var: str, arbitraries: Iterable[str]):
        self.induct_var = induct_var
        self.arbitraries = tuple(arbitraries)

    def __str__(self):
        if not self.arbitraries:
            return self.induct_var
        else:
            return "%s [%s]" % (self.induct_var, ", ".join(self.arbitraries))
    
class Induction(Tactic):
    """Perform induction on a variable.
    
    Attributes
    ----------
    param : InductionParam
    cases : tuple[TacticBranch]
        List of tactics applied to each case of the datatype.
    cases_map : dict[str, TacticBranchCase]
        Mapping from constructor name to corresponding tactic.
    default_tac : Tactic
        Tactic for the default case.

    """
    def __init__(self, param: InductionParam, cases: Iterable[TacticBranch]):
        self.param = param
        self.cases = tuple(cases)

        # Form cases_map and default_tac
        self.cases_map: dict[str, TacticBranchCase] = dict()
        self.default_tac: Tactic = Skip()
        for case in self.cases:
            if isinstance(case, TacticBranchCase):
                self.cases_map[case.constr_name] = case
            elif isinstance(case, TacticBranchDefault):
                self.default_tac = case.tactic
            else:
                raise AssertionError("Induction case: %s" % type(case))

    def __str__(self):
        res = "induction (%s) {" % self.param
        for case in self.cases:
            res += indent(str(case)) + "\n"
        res += "}"
        return res

    def __repr__(self):
        return "Induction(%s, [%s])" % (
            self.param, ", ".join(str(case) for case in self.cases))

    def exec(self, thy: OSTheory, state: ProofState) -> AbstractProofState:
        # Type of the induction variable
        var_name = self.param.induct_var
        if var_name not in state.fixes_map:
            raise AssertionError("induction: induction variable %s not found" % var_name)

        var_type = state.fixes_map[var_name]

        if not (isinstance(var_type, os_struct.OSHLevelType) and var_type.name in thy.datatypes):
            raise AssertionError("induction: variable %s has type %s is not datatype" % (var_name, var_type))

        # Obtain datatype of the induction variable, and find instantiation
        # of type parameters.
        datatype = thy.datatypes[var_type.name]
        branches = datatype.branches
        type_inst = dict(zip(datatype.params, var_type.params))

        # List of resulting proof states
        new_cases = list()

        for branch in branches:
            # Name of the constructor
            constr_name = branch.constr_name

            # Form fixes: the list of fixed variables are the original variables
            # minus the variable on which to conduct case analysis, plus parameters
            # for the case.
            fixes = []
            for fix in state.fixes:
                if fix.name != var_name:
                    fixes.append(fix)

            arg_list: list[OSVar] = list()
            if constr_name in self.cases_map:
                # Use parameter names provided in cases
                case = self.cases_map[constr_name]
                for case_param, (_, param_type) in zip(case.params, branch.params):
                    arg_list.append(OSVar(case_param, type=param_type.subst(type_inst)))
            else:
                # Create fresh names
                names = set(state.fixes_map.keys())
                for param_name, param_type in branch.params:
                    new_name = os_util.variant_names(names, param_name)
                    names.add(new_name)
                    arg_list.append(OSVar(new_name, type=param_type.subst(type_inst)))
            fixes.extend(arg_list)

            # For each existing assumption, make the corresponding assumption
            # by substitution
            assumes = []
            for assume in state.assumes:
                inst = dict()
                inst[var_name] = os_term.OSFun(branch.constr_name, *arg_list, type=var_type)
                assumes.append(Assumes(assume.prop.subst(inst), generation=assume.generation,
                                       conds=assume.conds, name=assume.name))

            # For each argument with the same type, make the corresponding
            # inductive hypothesis
            for arg in arg_list:
                if arg.type.subst(type_inst) == var_type:
                    inst = dict()
                    inst[var_name] = OSVar(arg.name, type=arg.type.subst(type_inst))
                    ind_assumes = list()
                    for assume in state.assumes:
                        if assume.prop.has_var(var_name) or \
                            any(assume.prop.has_var(arbitrary) for arbitrary in self.param.arbitraries):
                            ind_assumes.append(assume.prop)
                    ind_prop = os_term.list_implies(ind_assumes, state.concl.prop).subst(inst)
                    decls = list()
                    for arbitrary in reversed(self.param.arbitraries):
                        if arbitrary not in state.fixes_map:
                            raise AssertionError("arbitrary variable %s not found" % arbitrary)
                        decls.append(OSVar(arbitrary, type=state.fixes_map[arbitrary]))
                    if decls:
                        ind_prop = os_term.OSQuant("forall", decls, ind_prop)
                    assumes.append(Assumes(ind_prop, generation=0, conds=tuple(), name="IH_" + arg.name))

            # Form the goal
            inst = dict()
            inst[var_name] = os_term.OSFun(branch.constr_name, *arg_list, type=var_type)
            concl = Shows(state.concl.prop.subst(inst))

            state2 = ProofState(
                type_params=state.type_params,
                fixes=fixes,
                assumes=assumes,
                concl=concl,
                graph=state.graph
            )
            
            if constr_name in self.cases_map:
                tactic = self.cases_map[constr_name].tactic
            else:
                tactic = self.default_tac
            new_cases.append((constr_name, arg_list, tactic.exec(thy, state2)))

        return CaseProofState(new_cases)


class InductionFunc(Tactic):
    """Perform induction on a function."""
    def __init__(self, func_name: str):
        self.func_name = func_name

    def __str__(self):
        return "induction_func(%s)" % self.func_name
    
    def exec(self, thy: OSTheory, state: AbstractProofState) -> AbstractProofState:
        if not isinstance(state, ProofState):
            raise TacticException("induction: not applied to singleton")
        
        print(state)
        raise AssertionError


def init_proof_state(thy: OSTheory, query: os_query.Query, n: int) -> ProofState:
    """Initialize proof state from the given query.
    
    Parameters
    ----------
    query : Query
        input query.
    n : int
        index in shows list of the query to serve as initial goal.

    Returns
    -------
    ProofState
        initial proof state for the input query.

    """
    return ProofState(
        type_params=query.type_params,
        fixes=query.fixes,
        assumes=[Assumes(assume.prop, name=assume.name, generation=0, conds=tuple(),
                         meta=os_query.Meta(initial_form=assume.prop))
                 for assume in query.assumes],
        concl=query.shows[n],
        graph=None
    )

def check_proof(thy: OSTheory, query: os_query.Query):
    """Check proof of each goal in the query.
    
    Parameters
    ----------
    thy : OSTheory
        the current theory
    query : Query
        query on which to check proof

    """
    for i, show in enumerate(query.shows):
        state = init_proof_state(thy, query, i)
        proof: Tactic = show.proof
        state = proof.exec(thy, state)
        if state.num_unsolved() != 0:
            print("Subgoals remaining:")
            print(state)
            raise AssertionError(
                "check_proof: %s subgoals remaining" % state.num_unsolved())
