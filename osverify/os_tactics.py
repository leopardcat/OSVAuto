from typing import Dict, List, Iterable, Optional, Tuple

from osverify import os_util
from osverify import os_struct
from osverify import os_theory
from osverify import os_query
from osverify import os_term
from osverify.os_term import OSTerm
from osverify import os_match
from osverify.os_util import indent
from osverify import os_simplify
from osverify import os_z3wrapper
from osverify import os_model

class AbstractProofState:
    """Base class of proof states."""
    def __len__(self):
        raise NotImplementedError("__len__: %s" % type(self))

class EmptyProofState(AbstractProofState):
    """Corresponds to a proof state that is already resolved."""
    def __init__(self):
        pass

    def __str__(self):
        return "()"
    
    def __len__(self):
        return 0

class CaseProofState(AbstractProofState):
    """Corresponds to proof states distinguished by datatype cases.
    
    Each case is specified constructor name, list of arguments to the
    constructor, and the resulting proof state. Arguments to the
    constructor are new names that can appear in the corresponding
    proof state.

    """
    def __init__(self, cases: Iterable[Tuple[str, Tuple[os_term.OSVar], AbstractProofState]]):
        self.cases = cases

    def __str__(self):
        res = ""
        first = True
        for constr_name, params, state in self.cases:
            if len(state) > 0:
                if not first:
                    res += "\n"
                res += constr_name
                if params:
                    res += "(%s)" % (", ".join(str(param) for param in params))
                res += " {\n"
                res += indent(str(state)) + "\n"
                res += "}"
                first = False
        return res
    
    def __len__(self):
        res = 0
        for _, _, state in self.cases:
            res += len(state)
        return res

class IndexProofState(AbstractProofState):
    """Corresponding to proof states distinguished by index.
    
    The cases are distinguished by index. While we store the proof states
    in a list, the cases are 1-based.

    """
    def __init__(self, cases: Iterable[AbstractProofState]):
        self.cases = cases

    def __str__(self):
        res = ""
        first = True
        for i, state in enumerate(self.cases):
            if len(state) > 0:
                if not first:
                    res += "\n"
                res += "%s: {\n" % (i + 1)
                res += indent(str(state)) + "\n"
                res += "}"
                first = False
        return res
    
    def __len__(self):
        res = 0
        for state in self.cases:
            res += len(state)
        return res

class AssertProofState(AbstractProofState):
    """Proving and then using an assertion."""
    def __init__(self, assert_prop: OSTerm, assert_case: AbstractProofState, remain_case: AbstractProofState):
        self.assert_prop = assert_prop
        self.assert_case = assert_case
        self.remain_case = remain_case

    def __str__(self):
        res = ""
        first = True
        if len(self.assert_case) > 0:
            res += "assert %s: {" % self.assert_prop
            res += indent(str(self.assert_case)) + "\n"
            res += "}"
            first = False
        if len(self.remain_case) > 0:
            if not first:
                res += "\n"
            res += str(self.remain_case)
        return res
    
    def __len__(self):
        return len(self.assert_case) + len(self.remain_case)

class ProofState(AbstractProofState):
    """Represents the intermediate state during a proof.
    
    Each proof state is given by list of type parameters, fixed variables,
    assumptions and conclusion (goal).

    Proof states are immutable. Tactics should return new proof states
    rather than modifying their inputs.

    Attributes
    ----------
    type_params : Tuple[str]
        list of type parameters
    fixes : Tuple[OSVar]
        list of fixed variables
    assumes : Tuple[Tuple[str, OSTerm]]
        list of assumptions, each with optional name (default to empty string)
    concl : OSTerm
        current proof goal
    fixes_map : Dict[str, OSType]
        mapping from variable names to their type
    
    """
    def __init__(self, type_params: Iterable[str],
                 fixes: Iterable[os_term.OSVar],
                 assumes: Iterable[Tuple[str, OSTerm]],
                 concl: OSTerm):
        self.type_params = tuple(type_params)
        self.fixes = tuple(fixes)
        self.assumes = tuple(assumes)
        self.concl = concl
        self.fixes_map = dict((fix.name, fix.type) for fix in self.fixes)
        self.assume_map = dict((name, assume) for name, assume in self.assumes if name != "")

    def __str__(self):
        res = ""
        for type_param in self.type_params:
            res += "type %s" % type_param + '\n'
        for var in self.fixes:
            res += "fix %s: %s" % (var.name, var.type) + '\n'
        for name, assume in self.assumes:
            if name:
                res += "assume %s: %s" % (name, assume) + '\n'
            else:
                res += "assume %s" % assume + '\n'
        res += "prove %s" % self.concl
        return res
    
    def __len__(self):
        return 1
    
    def __eq__(self, other):
        return isinstance(other, ProofState) and self.type_params == other.type_params and \
            self.fixes == other.fixes and self.assumes == other.assumes and self.concl == other.concl

    def get_context(self, thy: os_theory.OSTheory) -> os_theory.OSContext:
        ctxt = os_theory.OSContext(thy)
        ctxt.type_params = list(self.type_params)
        ctxt.var_decls = self.fixes_map
        return ctxt


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
    def exec(self, thy: os_theory.OSTheory, state: AbstractProofState) -> AbstractProofState:
        """Execute the tactic on the given state."""
        raise NotImplementedError

class TacticBranch:
    """Base class for tactic branches."""
    
    # Tactic for the branch
    tactic : Tactic

class TacticBranchCase(TacticBranch):
    """Tactic branch corresponding to a datatype case
    
    The list of parameters is introduced, and may be used in the
    ensuing tactic.
    
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

    def exec(self, thy: os_theory.OSTheory, state: AbstractProofState) -> AbstractProofState:
        return state
    
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
    
    def exec(self, thy: os_theory.OSTheory, state: AbstractProofState) -> AbstractProofState:
        state2 = self.tactic1.exec(thy, state)

        if isinstance(state2, ProofState):
            return self.tactic2.exec(thy, state2)
        elif isinstance(state2, AssertProofState):
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
        self.cases_map: Dict[str, TacticBranchCase] = dict()
        self.index_map: Dict[int, TacticBranchIndex] = dict()
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

    def exec(self, thy: os_theory.OSTheory, state: AbstractProofState) -> AbstractProofState:
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

    Attributes
    ----------
    thm_spec : Tuple[TheoremSpec]
        List of theorems that can be used.
    
    """
    def __init__(self, *, thm_spec: Iterable[os_theory.TheoremSpec] = tuple()):
        self.thm_spec = tuple(thm_spec)

    def __str__(self):
        if self.thm_spec:
            return "auto(%s)" % ", ".join(str(spec) for spec in self.thm_spec)
        else:
            return "auto"

    def __repr__(self):
        return "Auto(%s)" % ", ".join(repr(spec) for spec in self.thm_spec)

    def exec(self, thy: os_theory.OSTheory, state: AbstractProofState) -> AbstractProofState:
        if not isinstance(state, ProofState):
            raise TacticException("auto: not applied to singleton")

        res = os_z3wrapper.solve(thy, [assume for _, assume in state.assumes],
                                 state.concl, thm_spec=self.thm_spec)
        if isinstance(res, os_z3wrapper.UnsatResult):
            return EmptyProofState()
        elif isinstance(res, os_z3wrapper.ModelResult):
            print(res.model)
            model = os_z3wrapper.convert_model(thy, state.fixes, res.model)
            print(model)
            os_model.diagnose_query(thy, [assume for _, assume in state.assumes], state.concl, model)
            raise TacticException("Z3 is unable to prove goal")
        else:
            raise TacticException("Z3 is unable to prove goal")

class Simplify(Tactic):
    """Simplify assumption and conclusion of a query."""
    def __init__(self):
        pass

    def exec(self, thy: os_theory.OSTheory, state: AbstractProofState) -> AbstractProofState:
        if not isinstance(state, ProofState):
            raise TacticException("simplify: not applied to singleton")

        return ProofState(
            state.type_params,
            state.fixes,
            [(name, os_simplify.simplify(thy, assume)) for name, assume in state.assumes],
            os_simplify.simplify(thy, state.concl)
        )

class Skolemize(Tactic):
    """Skolemize quantifiers.
    
    Existential quantifiers in the assumptions and universal quantifiers
    in the conclusion are converted into fixed variables.
    
    """
    def __init__(self):
        pass

    def exec(self, thy: os_theory.OSTheory, state: AbstractProofState) -> AbstractProofState:
        if not isinstance(state, ProofState):
            raise TacticException("skolemize: not applied to singleton")

        # Obtain list of existing variable names
        names = set(state.fixes_map.keys())

        # List of new variables, from existential quantifiers in assumptions
        # and universal quantifiers in the conclusion
        new_fixes = list()
        assumes = list()
        for name, assume in state.assumes:
            vars, body = os_term.strip_exists(assume)
            for var in vars:
                variant = os_util.variant_names(names, var.name)
                new_fixes.append(os_term.OSVar(variant, type=var.type))
                names.add(variant)
            assumes.append((name, body))

        # Form the new conclusion
        vars, body = os_term.strip_forall(state.concl)
        for var in vars:
            variant = os_util.variant_names(names, var.name)
            new_fixes.append(os_term.OSVar(variant, type=var.type))
            names.add(variant)

        return ProofState(
            type_params=state.type_params,
            fixes=tuple(list(state.fixes) + new_fixes),
            assumes=assumes,
            concl=body
        )


class Assert(Tactic):
    """Assert new fact with proof."""
    def __init__(self, name: str, expr: OSTerm, tactic: Tactic):
        self.name = name
        self.expr = expr
        if self.expr.type != os_struct.Bool:
            raise AssertionError("assert: input expression is not of boolean type")
        self.tactic = tactic

    def exec(self, thy: os_theory.OSTheory, state: AbstractProofState) -> AbstractProofState:
        if not isinstance(state, ProofState):
            raise TacticException("assert: not applied to singleton")

        # First prove assertion
        assert_state = ProofState(
            type_params=state.type_params,
            fixes=state.fixes,
            assumes=state.assumes,
            concl=self.expr
        )
        assert_state2 = self.tactic.exec(thy, assert_state)

        # The remainder is the proof state with assertion added
        remain_state = ProofState(
            type_params=state.type_params,
            fixes=state.fixes,
            assumes=state.assumes + ((self.name, self.expr),),
            concl=state.concl
        )
        return AssertProofState(self.expr, assert_state2, remain_state)

class Assumption(Tactic):
    """Find the goal in one of the assumptions."""
    def __init__(self):
        pass

    def exec(self, thy: os_theory.OSTheory, state: AbstractProofState) -> AbstractProofState:
        if not isinstance(state, ProofState):
            raise TacticException("assumption: not applied to singleton")

        for _, assume in state.assumes:
            if assume == state.concl:
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
    new_names : Tuple[str]
        name of the new assumptions

    """
    def __init__(self, name: str, new_names: Iterable[str]):
        self.name = name
        self.new_names = tuple(new_names)

    def exec(self, thy: os_theory.OSTheory, state: AbstractProofState) -> AbstractProofState:
        if not isinstance(state, ProofState):
            raise TacticException("split_conj: not applied to singleton")

        assumes = list()
        for name, assume in state.assumes:
            if name == self.name:
                conjs = os_term.split_conj(assume)
                if len(conjs) != len(self.new_names):
                    raise TacticException("SplitConj: expected %s names, provided %s." % (
                        len(conjs), len(self.new_names)))
                for new_name, conj in zip(self.new_names, conjs):
                    assumes.append((new_name, conj))
            else:
                assumes.append((name, assume))
        return ProofState(
            type_params=state.type_params,
            fixes=state.fixes,
            assumes=assumes,
            concl=state.concl
        )

class MatchShow(Tactic):
    """Match existential goal statement with one of the assumptions.

    For a goal of the form
        exists v_1 .. v_n. Q_1 && Q_2 && ... && Q_k
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

    def exec(self, thy: os_theory.OSTheory, state: AbstractProofState) -> AbstractProofState:
        if not isinstance(state, ProofState):
            raise TacticException("MatchShow: not applied to singleton")

        if self.name not in state.assume_map:
            raise TacticException("MatchShow: name %s not found" % self.name)
        assume = state.assume_map[self.name]

        if not (isinstance(state.concl, os_term.OSQuant) and state.concl.quantifier == "exists"):
            raise TacticException("MatchShow: goal not in exists form.")

        # Extract existential variable and body statement
        vars, body = os_term.strip_exists(state.concl)

        # Replace variables by schematic variables
        inst = dict()
        for var in vars:
            inst[var.name] = os_term.OSVar("?" + var.name, type=var.type)
        body = body.subst(inst)
        body_pats = os_term.split_conj(body)

        # Match each conjunction with the given assumption. For the first
        # match, return the resulting goals.
        for pat in body_pats:
            tyinst, inst = dict(), dict()
            if os_match.match(thy, pat, assume, tyinst, inst):
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
                            concl=show
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
    facts : Tuple[str], default to ()
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

    def exec(self, thy: os_theory.OSTheory, state: ProofState) -> List[ProofState]:
        if self.param.thm_name in thy.theorems:
            thm = thy.get_sch_theorem(self.param.thm_name)
            assumes, concl = os_term.strip_implies(thm)
        elif self.param.thm_name in state.assume_map:
            assume = state.assume_map[self.param.thm_name]

            if not (isinstance(assume, os_term.OSQuant) and assume.quantifier == "forall"):
                raise TacticException("ApplyTheorem: assumption %s is not in forall form" % self.name)

            # Extract forall variable and body statement
            vars, body = os_term.strip_forall(assume)

            # Replace variables by schematic variables
            inst = dict()
            for var in vars:
                inst[var.name] = os_term.OSVar("?" + var.name, type=var.type)
            body = body.subst(inst)
            assumes, concl = os_term.strip_implies(body)
        else:
            raise AssertionError("ApplyTheorem: theorem %s not found" % self.param.thm_name)

        # Match conclusion of theorem with current goal
        tyinst, inst = dict(), dict()
        if not os_match.match(thy, concl, state.concl, tyinst, inst):
            raise TacticException("ApplyTheorem: match %s with %s failed" % (concl, state.concl))
        
        # Match assumptions of the theorem with the existing facts
        for i, fact in enumerate(self.param.facts):
            if fact == "_":
                continue  # skip assumption
            elif fact not in state.assume_map:
                raise TacticException("ApplyTheorem: fact %s not found" % fact)
            elif not os_match.match(thy, assumes[i], state.assume_map[fact], tyinst, inst):
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
                    concl=new_concl
                ))
        
        if len(new_cases) == 0:
            return EmptyProofState()
        elif len(new_cases) == 1:
            return new_cases[0]
        else:
            return IndexProofState(new_cases)

class DefineVar(Tactic):
    """Define new variable u for a given expression t.

    This tactic adds equation u == t to the list of assumptions,
    and replaces t by u in the other parts of the state.
    
    """
    def __init__(self, var_name: str, expr: OSTerm):
        self.var_name = var_name
        self.expr = expr

    def __str__(self):
        return "define %s for %s" % (self.var_name, self.expr)
    
    def __repr__(self):
        return "DefineVar(%s, %s)" % (self.var_name, self.expr)

    def exec(self, thy: os_theory.OSTheory, state: AbstractProofState) -> AbstractProofState:
        if not isinstance(state, ProofState):
            raise TacticException("DefineVar: not applied to singleton")

        new_var = os_term.OSVar(self.var_name, type=self.expr.type)

        def replace_term(expr: OSTerm) -> OSTerm:
            return new_var if expr == self.expr else expr

        assumes: List[Tuple[str, OSTerm]] = list()
        for name, assume in state.assumes:
            assumes.append((name, assume.apply_subterm(replace_term)))
        assumes.append(("eq_%s" % self.var_name, os_term.OSOp("==", new_var, self.expr)))

        return ProofState(
            type_params=state.type_params,
            fixes=state.fixes + (new_var,),
            assumes=assumes,
            concl=state.concl.apply_subterm(replace_term)
        )

class Cases(Tactic):
    """Perform case analysis on the given query.

    Attributes
    ----------
    expr: OSTerm
        Expression on which to perform case analysis. The type of this expression
        should be a datatype.
    cases : Tuple[TacticBranch]
        List of tactics applied to each case of the datatype.
    default : Tactic
        Tactic for default cases.
    cases_map : Dict[str, TacticBranchCase]
        Mapping from constructor name to corresponding tactic.
    default_tac : Tactic
        Tactic for the default case

    The procedure for case analysis on expression t is as follows:

    - If t is already a variable, generate one case for each constructor
      for the type of t. For each case, replace t by the given constructor.

    - If t is not a variable, pick a fresh variable u and add equation
      u = t to the list of assumptions. Then perform the above procedure
      on variable u.

    """
    def __init__(self, expr: OSTerm, *,
                 cases: Iterable[TacticBranch] = tuple()):
        self.expr = expr
        self.cases = tuple(cases)

        # Form cases_map and default_tac
        self.cases_map: Dict[str, TacticBranchCase] = dict()
        self.default_tac: Tactic = Skip()
        for case in self.cases:
            if isinstance(case, TacticBranchCase):
                self.cases_map[case.constr_name] = case
            elif isinstance(case, TacticBranchDefault):
                self.default_tac = case.tactic
            else:
                raise AssertionError

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

    def exec(self, thy: os_theory.OSTheory, state: AbstractProofState) -> AbstractProofState:
        if not isinstance(state, ProofState):
            raise TacticException("Cases: not applied to singleton")

        if isinstance(self.expr, os_term.OSVar):
            # Expression is already a variable
            var_name = self.expr.name
        else:
            # Create new variable name for the expression, and apply DefineVar
            # tactic to replace expression by the variable throughout.
            names = set(state.fixes_map.keys())
            var_name = os_util.variant_names(names, "u")
            state = DefineVar(var_name, self.expr).exec(thy, state)[0]

        # Type of the expression
        var_type = os_theory.expand_type(thy, state.fixes_map[var_name])

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
                    arg_list.append(os_term.OSVar(case_param, type=param_type.subst(type_inst)))
            else:
                # Create fresh names
                names = set(state.fixes_map.keys())
                for param_name, param_type in branch.params:
                    new_name = os_util.variant_names(names, param_name)
                    names.add(new_name)
                    arg_list.append(os_term.OSVar(new_name, type=param_type.subst(type_inst)))
            fixes.extend(arg_list)

            # For each existing assumption, make the corresponding assumption
            # by substitution
            assumes = []
            for name, assume in state.assumes:
                inst = dict()
                inst[var_name] = os_term.OSFun(constr_name, *arg_list, type=var_type)
                assumes.append((name, assume.subst(inst)))

            # Form the goal
            inst = dict()
            inst[var_name] = os_term.OSFun(constr_name, *arg_list, type=var_type)
            concl = state.concl.subst(inst)

            state2 = ProofState(
                type_params=state.type_params,
                fixes=fixes,
                assumes=assumes,
                concl=concl)
            
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
    arbitraries : Tuple[str]
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
    cases : Tuple[TacticBranch]
        List of tactics applied to each case of the datatype.
    cases_map : Dict[str, TacticBranchCase]
        Mapping from constructor name to corresponding tactic.
    default_tac : Tactic
        Tactic for the default case.

    """
    def __init__(self, param: InductionParam, cases: Iterable[TacticBranch]):
        self.param = param
        self.cases = tuple(cases)

        # Form cases_map and default_tac
        self.cases_map: Dict[str, TacticBranchCase] = dict()
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

    def exec(self, thy: os_theory.OSTheory, state: ProofState) -> List[ProofState]:
        # Type of the induction variable
        var_name = self.param.induct_var
        if var_name not in state.fixes_map:
            raise AssertionError("induction: induction variable %s not found" % var_name)

        var_type = os_theory.expand_type(thy, state.fixes_map[var_name])

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

            arg_list: List[os_term.OSVar] = list()
            if constr_name in self.cases_map:
                # Use parameter names provided in cases
                case = self.cases_map[constr_name]
                for case_param, (_, param_type) in zip(case.params, branch.params):
                    arg_list.append(os_term.OSVar(case_param, type=param_type.subst(type_inst)))
            else:
                # Create fresh names
                names = set(state.fixes_map.keys())
                for param_name, param_type in branch.params:
                    new_name = os_util.variant_names(names, param_name)
                    names.add(new_name)
                    arg_list.append(os_term.OSVar(new_name, type=param_type.subst(type_inst)))
            fixes.extend(arg_list)

            # For each existing assumption, make the corresponding assumption
            # by substitution
            assumes = []
            for name, assume in state.assumes:
                inst = dict()
                inst[var_name] = os_term.OSFun(branch.constr_name, *arg_list, type=var_type)
                assumes.append((name, assume.subst(inst)))

            # For each argument with the same type, make the corresponding
            # inductive hypothesis
            for arg in arg_list:
                if os_theory.equal_type(thy, arg.type.subst(type_inst), var_type):
                    inst = dict()
                    inst[var_name] = os_term.OSVar(arg.name, type=arg.type.subst(type_inst))
                    ind_assumes = list()
                    for name, assume in state.assumes:
                        if assume.has_var(var_name) or \
                            any(assume.has_var(arbitrary) for arbitrary in self.param.arbitraries):
                            ind_assumes.append(assume)
                    ind_prop = os_term.list_implies(ind_assumes, state.concl).subst(inst)
                    decls = list()
                    for arbitrary in reversed(self.param.arbitraries):
                        if arbitrary not in state.fixes_map:
                            raise AssertionError("arbitrary variable %s not found" % arbitrary)
                        decls.append(os_term.OSVar(arbitrary, type=state.fixes_map[arbitrary]))
                    if decls:
                        ind_prop = os_term.OSQuant("forall", decls, ind_prop)
                    assumes.append(("IH_" + arg.name, ind_prop))

            # Form the goal
            inst = dict()
            inst[var_name] = os_term.OSFun(branch.constr_name, *arg_list, type=var_type)
            concl = state.concl.subst(inst)

            state2 = ProofState(
                type_params=state.type_params,
                fixes=fixes,
                assumes=assumes,
                concl=concl)
            
            if constr_name in self.cases_map:
                tactic = self.cases_map[constr_name].tactic
            else:
                tactic = self.default_tac
            new_cases.append((constr_name, arg_list, tactic.exec(thy, state2)))

        return CaseProofState(new_cases)


def init_proof_state(query: os_query.Query, n: int) -> ProofState:
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
        assumes=[(assume.name, assume.prop) for assume in query.assumes],
        concl=query.shows[n].prop
    )

def check_proof(thy: os_theory.OSTheory, query: os_query.Query):
    """Check proof of each goal in the query.
    
    Parameters
    ----------
    thy : OSTheory
        the current theory
    query : Query
        query on which to check proof

    """
    for i, show in enumerate(query.shows):
        state = init_proof_state(query, i)
        proof: Tactic = show.proof
        state = proof.exec(thy, state)
        if len(state) != 0:
            print("Subgoals remaining:")
            print(state)
            raise AssertionError("check_proof: %s subgoals remaining" % len(state))
