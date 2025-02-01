"""Definitions of proof states."""

from collections.abc import Iterable

from osverify import os_struct
from osverify import os_term
from osverify.os_term import OSTerm, OSVar, VarContext, Visitor
from osverify import os_theory
from osverify.os_theory import OSTheory, OSContext
from osverify.os_util import indent
from osverify.os_query import Assumes, Shows
from osverify import os_query


class AbstractProofState:
    """Base class of proof states."""
    def num_unsolved(self) -> int:
        """Return the number of unsolved subgoals."""
        raise NotImplementedError("num_unsolved: %s" % type(self))

class EmptyProofState(AbstractProofState):
    """Corresponds to a proof state that is already resolved."""
    def __init__(self):
        pass

    def __str__(self):
        return "()"
    
    def num_unsolved(self) -> int:
        return 0

class CaseProofState(AbstractProofState):
    """Corresponds to proof states distinguished by datatype cases.
    
    Each case is specified constructor name, list of arguments to the
    constructor, and the resulting proof state. Arguments to the
    constructor are new names that can appear in the corresponding
    proof state.

    Attributes
    ----------
    cases : tuple[tuple[str, tuple[OSVar], AbstractProofState]]
        list of cases, each case is a triple (constr_name, params, state)

    """
    def __init__(self, cases: Iterable[tuple[str, tuple[OSVar], AbstractProofState]]):
        self.cases = tuple(cases)

    def __str__(self):
        res = ""
        first = True
        for constr_name, params, state in self.cases:
            if state.num_unsolved() > 0:
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
    
    def num_unsolved(self) -> int:
        res = 0
        for _, _, state in self.cases:
            res += state.num_unsolved()
        return res

class IndexProofState(AbstractProofState):
    """Corresponding to proof states distinguished by index.
    
    The cases are distinguished by an 1-based integer index.

    Attributes
    ----------
    cases : tuple[AbstractProofState]
        list of cases, with indices starting at 1    

    """
    def __init__(self, cases: Iterable[AbstractProofState]):
        self.cases = tuple(cases)

    def __str__(self):
        res = ""
        first = True
        for i, state in enumerate(self.cases):
            if state.num_unsolved() > 0:
                if not first:
                    res += "\n"
                res += "%s: {\n" % (i + 1)
                res += indent(str(state)) + "\n"
                res += "}"
                first = False
        return res
    
    def num_unsolved(self) -> int:
        res = 0
        for state in self.cases:
            res += state.num_unsolved()
        return res

class AssertProofState(AbstractProofState):
    """Proving and then using an assertion.

    This construct split the proof into two parts: first for asserting some
    proposition, and second for making use of that proposition (for example
    by putting it among the assumptions, but there are other possibilities).

    Attributes
    ----------
    assert_prop : OSTerm
        proposition to be asserted
    assert_case : AbstractProofState
        proof state for showing the asserted proposition
    remain_case : AbstractProofState
        proof state assuming the asserted proposition

    """
    def __init__(self, assert_prop: OSTerm, assert_case: AbstractProofState,
                 remain_case: AbstractProofState):
        self.assert_prop = assert_prop
        self.assert_case = assert_case
        self.remain_case = remain_case

    def __str__(self):
        res = ""
        first = True
        if self.assert_case.num_unsolved() > 0:
            res += "assert %s: {" % self.assert_prop
            res += indent(str(self.assert_case)) + "\n"
            res += "}"
            first = False
        if self.remain_case.num_unsolved() > 0:
            if not first:
                res += "\n"
            res += str(self.remain_case)
        return res
    
    def num_unsolved(self) -> int:
        return self.assert_case.num_unsolved() + self.remain_case.num_unsolved()

class ProofState(AbstractProofState):
    """Represents the intermediate state during a proof.
    
    Each proof state is given by list of type parameters, fixed variables,
    assumptions and conclusion (goal).

    Proof states are immutable. Tactics should return new proof states
    rather than modifying their inputs.

    Attributes
    ----------
    type_params : tuple[str]
        list of type parameters
    fixes : tuple[OSVar]
        list of fixed variables
    assumes : tuple[Assume]
        list of assumptions, each with optional name (default to empty string)
    concl : Shows
        current proof goal
    fixes_map : dict[str, OSType]
        mapping from variable names to their type
    graph : ClassificationGraph
        classification graph for the state

    """
    def __init__(self, type_params: Iterable[str],
                 fixes: Iterable[OSVar],
                 assumes: Iterable[Assumes],
                 concl: Shows, *, graph):
        self.type_params = tuple(type_params)
        self.fixes = tuple(fixes)
        assert all(isinstance(assume, Assumes) for assume in assumes)
        self.assumes = tuple(assumes)
        assert isinstance(concl, Shows)
        self.concl = concl
        self.graph = graph  # type ClassificationGraph
        self.fixes_map = dict((fix.name, fix.type) for fix in self.fixes)
        self.assume_map = dict((assume.name, assume.prop) for assume in self.assumes)

    def __str__(self):
        res = "state {\n"
        for type_param in self.type_params:
            res += indent("type %s;" % type_param, 2) + '\n'
        for var in self.fixes:
            res += indent("fixes %s: %s;" % (var.name, var.type), 2) + '\n'
        for assume in self.assumes:
            res += indent(str(assume), 2) + '\n'
        res += indent(str(self.concl), 2) + '\n'
        res += "}"
        return res
    
    def pprint_map(self) -> str:
        """Obtain pretty-printed form of the map of assumptions."""
        res = ""
        res += "Assumptions:\n"
        for assume in self.assumes:
            res += assume.pprint_map() + "\n"
        res += "Goal\n"
        res += self.concl.pprint_map()
        return res

    def export_meta(self) -> dict:
        """Export meta information trees to json format."""
        res = dict()
        assume_meta_lists: list[list[os_query.Meta]] = list()
        for assume in self.assumes:
            assume_meta_lists.append(assume.get_meta_list())
        assume_nodes = os_query.combine_meta_lists(assume_meta_lists)
        res["assume"] = []
        for node in assume_nodes:
            res["assume"].append(node.export())

        concl_nodes = os_query.combine_meta_lists([self.concl.get_meta_list()])
        res["concl"] = []
        for node in concl_nodes:
            res["concl"].append(node.export())
        return res

    def num_unsolved(self) -> int:
        return 1
    
    def __eq__(self, other):
        return isinstance(other, ProofState) and self.type_params == other.type_params and \
            self.fixes == other.fixes and self.assumes == other.assumes and self.concl == other.concl

    def get_context(self, thy: OSTheory) -> OSContext:
        var_ctxt = self.get_var_context()
        ctxt = OSContext(thy, var_ctxt)
        for assum in self.assumes:
            ctxt.process_fact(assum.prop)
        return ctxt

    def get_var_context(self) -> VarContext:
        var_ctxt = VarContext(self.fixes)
        var_ctxt.type_params = list(self.type_params)
        return var_ctxt
    
    def traverse(self, visitor: Visitor):
        """Traverse all assumptions and conclusion using the visitor."""
        var_ctxt = self.get_var_context()
        for _, assume in self.assume_map.items():
            assume.traverse(var_ctxt, visitor)
        self.concl.prop.traverse(var_ctxt, visitor)

    def traverse_skip_defining_eq(self, thy: OSTheory, visitor: Visitor):
        """Traverse while skipping defining equations using the visitor."""
        var_ctxt = self.get_var_context()
        for _, assume in self.assume_map.items():
            if not os_theory.is_defining_eq(thy, assume):
                assume.traverse(var_ctxt, visitor)
        self.concl.prop.traverse(var_ctxt, visitor)

    def check_vars(self, msg: str = ""):
        """Check validity of all variables in the state."""
        self.traverse(os_term.CheckVarVisitor(msg=msg))

    def check_type(self, thy: OSTheory):
        """Check type of all assumptions and conclusion."""
        var_ctxt = self.get_var_context()
        for _, assume in self.assume_map.items():
            os_theory.check_type(thy, assume, var_ctxt, os_struct.Bool)
        os_theory.check_type(thy, self.concl.prop, var_ctxt, os_struct.Bool)
