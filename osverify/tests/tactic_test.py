"""Unit test for tactics."""

import unittest

from osverify import os_tactics
from osverify import os_parser

basic_thy = os_parser.load_theory("basic", verbose=False)

class OSTacticTest(unittest.TestCase):
    def testInduction(self):
        thy = basic_thy

        append_nil = """
        state {
            type T;
            fixes xs: List<T>;
            shows append(nil, xs) == xs
        }
        """
        state = os_parser.parse_proof_state(thy, append_nil)

        append_nil_cons = """
        state {
            type T;
            fixes ele : T;
            fixes rest : List<T>;
            assumes IH_rest: append(nil, rest) == rest;
            shows append(nil, cons(ele, rest)) == cons(ele, rest)
        }
        """

        res_states = os_tactics.Induction(os_tactics.InductionParam("xs", []), tuple()).exec(thy, state)
        self.assertEqual(res_states.num_unsolved(), 2)
        assert isinstance(res_states, os_tactics.CaseProofState)
        self.assertEqual(res_states.cases[0][2], os_parser.parse_proof_state(
            thy, "state { type T; shows append(nil::List<T>, nil) == nil }"))
        self.assertEqual(res_states.cases[1][2], os_parser.parse_proof_state(
            thy, append_nil_cons))
        
        append_assoc = """
        state {
            type T;
            fixes xs: List<T>;
            fixes ys: List<T>;
            fixes zs: List<T>;
            shows append(append(xs, ys), zs) == append(xs, append(ys, zs))
        }
        """
        state = os_parser.parse_proof_state(thy, append_assoc)

        append_assoc_nil = """
        state {
            type T;
            fixes ys : List<T>;
            fixes zs : List<T>;
            shows append(append(nil, ys), zs) == append(nil, append(ys, zs))
        }
        """

        append_assoc_cons = """
        state {
            type T;
            fixes ys : List<T>;
            fixes zs : List<T>;
            fixes ele : T;
            fixes rest : List<T>;
            assumes IH_rest: append(append(rest, ys), zs) == append(rest, append(ys, zs));
            shows append(append(cons(ele, rest), ys), zs) == append(cons(ele, rest), append(ys, zs))
        }
        """
        res_states = os_tactics.Induction(os_tactics.InductionParam("xs", []), tuple()).exec(thy, state)
        self.assertEqual(res_states.num_unsolved(), 2)
        assert isinstance(res_states, os_tactics.CaseProofState)
        self.assertEqual(res_states.cases[0][2], os_parser.parse_proof_state(
            thy, append_assoc_nil))
        self.assertEqual(res_states.cases[1][2], os_parser.parse_proof_state(
            thy, append_assoc_cons))
