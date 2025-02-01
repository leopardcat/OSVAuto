"""Unit test for Z3 conversion"""

import unittest

from osverify import os_theory
from osverify import os_parser
from osverify.os_z3wrapper import solve, UnsatResult, ModelResult
from osverify.os_proofstate import ProofState


def initTheory() -> os_theory.OSTheory:
    return os_parser.load_theory("basic", verbose=False)

def seqTheory() -> os_theory.OSTheory:
    return os_parser.load_theory("seq", verbose=False)

class Z3WrapperTest(unittest.TestCase):
    def solve_query(self, thy: os_theory.OSTheory, state: ProofState):
        """Solve the given query, return whether the query can be proved."""
        res = solve(thy, state)
        if isinstance(res, UnsatResult):
            return True
        elif isinstance(res, ModelResult):
            return False
        else:
            raise NotImplementedError

    def testSeq(self):
        thy = seqTheory()

        # Running example in "A Solver for Arrays with Concatenation"
        os_parser.parse_theory_items(
            thy, """
            axiomfunc P: int32u -> bool
            """
        )

        state = """
        state {
            fixes a: Seq<int32u>;
            fixes b: Seq<int32u>;
            fixes k: int;
            assumes k + |a| >= 0 &&
                    k + |a| < |a| + |b| ->
                    k + |a| >= |a| &&
                    k + |a| < |a| + |b| ->
                    P(b[k + |a| - |a|]);
            assumes k >= 0 && k < |b| + |a|;
            assumes k >= 0 && k < |b|;
            shows P(b[k])
        }
        """
        state = os_parser.parse_proof_state(thy, state)
        self.assertTrue(self.solve_query(thy, state))


if __name__ == "__main__":
    unittest.main()
