"""Unit test for tactics."""

import unittest

import osverify.os_seq
from osverify import os_tactics
from osverify.os_parser import load_theory, parse_term, parse_proof_state

core_thy = load_theory("core", verbose=False)
basic_thy = load_theory("basic", verbose=False)
seq_thy = load_theory("seq", verbose=False)

class OSTacticTest(unittest.TestCase):
    def testIntro(self):
        thy = core_thy

        state = parse_proof_state(
            thy, """state {
                fixes x: int32u;
                shows forall (int32u y) {
                    y > x
                }
            }"""
        )
        state = os_tactics.Intros(["z"]).exec(thy, state)

        state2 = parse_proof_state(
            thy, """state {
                fixes x: int32u;
                fixes z: int32u;
                shows z > x
            }"""
        )
        self.assertEqual(state, state2)

    def testIntroForallIn(self):
        thy = basic_thy

        state = parse_proof_state(
            thy, """state {
                fixes x: int32u;
                shows forall (int32u y) {
                    y >= 0 && y < 10 -> y > x
                }
            }"""
        )
        state = os_tactics.Intros(["y1"]).exec(thy, state)

        state2 = parse_proof_state(
            thy, """state {
                fixes x: int32u;
                fixes y1: int32u;
                assumes y1 >= 0 && y1 < 10;
                shows y1 > x
            }"""
        )
        self.assertEqual(state, state2)

    def testIntroNoName(self):
        thy = core_thy

        state = parse_proof_state(
            thy, """state {
                fixes x: int32u;
                fixes y: int32u;
                shows forall (int32u y) {
                    y > x
                }
            }"""
        )
        state = os_tactics.Intros().exec(thy, state)

        state2 = parse_proof_state(
            thy, """state {
                fixes x: int32u;
                fixes y: int32u;
                fixes y0: int32u;
                shows y0 > x
            }"""
        )
        self.assertEqual(state, state2)

    def testIntroNameConflict(self):
        thy = core_thy

        state = parse_proof_state(
            thy, """state {
                fixes x: int32u;
                fixes z: int32u;
                shows forall (int32u y) {
                    y > x
                }
            }"""
        )
        self.assertRaises(os_tactics.TacticException,
                          os_tactics.Intros("z").exec, thy, state)

    def testDefineVar(self):
        thy = basic_thy

        state = """
        state {
            type T;
            fixes xs: Seq<T>;
            fixes ys: Seq<T>;
            fixes zs: Seq<T>;
            shows xs ++ ys == zs
        }
        """
        state = parse_proof_state(thy, state)
        var_ctxt = state.get_var_context()

        state2 = """
        state {
            type T;
            fixes xs: Seq<T>;
            fixes ys: Seq<T>;
            fixes zs: Seq<T>;
            fixes u: Seq<T>;
            assumes u == xs ++ ys;
            shows u == zs
        }
        """

        res_state = os_tactics.DefineVar("u", parse_term(thy, var_ctxt, "xs ++ ys")).exec(thy, state)
        assert isinstance(res_state, os_tactics.ProofState)
        self.assertEqual(res_state, parse_proof_state(thy, state2))

    def testRewriteDefining(self):
        thy = basic_thy

        state = """
        state {
            fixes x: int32u;
            fixes y: int32u;
            fixes z: int32u;
            assumes A: x == y + z;
            shows x == z + y
        }
        """
        state = parse_proof_state(thy, state)

        state2 = """
        state {
            fixes x: int32u;
            fixes y: int32u;
            fixes z: int32u;
            assumes A: x == y + z;
            shows y + z == z + y
        }
        """

        res_state = os_tactics.RewriteDefine("A").exec(thy, state)
        assert isinstance(res_state, os_tactics.ProofState)
        self.assertEqual(res_state, parse_proof_state(thy, state2))

    def testRewrite(self):
        thy = seq_thy

        state = """
        state {
            fixes xs: Seq<int32u>;
            fixes ys: Seq<int32u>;
            shows 0 == |xs ++ ys|
        }
        """
        state = parse_proof_state(thy, state)

        state2 = """
        state {
            fixes xs: Seq<int32u>;
            fixes ys: Seq<int32u>;
            shows 0 == |xs| + |ys|
        }
        """
        res_state = os_tactics.Rewrite("seq_append_length").exec(thy, state)
        assert isinstance(res_state, os_tactics.ProofState)
        self.assertEqual(res_state, parse_proof_state(thy, state2))

    def testCasesVar(self):
        thy = basic_thy

        state = """
        state {
            type T;
            fixes x: Option<T>;
            fixes y: Option<T>;
            shows x == y
        }
        """
        state = parse_proof_state(thy, state)
        var_ctxt = state.get_var_context()

        state_none = """
        state {
            type T;
            fixes y: Option<T>;
            shows none == y
        }
        """

        state_some = """
        state {
            type T;
            fixes y: Option<T>;
            fixes val: T;
            shows some(val) == y
        }
        """

        res_states = os_tactics.Cases(parse_term(thy, var_ctxt, "x")).exec(thy, state)
        self.assertEqual(res_states.num_unsolved(), 2)
        assert isinstance(res_states, os_tactics.CaseProofState)
        self.assertEqual(res_states.cases[0][2], parse_proof_state(thy, state_none))
        self.assertEqual(res_states.cases[1][2], parse_proof_state(thy, state_some))

    def testCasesExpr(self):
        thy = basic_thy

        state = """
        state {
            type T;
            fixes i: int32u;
            fixes m: Map<int32u, Option<T> >;
            fixes zs: Option<T>;
            shows get(i, m) == zs
        }
        """
        state = parse_proof_state(thy, state)
        var_ctxt = state.get_var_context()

        state_none = """
        state {
            type T;
            fixes i: int32u;
            fixes m: Map<int32u, Option<T> >;
            fixes zs: Option<T>;
            assumes none == get(i, m);
            shows none == zs
        }
        """

        state_some = """
        state {
            type T;
            fixes i: int32u;
            fixes m: Map<int32u, Option<T> >;
            fixes zs: Option<T>;
            fixes val: T;
            assumes some(val) == get(i, m);
            shows some(val) == zs
        }
        """

        res_states = os_tactics.Cases(parse_term(thy, var_ctxt, "get(i, m)")).exec(thy, state)
        self.assertEqual(res_states.num_unsolved(), 2)
        assert isinstance(res_states, os_tactics.CaseProofState)
        self.assertEqual(res_states.cases[0][2], parse_proof_state(thy, state_none))
        self.assertEqual(res_states.cases[1][2], parse_proof_state(thy, state_some))

    def testCasesBool(self):
        thy = basic_thy

        state = """
        state {
            fixes x: int32u;
            shows x * x >= 0
        }
        """
        state = parse_proof_state(thy, state)
        var_ctxt = state.get_var_context()

        state_true = """
        state {
            fixes x: int32u;
            assumes x >= 0;
            shows x * x >= 0
        }
        """

        state_false = """
        state {
            fixes x: int32u;
            assumes x < 0;
            shows x * x >= 0
        }
        """
        res_states = os_tactics.Cases(parse_term(thy, var_ctxt, "x >= 0")).exec(thy, state)
        self.assertEqual(res_states.num_unsolved(), 2)
        assert isinstance(res_states, os_tactics.CaseProofState)
        self.assertEqual(res_states.cases[0][2], parse_proof_state(thy, state_true))
        self.assertEqual(res_states.cases[1][2], parse_proof_state(thy, state_false))

    def testModuloOp(self):
        thy = basic_thy
        state = parse_proof_state(
            thy, """state {
                fixes x: int32;
                fixes y: int32;
                assumes x == 10;
                assumes y == x % 3;
                shows y == 1   
            }
            """
        )
        res = osverify.os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(res.num_unsolved(), 0)


if __name__ == "__main__":
    unittest.main()
