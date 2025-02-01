"""Unit test for sequence theory."""

import unittest

from osverify import os_struct
from osverify import os_term
from osverify import os_parser
from osverify import os_seq, os_model, os_z3wrapper
from osverify.os_theory import OSTheory
from osverify.os_proofstate import ProofState
from osverify.graph import ConditionalTerm, ClassificationGraph, GraphNode, \
    MapNode, SeqNode


def seq_thy():
    return os_parser.load_theory("seq", verbose=False)

class SeqTest(unittest.TestCase):
    def solve_model(self, thy: OSTheory, state: ProofState, *,
                    verbose: bool = False) -> os_model.Model:
        """Solve a list of constraints for a Seq model."""
        try:
            res = os_seq.SeqAuto().exec(thy, state)
        except os_z3wrapper.SMTException as e:
            # print("--- State ---")
            # print(e.state)
            print("--- Original model ---")
            print(e.z3_model)
            model = os_model.convert_model(thy, e.state, e.z3_model)
            print("--- Converted model ---")
            print(model)
            raise e

    def testParseSeq(self):
        thy = seq_thy()

        ctxt = os_parser.parse_context(
            thy, """context {
                type T;
                fixes xs: Seq<T>;
                fixes ys: Seq<T>;
                fixes i: int;
                fixes j: int;
                fixes t: T
            }"""
        )


    def testVisitIndexWithCond(self):
        thy = seq_thy()

        ctxt = os_parser.parse_context(
            thy, """context {
                fixes m: Map<int, Seq<int> >;
                fixes k: int;
                fixes i: int
            }""")

        t = os_parser.parse_term(
            thy, ctxt, """
                exists (int j) {
                    get(i, m)[j] == k
                }
            """)
        new_insts: dict[GraphNode, list[ConditionalTerm]] = dict()
        graph = ClassificationGraph(thy)
        os_seq.visit_index_with_cond(ctxt, t, 0, tuple(), graph, new_insts)

        m = os_parser.parse_term(thy, ctxt, "m")
        i = os_parser.parse_term(thy, ctxt, "i")
        m_i = os_parser.parse_term(thy, ctxt, "get(i, m)")
        self.assertEqual(new_insts, {MapNode(m): [ConditionalTerm(tuple(), 0, i)],
                                     SeqNode(m_i): []})

    def testExample1(self):
        thy = seq_thy()

        # Running example in "A Solver for Arrays with Concatenation"
        os_parser.parse_theory_items(
            thy, """
            axiomfunc P: int32u -> bool
            """
        )

        state = os_parser.parse_proof_state(
            thy, """state {
                fixes a: Seq<int32u>;
                fixes b: Seq<int32u>;
                fixes c: Seq<int32u>;
                fixes d: Seq<int32u>;
                assumes c == a ++ b;
                assumes d == b ++ a;
                assumes forall (int i) {
                    i >= 0 && i < |c| -> P(c[i])
                };
                shows forall (int k) {
                    k >= 0 && k < |d| -> P(d[k])
                }
            }"""
        )

        state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(state.num_unsolved(), 0)

    def testExample1Int32(self):
        # 32-bit version of Example 1, with known array lengths
        thy = seq_thy()

        os_parser.parse_theory_items(
            thy, """
            axiomfunc P: int32u -> bool
            """
        )

        state = os_parser.parse_proof_state(
            thy, """state {
                fixes a: Seq<int32u>;
                fixes b: Seq<int32u>;
                fixes c: Seq<int32u>;
                fixes d: Seq<int32u>;
                assumes c == a ++ b;
                assumes d == b ++ a;
                assumes forall (int i) {
                    i >= 0 && i < |a| + |b| ->
                    P(c[i])
                };
                shows forall (int k) {
                    k >= 0 && k < |a| + |b| ->
                    P(d[k])
                }
            }"""
        )

        state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(state.num_unsolved(), 0)

    def testExample1WithStruct(self):
        # Version of Example 1 with structures. This test only checks that
        # structure fields are considered atomic terms.
        thy = seq_thy()

        os_parser.parse_theory_items(
            thy, """
            axiomfunc P: int32u -> bool
            """
        )

        os_parser.parse_theory_items(
            thy, """
            struct Global {
                Seq<int32u> a;
                Seq<int32u> b;
            }
            """
        )

        state = os_parser.parse_proof_state(
            thy, """state {
                fixes global: Global;
                fixes c: Seq<int32u>;
                fixes d: Seq<int32u>;
                assumes c == global.a++global.b;
                assumes d == global.b++global.a;
                assumes forall (int i) {
                    i >= 0 && i < |global.a| + |global.b| ->
                    P(c[i])
                };
                shows forall (int k) {
                    k >= 0 && k < |global.a| + |global.b| ->
                    P(d[k])
                }
            }"""
        )

        state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(state.num_unsolved(), 0)

    def testExample1WithStructUpdate(self):
        # Version of Example 1 with structure literals.
        thy = seq_thy()

        os_parser.parse_theory_items(
            thy, """
            axiomfunc P: int32u -> bool
            """
        )

        os_parser.parse_theory_items(
            thy, """
            struct Global {
                Seq<int32u> a;
                Seq<int32u> b;
            }
            """
        )

        state = os_parser.parse_proof_state(
            thy, """state {
                fixes global: Global;
                fixes global2: Global;
                assumes global2 == Global{{
                    a: global.a ++ global.b,
                    b: global.b ++ global.a
                }};
                assumes forall (int i) {
                    i >= 0 && i < |global.a| + |global.b| ->
                    P(global2.a[i])
                };
                shows forall (int k) {
                    k >= 0 && k < |global.a| + |global.b| ->
                    P(global2.b[k])
                }
            }"""
        )

        state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(state.num_unsolved(), 0)


    def testExample1WithMap(self):
        # Version of Example 1 with maps.
        thy = seq_thy()

        os_parser.parse_theory_items(
            thy, """
            axiomfunc P: int32u -> bool
            """
        )

        state = os_parser.parse_proof_state(
            thy, """state {
                fixes global: Map<int, Seq<int32u> >;
                assumes get(2, global) == get(0, global) ++  get(1, global);
                assumes get(3, global) == get(1, global) ++  get(0, global);
                assumes forall (int i) {
                    i >= 0 && i < |get(0, global)| + |get(1, global)| ->
                    P(get(2, global)[i])
                };
                shows forall (int k) {
                    k >= 0 && k < |get(0, global)| + |get(1, global)| ->
                    P(get(3, global)[k])
                }
            }"""
        )

        state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(state.num_unsolved(), 0)

    def test2dSequence(self):
        # In this example, c and d are formed by appending a and b
        # in the vertical direction.
        thy = seq_thy()

        os_parser.parse_theory_items(
            thy, """
            axiomfunc P: int32u -> bool
            """
        )

        state = os_parser.parse_proof_state(
            thy, """state {
                fixes a: Seq< Seq<int32u> >;
                fixes b: Seq< Seq<int32u> >;
                fixes c: Seq< Seq<int32u> >;
                fixes d: Seq< Seq<int32u> >;
                assumes c == a ++ b;
                assumes d == b ++ a;
                assumes forall (int i, int j) {
                    i >= 0 && i < |c| &&
                    j >= 0 && j < |c[i]| ->
                    P(c[i][j])
                };
                shows forall (int k, int l) {
                    k >= 0 && k < |d| &&
                    l >= 0 && l < |d[k]| ->
                    P(d[k][l])
                }
            }"""
        )

        state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(state.num_unsolved(), 0)

    def test2dSequence2(self):
        # In this example, c and d are formed by appending each (sequence)
        # element of a and b.
        thy = seq_thy()

        os_parser.parse_theory_items(
            thy, """
            axiomfunc P: int32u -> bool
            """
        )

        state = os_parser.parse_proof_state(
            thy, """state {
                fixes a: Seq< Seq<int32u> >;
                fixes b: Seq< Seq<int32u> >;
                fixes c: Seq< Seq<int32u> >;
                fixes d: Seq< Seq<int32u> >;
                assumes |a| == |b|;
                assumes |c| == |a|;
                assumes forall (int i) {
                    i >= 0 && i < |c| ->
                    |c[i]| == |a[i] ++ b[i]|
                };
                assumes forall (int i, int j) {
                    i >= 0 && i < |c| ->
                    j >= 0 && j < |c[i]| ->
                    c[i][j] == (a[i] ++ b[i])[j]
                };
                assumes |d| == |a|;
                assumes forall (int i) {
                    i >= 0 && i < |d| ->
                    |d[i]| == |b[i] ++ a[i]|
                };
                assumes forall (int i, int j) {
                    i >= 0 && i < |d| ->
                    j >= 0 && j < |d[i]| ->
                    d[i][j] == (b[i] ++ a[i])[j]
                };
                assumes forall (int i, int j) {
                    i >= 0 && i < |c| &&
                    j >= 0 && j < |c[i]| ->
                    P(c[i][j])
                };
                shows forall (int k, int l) {
                    k >= 0 && k < |d| &&
                    l >= 0 && l < |d[k]| ->
                    P(d[k][l])
                }
            }"""
        )

        state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(state.num_unsolved(), 0)

    def test2dSequence3(self):
        thy = seq_thy()

        os_parser.parse_theory_items(
            thy, """
            axiomfunc P: int32u -> bool
            """
        )

        state = os_parser.parse_proof_state(
            thy, """state {
                fixes a: Seq< Seq<int32u> >;
                fixes b: Seq< Seq<int32u> >;
                fixes c: Seq< Seq<int32u> >;
                fixes d: Seq< Seq<int32u> >;
                assumes c[0] == a[0] ++ b[0];
                assumes d[0] == b[0] ++ a[0];
                assumes forall (int i) {
                    i >= 0 && i < |c[0]| ->
                    P(c[0][i])
                };
                shows forall (int i) {
                    i >= 0 && i < |d[0]| ->
                    P(d[0][i])
                }
            }"""
        )
        state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(state.num_unsolved(), 0)

    def testSeqInListRemoveWithMap(self):
        thy = seq_thy()

        state = os_parser.parse_proof_state(
            thy, """state {
                type T;
                fixes m: Seq<Seq<T> >;
                assumes forall (int i, int j) {
                    0 <= i && i < |m[0]| &&
                    0 <= j && j < |m[0]| && i != j ->
                    m[0][i] != m[0][j]
                };
                fixes k: int;
                assumes 0 <= k && k < |m[0]|;
                assumes m[1] == seq_remove(k, m[0]);
                shows forall (int j) {
                    0 <= j && j < |m[1]| ->
                    m[1][j] != m[0][k]
                }
            }"""
        )
        state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(state.num_unsolved(), 0)

    def testSeqExists(self):
        thy = seq_thy()

        os_parser.parse_theory_items(
            thy, """
            axiomfunc P: int32u -> bool
            """
        )

        state = os_parser.parse_proof_state(
            thy, """state {
                fixes l: Seq<int32u>;
                assumes exists (int i) {
                    i >= 0 && i < |l| &&
                    P(l[i])
                };
                assumes |l| == 1;
                shows P(l[0])
            }"""
        )
        state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(state.num_unsolved(), 0)

    def testSeqSlice(self):
        thy = seq_thy()
        os_parser.parse_theory_items(
            thy, """
            axiomfunc P: int32u -> bool
            """
        )
        state = os_parser.parse_proof_state(
            thy, """state {
               fixes l: Seq<int32u>;
               assumes forall (int i) {
                    i >= 0 && i < |l| - 1 -> 
                    P(seq_slice(1, |l|, l)[i])
               };
               shows forall (int i){
                    i >= 1 && i < |l| -> 
                    P(l[i])
               }
           }"""
        )
        state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(state.num_unsolved(), 0)

    def testQuantifiedSeqEqual2(self):
        thy = seq_thy()

        state = os_parser.parse_proof_state(
            thy, """state {
                fixes l1: Seq< Seq<int32u> >;
                fixes l2: Seq< Seq<int32u> >;
                assumes forall (int i) {
                    i >= 0 && i < min(|l1|, |l2|) ->
                    l1[i] == l2[i]
                };
                assumes l1 == l2;
                assumes |l1| > 0;
                assumes |l1[0]| > 0;
                shows l1[0][0] == l2[0][0]
            }"""
        )
        state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(state.num_unsolved(), 0)

    def testNestedForall(self):
        thy = seq_thy()
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes x: int32;
                fixes y: int32;
                assumes forall (int x) {
                    forall (int y) {
                        x > 0 && y > 0 -> x * y > 0 
                    }
                };
                assumes x == 2;
                assumes y == 3;
                shows x * y > 0
            }"""
        )
        state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(state.num_unsolved(), 0)

    def testSeqIndexPattern(self):
        thy = seq_thy()
        os_parser.parse_theory_items(
            thy, """
            axiomfunc P: int -> int
            """
        )
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes x: int32u;
                fixes l1: Seq<int32u>;
                fixes k: int;
                assumes forall (int x) {
                    0 <= P(x) && P(x) <= |l1| -> l1[P(x)] > 0
                };
                assumes 0 <= P(k) && P(k) <= |l1|;
                shows l1[P(k)] > 0
            }"""
        )
        state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(state.num_unsolved(), 0)

    def testMapIndexPattern(self):
        thy = seq_thy()
        os_parser.parse_theory_items(
            thy, """
            axiomfunc P: int -> int
            """
        )
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes x: int32u;
                fixes m: Map<int, int32u>;
                fixes k: int;
                assumes forall (int x) {
                    get(P(x), m) > 0
                };
                shows get(P(k), m) > 0
            }"""
        )
        state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(state.num_unsolved(), 0)

    def testSeqRevRev(self):
        thy = seq_thy()
        os_parser.parse_theory_items(
            thy, """
            axiomfunc P: int -> bool
            """
        )
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes l1: Seq<int>;
                shows l1 == seq_rev(seq_rev(l1))
            }"""
        )
        state = os_seq.SeqAuto().exec(thy, state)

    def testSeqRevAppend(self):
        thy = seq_thy()
        os_parser.parse_theory_items(
            thy, """
            axiomfunc P: int -> bool
            """
        )
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes l1: Seq<int>;
                fixes l2: Seq<int>;
                shows forall (int i) {
                          0 <= i && i < |l1| + |l2| ->
                          seq_rev(l1 ++ l2)[i] == (seq_rev(l2) ++ seq_rev(l1))[i]
                      }
            }"""
        )
        state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(state.num_unsolved(), 0)

    def testSeqEQ3(self):
        thy = seq_thy()
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes l11: Seq<int>;
                fixes l12: Seq<int>;
                fixes v1: int;
                fixes l21: Seq<int>;
                fixes l22: Seq<int>;
                fixes v2: int;
                assumes l11 ++ v1 :: l12 ==
                        l21 ++ v2 :: l22;
                assumes |l11| == |l21|;
                shows l11 == l21 && v1 == v2 && l12 == l22
            }"""
        )
        res_state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(res_state.num_unsolved(), 0)

    def testForallInIf(self):
        thy = seq_thy()
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes l1: Seq<int>;
                fixes l2: Seq<int>;
                assumes if (|l1| == 5) {
                            |l1| == |l2| &&
                            forall (int i) {
                                i < |l1| -> l1[i] == l2[i]
                            }
                        } else {
                            false
                        };
                shows seq_rev(l1 ++ l2) == seq_rev(l2) ++ seq_rev(l1)
            }"""
        )
        state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(state.num_unsolved(), 0)

    def testForallRange(self):
        thy = seq_thy()
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes l: Seq<int32u>;
                assumes |l| == 32;
                assumes forall (int32u i in range(0, 32)) {
                    l[int(i)] > 0
                };
                shows forall (int32u i in range(0, 16)) {
                    l[int(i)] > 0
                }
            }"""
        )
        state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(state.num_unsolved(), 0)

    def testForallExists(self):
        thy = seq_thy()
        os_parser.parse_theory_items(
            thy, """
            axiomfunc P: int32u -> bool
            """
        )
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes l: Seq<Seq<int32u> >;
                assumes forall (int i) {
                            exists (int j) {
                                P(l[i][j])
                            }
                        };
                shows   exists (int j) {
                            P(l[1][j])
                        }
            }"""
        )
        state = os_seq.SeqAuto().exec(thy, state)
        self.assertEqual(state.num_unsolved(), 0)


if __name__ == "__main__":
    unittest.main()
