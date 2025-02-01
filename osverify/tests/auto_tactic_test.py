"""Unit test for automation tactics."""

import unittest

from osverify import auto_tactics
from osverify.os_tactics import IndexProofState, ProofState
from osverify import os_parser
from osverify.os_parser import load_theory, parse_proof_state
from osverify import os_tactics
from osverify import os_simplify

def core_thy():
    return load_theory("core", verbose=False)

def basic_thy():
    return load_theory("basic", verbose=False)

class OSAutoTacticTest(unittest.TestCase):
    def testProcessLet(self):
        thy = core_thy()
        state = parse_proof_state(
            thy, """state {
                fixes prio1: int8u;
                fixes prio2: int8u;
                fixes n : int8u;
                assumes let x = prio1 & prio2 in 
                            x & n > 0
                        end;
                shows false 
            }
            """
        )
        res_state = auto_tactics.ProcessLet().exec(thy, state)
        state2 = parse_proof_state(
            thy, """state {
                fixes prio1: int8u;
                fixes prio2: int8u;
                fixes n : int8u;
                fixes x : int8u;
                assumes x == prio1 & prio2;
                assumes x & n > 0;
                shows false 
            }
            """
        )
        self.assertEqual(res_state, state2)

    def testProcessMultiLet(self):
        thy = core_thy()
        state = parse_proof_state(
            thy, """state {
                fixes prio1: int8u;
                fixes prio2: int8u;
                assumes let x = prio1 & prio2 in 
                            x > 0
                        end;
                assumes let x = prio1 & prio2 in 
                            x + 1 > 0
                        end;
                shows false 
            }
            """
        )
        res_state = auto_tactics.ApplyAll([auto_tactics.ProcessLet()]).exec(thy, state)
        state2 = parse_proof_state(
            thy, """state {
                fixes prio1: int8u;
                fixes prio2: int8u;
                fixes x: int8u;
                fixes x0: int8u;
                assumes x == prio1 & prio2;
                assumes x > 0;
                assumes x0 == prio1 & prio2;
                assumes x0 + 1 > 0;
                shows false
            }"""
        )
        self.assertEqual(res_state, state2)

    def testProcessExists1(self):
        thy = core_thy()
        state = parse_proof_state(
            thy, """state {
                assumes exists (int x) {
                    x > 0
                };
                shows false 
            }
            """
        )
        res_state = auto_tactics.ProcessExists().exec(thy, state)
        state2 = parse_proof_state(
            thy, """
                state {
                  fixes x: int;
                  assumes _A0: x > 0;
                  shows false
                }
            """
        )
        self.assertEqual(res_state, state2)

    def testProcessExists2(self):
        thy = core_thy()
        state = parse_proof_state(
            thy, """state {
                fixes d: int;
                assumes exists (int x, int y) {
                    exists (int z) {
                        exists (int g) {
                            x + y + z + d * g > 0
                        }
                    }
                };
                shows false 
            }
            """
        )
        res_state = auto_tactics.ApplyAll([auto_tactics.ProcessExists()]).exec(thy, state)
        state2 = parse_proof_state(
            thy, """state {
                fixes d: int;
                fixes x: int;
                fixes y: int;
                fixes z: int;
                fixes g: int;
                assumes _A0: x + y + z + d * g > 0;
                shows false
            }
            """
        )
        self.assertEqual(res_state, state2)

    def testProcessExists3(self):
        thy = basic_thy()
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes x: int;
                assumes exists (int x) {
                            x == 2
                        };
                assumes forall (int y) {
                            exists (int x) {
                                x == 2
                            }
                        };
                shows true
            }"""
        )
        res_state = auto_tactics.ProcessExists().exec(thy, state)
        state2 = os_parser.parse_proof_state(
            thy, """state {
                fixes x: int;
                fixes x0: int;
                assumes x0 == 2;
                assumes forall (int y) {
                            exists (int x) {
                                x == 2
                            }
                        };
                shows true
            }"""
        )
        self.assertEqual(res_state, state2)

    def testProcessSeqLiteral1(self):
        thy = basic_thy()
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes l1: Seq<int>;
                fixes l2: Seq<int>;
                assumes l2 == l1 ++ [];
                shows l1 == l2
            }"""
        )
        res_state = auto_tactics.ProcessSeqLiteral().exec(thy, state)
        state2 = os_parser.parse_proof_state(
            thy, """state {
                fixes l1: Seq<int>;
                fixes l2: Seq<int>;
                fixes l: Seq<int>;
                assumes _A1: |l| == 0;
                assumes _A0: l2 == l1 ++ l;
                shows l1 == l2
            }"""
        )
        self.assertEqual(res_state, state2)

    def testProcessSeqLiteral2(self):
        thy = basic_thy()
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes l1: Seq<int>;
                fixes l2: Seq<int>;
                assumes l2 == l1 ++ [1, 2, 3];
                shows |l2| == |l1| + 3
            }"""
        )
        res_state = auto_tactics.ProcessSeqLiteral().exec(thy, state)
        state2 = os_parser.parse_proof_state(
            thy, """state {
                fixes l1: Seq<int>;
                fixes l2: Seq<int>;
                fixes l: Seq<int>;
                assumes _A1: |l| == 3;
                assumes _A2: l[0] == 1;
                assumes _A3: l[1] == 2;
                assumes _A4: l[2] == 3;
                assumes _A0: l2 == l1 ++ l;
                shows |l2| == |l1| + 3
            }"""
        )
        self.assertEqual(res_state, state2)

    def testProcessSeqLiteral3(self):
        thy = basic_thy()
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes l1: Seq<int>;
                fixes l2: Seq<int>;
                assumes l2 == l1 ++ [] ++ [1, 2, 3];
                shows |l2| == |l1 ++ [4] ++ [5, 6]|
            }"""
        )
        res_state =  auto_tactics.ApplyAll([auto_tactics.ProcessSeqLiteral()]).exec(thy, state)
        state2 = os_parser.parse_proof_state(
            thy, """state {
                fixes l1: Seq<int>;
                fixes l2: Seq<int>;
                fixes l: Seq<int>;
                fixes l0: Seq<int>;
                fixes l3: Seq<int>;
                fixes l4: Seq<int>;
                assumes _A8: |l4| == 2;
                assumes _A9: l4[0] == 5;
                assumes _A10: l4[1] == 6;
                assumes _A6: |l3| == 1;
                assumes _A7: l3[0] == 4;
                assumes _A2: |l0| == 3;
                assumes _A3: l0[0] == 1;
                assumes _A4: l0[1] == 2;
                assumes _A5: l0[2] == 3;
                assumes _A1: |l| == 0;
                assumes _A0: l2 == l1 ++ l ++ l0;
                shows |l2| == |l1 ++ l3 ++ l4|
            }"""
        )
        self.assertEqual(res_state, state2)

    def testDistributeQuant(self):
        thy = basic_thy()
        state= os_parser.parse_proof_state(
            thy, """state {
                fixes x: int;
                assumes if (x == 1) {
                            forall (int x) {
                                if (x == 1) {
                                    forall (int x) {
                                        x == 2
                                    }
                                } else {
                                    exists (int x) {
                                        x == 3
                                    }
                                }
                            }
                        } else {
                            x != 1
                        };
                shows true
            }"""
        )
        res_state = auto_tactics.ApplyAll([
            auto_tactics.SplitConjAuto(),
            os_tactics.ApplyTransformerThy(os_simplify.Normalize)
        ]).exec(thy, state)

        state2 = os_parser.parse_proof_state(
            thy, """state {
                fixes x: int;
                assumes forall (int x0) {
                            forall (int x1) {
                                x == 1 -> x0 == 1 -> x1 == 2
                            } && exists (int x1) {
                                x == 1 -> x0 != 1 -> x1 == 3
                            }
                        };
                assumes x != 1 -> x != 1;
                shows true
            }"""
        )
        self.assertEqual(res_state, state2)

    def testDistributeQuant2(self):
        thy = basic_thy()
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes x: int;
                assumes if (x == 1) {
                            forall (int x) {
                                x == 2
                            } && x == 1
                        } else {
                            x != 1
                        };
                shows true
            }"""
        )
        res_state = auto_tactics.ApplyAll([
            auto_tactics.SplitConjAuto(),
            os_tactics.ApplyTransformerThy(os_simplify.Normalize)
        ]).exec(thy, state)

        state2 = os_parser.parse_proof_state(
            thy, """state {
                fixes x: int;
                assumes forall (int x0) {
                            x == 1 -> x0 == 2
                        };
                assumes x == 1 -> x == 1;
                assumes x != 1 -> x != 1;
                shows true
            }"""
        )
        self.assertEqual(res_state, state2)

    def testProcessExistsGoal(self):
        thy = basic_thy()
        state = os_parser.parse_proof_state(
            thy, """state {
                shows exists (int x) {
                    x > 1
                }
            }"""
        )
        res_state = auto_tactics.ProcessExistsGoal().exec(thy, state)

        state2 = os_parser.parse_proof_state(
            thy, """state {
                assumes forall (int x) {
                            x <= 1
                        };
                shows false
            }"""
        )
        self.assertEqual(res_state, state2)


if __name__ == "__main__":
    unittest.main()
