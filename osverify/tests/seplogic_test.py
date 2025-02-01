"""Unit tests for separation logic."""

import unittest

from osverify import os_struct
from osverify import os_term
from osverify import os_parser
from osverify import os_seplogic
from osverify.os_parser import parse_term, parse_sep
from osverify.os_seplogic import SepFun, SepConj, sll


basic_thy = os_parser.load_theory("basic", verbose=False)

class SepLogicTest(unittest.TestCase):
    def testParseAssertion(self):
        thy = basic_thy
        ctxt = os_parser.parse_context(
            thy, """
            context {
                fixes p: int32u;
                fixes q: int32u;
                fixes lst: Seq<int32u>
            }
            """
        )

        p = os_term.OSVar("p", type=os_struct.Int32U)
        q = os_term.OSVar("q", type=os_struct.Int32U)
        lst = os_term.OSVar("lst", type=os_struct.SeqType(os_struct.Int32U))
        nil = os_term.SeqLiteral([], type=os_struct.SeqType(os_struct.Int32U))

        test_data = [
            ("sll(p, lst)", SepConj(sll(p, lst))),

            ("sll(p, lst); sll(q, []@Seq<int32u>)",
             SepConj(sll(p, lst), sll(q, nil)))
        ]

        for s, res in test_data:
            t = parse_sep(thy, ctxt, s)
            self.assertEqual(t, res)

    def testReduceEntail(self):
        thy = basic_thy
        ctxt = os_parser.parse_context(
            thy, """
            context {
                fixes v: int32u;
                fixes w: int32u;
                fixes l1: Seq<int32u>;
                fixes l2: Seq<int32u>;
                fixes l_free: Seq<int32u>
            }
            """
        )

        entail = os_seplogic.Entails(
            left=parse_sep(thy, ctxt, "sll(w, l1); sll(v, l2)"),
            right=parse_sep(thy, ctxt, "sll(w, seq_rev(l_free))"),
            assums=[parse_term(thy, ctxt, "v == 0"),
                    parse_term(thy, ctxt, "l_free == seq_append(seq_rev(l1), l2)")],
            goals=[]
        )

        entail2 = os_seplogic.reduceEntail(entail)
        expected_entail2 = os_seplogic.Entails(
            left=SepConj(),
            right=SepConj(),
            assums=[],
            goals=[parse_term(thy, ctxt, "l1 == seq_rev(seq_append(seq_rev(l1), []@Seq<int32u>))")]
        )
        self.assertEqual(entail2, expected_entail2)


if __name__ == "__main__":
    unittest.main()
