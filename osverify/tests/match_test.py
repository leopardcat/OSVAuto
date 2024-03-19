"""Unit test for term matching."""

import unittest

from osverify import os_parser
from osverify import os_match

basic_thy = os_parser.load_theory("basic", verbose=False)

class OSMatchTest(unittest.TestCase):
    def testMatch(self):
        thy = basic_thy
        ctxt = os_parser.parse_context(
            thy, "context { type S; type T; fixes x : S; fixes xs : List<S> }"
        )

        # Each test case is in the form (pat, t, res), where pat is the pattern
        # to be matched and t is the concrete term, res is the expected return
        # value (whether match is successful).
        test_data = [
            ("?x::?S", "x", True),
            ("?x::S", "x", True),
            ("?x::T", "x", False),
            ("nil::List<?S>", "nil::List<S>", True),
            ("cons(?x::?S, ?xs)", "cons(x, xs)", True),
        ]

        for s, s2, res in test_data:
            t = os_parser.parse_term(thy, ctxt, s)
            t2 = os_parser.parse_term(thy, ctxt, s2)
            tyinst, inst = dict(), dict()
            if res:
                self.assertTrue(os_match.match(thy, t, t2, tyinst, inst))
                self.assertEqual(t.subst_type(tyinst).subst(inst), t2)
            else:
                self.assertFalse(os_match.match(thy, t, t2, tyinst, inst))


if __name__ == "__main__":
    unittest.main()
