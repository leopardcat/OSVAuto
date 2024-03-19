"""Unit test for types."""

from typing import Dict
import unittest

from osverify.os_struct import OSType
from osverify import os_parser
from osverify import os_theory


core_thy = os_parser.load_theory("core", verbose=False)

class OSTypeTest(unittest.TestCase):
    def testMakeSchematic(self):
        thy = core_thy
        ctxt = os_parser.parse_context(
            thy, "context { type S; type T }"
        )

        # In the following tests, replace T by schematic type variables
        test_data = [
            ("T", "?T"),
            ("List<T>", "List<?T>"),
            ("Prod<S, T>", "Prod<S, ?T>"),
        ]

        for s, s2 in test_data:
            ty = os_parser.parse_type(thy, ctxt, s)
            res = os_parser.parse_type(thy, ctxt, s2)
            self.assertEqual(ty.make_schematic({'T'}), res)

    def testTypeMatch(self):
        thy = core_thy
        ctxt = os_parser.parse_context(
            thy, "context { type S; type T }"
        )

        # Each test case is in the form (pat, t, res), where pat is the pattern
        # to be matched and t is the concrete type, res is the expected return
        # value (whether match is successful).
        test_data = [
            ("?T", "S", True),
            ("S", "S", True),
            ("T", "S", False),
            ("Prod<?T, T>", "Prod<S, T>", True),
            ("Prod<?T, ?T>", "Prod<S, T>", False),
            ("Prod<?T, ?T>", "Prod<S, T>", False),
            ("Prod<?S, ?T>", "Prod<S, T>", True),
        ]

        for s, s2, res in test_data:
            ty = os_parser.parse_type(thy, ctxt, s)
            ty2 = os_parser.parse_type(thy, ctxt, s2)
            tyinst: Dict[str, OSType] = dict()
            if res:
                self.assertTrue(ty.match(ty2, tyinst))
                self.assertEqual(ty.subst(tyinst), ty2)
            else:
                self.assertFalse(ty.match(ty2, tyinst))


if __name__ == "__main__":
    unittest.main()
