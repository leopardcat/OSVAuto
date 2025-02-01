"""Unit test for theory."""

import unittest

from osverify import os_parser
from osverify import os_struct
from osverify import os_term
from osverify import os_theory


basic_thy = os_parser.load_theory("basic", verbose=False)

class OSTheoryTest(unittest.TestCase):
    def testBasicTheoryTypes(self):
        thy = basic_thy

        # Datatypes in basic
        self.assertEqual(thy.datatypes.keys(), {"Prod", "Option"})

        # Axiomatic types in basic
        self.assertEqual(thy.axiom_types.keys(), {"Map", "Seq"})

    def testGetFuncType(self):
        thy = basic_thy
        ctxt = os_parser.parse_context(
            thy, """context {
                type E;
                type T;
                type K;
                type V
            }"""
        )

        data = [
            ("Option.id", ["T"], "Option<T> -> int"),
            ("none", ["T"], "Option<T>"),
            ("some", ["T"], "T -> Option<T>"),
            ("indom", ["K", "V"], "K -> Map<K, V> -> bool"),
            ("get", ["K", "V"], "K -> Map<K, V> -> V"),
        ]

        for func_name, expected_params, ty_str in data:
            func_ty, ty_params = thy.get_func_type(func_name)
            expected_ty = os_parser.parse_type(thy, ctxt, ty_str)
            self.assertEqual(func_ty, expected_ty, "%s != %s" % (func_ty, expected_ty))
            self.assertEqual(ty_params, tuple(expected_params))

    def testCheckType(self):
        thy = basic_thy

        os_theory.check_type(thy, os_term.OSNumber(1, os_struct.Int), dict(), os_struct.Int)

        # 1::bool
        self.assertRaises(os_theory.TypeCheckException, os_theory.check_type,
                          thy, os_term.OSNumber(1), dict(), os_struct.Bool)

        # false && (1::int)
        self.assertRaises(os_theory.TypeCheckException, os_theory.check_type,
                          thy, os_term.conj(os_term.false, os_term.OSNumber(1, os_struct.Int)), dict())

        # if (true) { 1 } else { 0 }
        self.assertRaises(os_theory.TypeCheckException, os_theory.check_type,
                          thy, os_term.ite(os_term.true, os_term.OSNumber(1), os_term.OSNumber(0)), dict(),
                          os_struct.Bool)

        # false && if (true) { 1 } else { 0 }
        self.assertRaises(os_theory.TypeCheckException, os_theory.check_type,
                          thy, os_term.conj(
                              os_term.false,
                              os_term.ite(os_term.true, os_term.OSNumber(1), os_term.OSNumber(0))), dict())


if __name__ == "__main__":
    unittest.main()
