"""Unit test for terms."""

import unittest

from osverify import os_parser
from osverify import os_term


core_thy = os_parser.load_theory("core", verbose=False)
basic_thy = os_parser.load_theory("basic", verbose=False)

class OSTermTest(unittest.TestCase):
    def testParseTerm(self):
        thy = core_thy
        ctxt = os_parser.parse_context(
            thy, "context { type S; type T; fixes x : S; fixes xs : List<S> }"
        )

        # Each test case is in the form (s, res), where s is the term
        # to be parsed, and res is the repr output of the term.
        test_data = [
            ("x",
             "OSVar('x', S)"),

            ("?x::?S",
             "OSVar('?x', ?S)"),

            ("cons(x, xs)",
             "OSFun('cons', OSVar('x', S), OSVar('xs', List<S>), List<S>)"),

            # The following tests type inference for datatype constructors
            ("cons(?x::?S, ?xs)",
             "OSFun('cons', OSVar('?x', ?S), OSVar('?xs', List<?S>), List<?S>)"),

            ("cons(?x, ?xs)::List<?S>",
             "OSFun('cons', OSVar('?x', ?S), OSVar('?xs', List<?S>), List<?S>)"),
        ]

        for s, res in test_data:
            t = os_parser.parse_term(thy, ctxt, s)
            self.assertEqual(repr(t), res)

    def testParseSwitch(self):
        thy = basic_thy
        ctxt = os_parser.parse_context(
            thy, "context { type S; type T; fixes x : S; fixes xs : List<S> }"
        )

        t = os_parser.parse_term(
            thy, ctxt,
            """
            switch (xs) {
                case nil:
                    0::nat;
                case cons(i, xs2):
                    succ(length(xs));
            }
            """
        )
        assert isinstance(t, os_term.OSSwitch)
        self.assertEqual(repr(t.switch_expr), "OSVar('xs', List<S>)")
        self.assertEqual(repr(t.branches[0]), "OSSwitchBranchCase(OSFun('nil', List<S>), OSNumber(0, nat))")

    def testGetVars(self):
        thy = basic_thy
        ctxt = os_parser.parse_context(
            thy, "context { type S; type T; fixes x : S; fixes xs : List<S> }"
        )

        xs = os_parser.parse_term(thy, ctxt, "xs")

        t = os_parser.parse_term(
            thy, ctxt,
            """
            switch (xs) {
                case nil:
                    0::nat;
                case cons(i, xs2):
                    succ(length(xs));
            }
            """
        )
        ty_vars, vars = t.get_vars()
        self.assertEqual(ty_vars, ('S',))
        self.assertEqual(vars, (xs,))

    def testGetVars2(self):
        thy = basic_thy
        ctxt = os_parser.parse_context(
            thy, "context { fixes prio : int32u; fixes rtbl : int32u[] }"
        )

        prio = os_parser.parse_term(thy, ctxt, "prio")
        rtbl = os_parser.parse_term(thy, ctxt, "rtbl")

        t = os_parser.parse_term(
            thy, ctxt,
            """
            let x = prio & 7 in
                rtbl[prio >> 3] & (1 << x) == 1 << x
            end
            """
        )
        ty_vars, vars = t.get_vars()
        self.assertEqual(ty_vars, tuple())
        self.assertEqual(vars, (prio, rtbl))

    def testMakeSchematic(self):
        thy = basic_thy
        ctxt = os_parser.parse_context(
            thy, "context { type S; type T; fixes x : S; fixes xs : List<S> }"
        )

        x = os_parser.parse_term(thy, ctxt, "x")
        xs = os_parser.parse_term(thy, ctxt, "xs")

        # Test 1
        t = os_parser.parse_term(thy, ctxt, "x")
        t2 = t.make_schematic(['S'], [x])
        self.assertEqual(repr(t2), "OSVar('?x', ?S)")

        # Test 2
        t = os_parser.parse_term(thy, ctxt, "x")
        t2 = t.make_schematic(['S'], [])
        self.assertEqual(repr(t2), "OSVar('x', ?S)")

        # Test 3
        t = os_parser.parse_term(thy, ctxt, "cons(x, xs)")
        t2 = t.make_schematic(['S'], [x, xs])
        self.assertEqual(repr(t2), "OSFun('cons', OSVar('?x', ?S), OSVar('?xs', List<?S>), List<?S>)")

    def testSubstVarCapture(self):
        # Test that variable capture is avoided during substitution
        thy = basic_thy
        ctxt = os_parser.parse_context(
            thy, "context { type K; type V }"
        )
        ctxt2 = os_parser.parse_context(
            thy, "context { type K; type V; fixes k: Map<K, V> }"
        )

        t = os_parser.parse_term(thy, ctxt, "forall (K k) { !indom(k, ?m::Map<K, V>) }")
        k = os_parser.parse_term(thy, ctxt2, "k")
        inst = {"?m": k}
        res_t = os_parser.parse_term(thy, ctxt2, "forall (K k0) { !indom(k0, k) }")
        self.assertEqual(t.subst(inst), res_t)


if __name__ == "__main__":
    unittest.main()
