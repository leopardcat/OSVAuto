"""Unit test for terms."""

import unittest

from osverify import os_parser
from osverify.os_parser import parse_term, parse_context
from osverify import os_term


def basic_thy():
    return os_parser.load_theory("basic", verbose=False)

class OSTermTest(unittest.TestCase):
    def testParseTerm(self):
        thy = basic_thy()
        ctxt = parse_context(
            thy, """context {
                type S;
                type T;
                fixes x : S;
                fixes xs : Seq<S>
            }"""
        )

        # Each test case is in the form (s, res), where s is the term
        # to be parsed, and res is the repr output of the term.
        test_data = [
            ("x",
             "OSVar('x', S)"),

            ("?x@?S",
             "OSVar('?x', ?S)"),

            ("some(x)",
             "OSFun('some', OSVar('x', S), Option<S>)"),

            # The following tests type inference for datatype constructors
            ("some(?x@?S)",
             "OSFun('some', OSVar('?x', ?S), Option<?S>)"),

            ("some(?x)@Option<?S>",
             "OSFun('some', OSVar('?x', ?S), Option<?S>)"),
        ]

        for s, res in test_data:
            t = parse_term(thy, ctxt, s)
            self.assertEqual(repr(t), res)

    def testParseSwitch(self):
        thy = basic_thy()
        ctxt = parse_context(
            thy, """context {
                type S;
                type T;
                fixes x : S;
                fixes y : Option<T>
            }"""
        )

        t = parse_term(
            thy, ctxt,
            """
            switch (y) {
                case none:
                    0@int;
                case some(x):
                    1@int;
            }
            """
        )
        assert isinstance(t, os_term.OSSwitch)
        self.assertEqual(repr(t.switch_expr), "OSVar('y', Option<T>)")
        self.assertEqual(repr(t.branches[0]), "OSSwitchBranchCase(OSFun('none', Option<T>), OSNumber(0, int))")

    def testParseStructUpdateGen(self):
        thy = basic_thy()
        os_parser.parse_theory_items(
            thy, """
            struct A {
                int32u x;
                Seq<int32u> ys;
            }
            """
        )
        os_parser.parse_theory_items(
            thy, """
            struct B {
                Seq<A> as;
            }
            """
        )
        ctxt = parse_context(
            thy, """context {
                fixes a: A;
                fixes b: B
            }"""
        )

        test_data = [
            "a{|x := 3|}",
            "a{|ys[0] := 3|}",
            "b{|as[0].x := 3|}",
            "b{|as[0].ys[1] := 3|}",
        ]

        for s in test_data:
            t = parse_term(thy, ctxt, s)
            t.assert_type_checked()
            self.assertEqual(str(t), s)

    def testGetVars(self):
        thy = basic_thy()
        ctxt = parse_context(
            thy, """context {
                type S;
                type T;
                fixes x : S;
                fixes y : Option<T>
            }"""
        )

        y = parse_term(thy, ctxt, "y")

        t = parse_term(
            thy, ctxt,
            """
            switch (y) {
                case none:
                    0@int;
                case some(x):
                    1@int;
            }
            """
        )
        ty_vars, vars = t.get_vars()
        self.assertEqual(ty_vars, ('T',))
        self.assertEqual(vars, (y,))

    def testGetVars2(self):
        thy = basic_thy()
        ctxt = parse_context(
            thy, """context {
                fixes prio : int32u;
                fixes rtbl : Seq<int32u>
            }"""
        )

        prio = parse_term(thy, ctxt, "prio")
        rtbl = parse_term(thy, ctxt, "rtbl")

        t = parse_term(
            thy, ctxt,
            """
            let x = prio & 7 in
                rtbl[int(prio >> 3)] & (1 << x) == 1 << x
            end
            """
        )
        ty_vars, vars = t.get_vars()
        self.assertEqual(ty_vars, tuple())
        self.assertEqual(vars, (prio, rtbl))

    def testMakeSchematic(self):
        thy = basic_thy()
        ctxt = parse_context(
            thy, """context {
                type S;
                type T;
                fixes x : S;
                fixes xs : Seq<S>
            }"""
        )

        x = parse_term(thy, ctxt, "x")
        xs = parse_term(thy, ctxt, "xs")

        # Test 1
        t = parse_term(thy, ctxt, "x")
        t2 = t.make_schematic(['S'], [x])
        self.assertEqual(repr(t2), "OSVar('?x', ?S)")

        # Test 2
        t = parse_term(thy, ctxt, "x")
        t2 = t.make_schematic(['S'], [])
        self.assertEqual(repr(t2), "OSVar('x', ?S)")

        # Test 3
        t = parse_term(thy, ctxt, "some(x)")
        t2 = t.make_schematic(['S'], [x])
        self.assertEqual(repr(t2), "OSFun('some', OSVar('?x', ?S), Option<?S>)")

    def testSubstVarCapture(self):
        # Test that variable capture is avoided during substitution
        thy = basic_thy()
        ctxt = parse_context(
            thy, "context { type K; type V; fixes m: Map<K, V> }"
        )
        ctxt2 = parse_context(
            thy, "context { type K; type V; fixes k: Map<K, V> }"
        )

        t = parse_term(thy, ctxt, "forall (K k) { !indom(k, m@Map<K, V>) }")
        inst = {"m": parse_term(thy, ctxt2, "k")}

        # Since the substitution of ?m conflicts with bound variable, the
        # bound variable is renamed.
        res_t = parse_term(thy, ctxt2, "forall (K k0) { !indom(k0, k) }")
        self.assertEqual(t.subst(inst), res_t)

    def testSubstVarCaptureSchematic(self):
        # Test that variable capture is avoided during substitution
        thy = basic_thy()
        ctxt = parse_context(
            thy, "context { type K; type V }"
        )
        ctxt2 = parse_context(
            thy, "context { type K; type V; fixes k: Map<K, V> }"
        )

        t = parse_term(thy, ctxt, "forall (K k) { !indom(k, ?m@Map<K, V>) }")
        inst = {"?m": parse_term(thy, ctxt2, "k")}

        # Since the substitution of ?m conflicts with bound variable, the
        # bound variable is renamed.
        res_t = parse_term(thy, ctxt2, "forall (K k0) { !indom(k0, k) }")
        self.assertEqual(t.subst(inst), res_t)

    def testSubstVarNoBoundSubst(self):
        # Test that no substitution is performed on bound variables
        thy = basic_thy()
        ctxt = parse_context(
            thy, "context { fixes b: int32u }"
        )
        ctxt2 = parse_context(
            thy, "context { fixes x: int32u; fixes y: int32u }"
        )

        t = parse_term(thy, ctxt, "forall (int32u a) { a + b > 0 }")
        inst = {"a": parse_term(thy, ctxt2, "x"),
                "b": parse_term(thy, ctxt2, "y")}
        
        # Since a is a bound variable, it is not substituted
        res_t = parse_term(thy, ctxt2, "forall (int32u a) { a + y > 0 }")
        self.assertEqual(t.subst(inst), res_t)

    def testSubstSwitch(self):
        thy = basic_thy()
        struct = """
        struct A {
            int32u field1;
            int32u field2;
        }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))
        ctxt = parse_context(
            thy, "context { fixes a: A; fixes v: int32u }"
        )

        t = parse_term(thy, ctxt,
            """
            switch (a) {
                case A{{field2: 1}}:
                    v + 1;
                case A{{field1: v, field2: 2}}:
                    v + 2;
                default: 0;
            }"""
        )
        expr = parse_term(thy, ctxt, "a.field1")

        t2 = parse_term(thy, ctxt,
            """
            switch (a) {
                case A{{field2: 1}}:
                    a.field1 + 1;
                case A{{field1: v, field2: 2}}:
                    v + 2;
                default: 0;                
            }
            """
        )
        self.assertEqual(t2, t.subst({"v": expr}))

    def testParseTermType(self):
        thy = basic_thy()
        ctxt = parse_context(
            thy, "context { fixes x: int32u }"
        )

        t = parse_term(thy, ctxt, "0 <= x")
        t.assert_type_checked()

    def testStripForall(self):
        thy = basic_thy()

        var_ctxt = parse_context(
            thy, """context {
                fixes x: int
            }"""
        )

        t = parse_term(thy, var_ctxt, "forall (int y) { x < y }")
        vars, body, var_ctxt2 = os_term.strip_forall(var_ctxt, t)
        self.assertEqual([var.name for var in vars], ["y"])
        self.assertEqual(body, parse_term(thy, var_ctxt2, "x < y"))

    def testStripForallNameConflict(self):
        thy = basic_thy()

        var_ctxt = parse_context(
            thy, """context {
                fixes x: int;
                fixes y: int
            }"""
        )
        
        t = parse_term(thy, var_ctxt, "forall (int y) { x < y }")
        vars, body, var_ctxt2 = os_term.strip_forall(var_ctxt, t)
        self.assertEqual([var.name for var in vars], ["y0"])
        self.assertEqual(body, parse_term(thy, var_ctxt2, "x < y0"))

    def testStripForallProvidedName(self):
        thy = basic_thy()

        var_ctxt = parse_context(
            thy, """context {
                fixes x: int
            }"""
        )

        t = parse_term(thy, var_ctxt, "forall (int y) { x < y }")
        vars, body, var_ctxt2 = os_term.strip_forall(var_ctxt, t, var_names=["z"])
        self.assertEqual([var.name for var in vars], ["z"])
        self.assertEqual(body, parse_term(thy, var_ctxt2, "x < z"))

    def testStripForallConj(self):
        thy = basic_thy()

        var_ctxt = parse_context(
            thy, """context {
                fixes x: int;
                fixes z: int
            }"""
        )

        t = parse_term(
            thy, var_ctxt, """
            forall (int a) {
                forall (int y) {
                    x < z && a < y
                }
            }"""
        )
        vars, body, var_ctxt2 = os_term.strip_forall(var_ctxt, t)
        self.assertEqual([var.name for var in vars], ["a", "y"])
        self.assertEqual(body, parse_term(thy, var_ctxt2, "x < z && a < y"))

    def testStripForallMap(self):
        thy = basic_thy()

        var_ctxt = parse_context(
            thy, """context {
                type K;
                type V;
                fixes m: Map<K, V>;
                fixes v: V
            }"""
        )

        t = parse_term(
            thy, var_ctxt, """
            forall (K k) {
                indom(k, m) -> get(k, m) == v
            }"""
        )
        vars, body, var_ctxt2 = os_term.strip_forall(var_ctxt, t, var_names=["k"])
        self.assertEqual([var.name for var in vars], ["k"])
        self.assertEqual(body, parse_term(thy, var_ctxt2, "indom(k, m) -> get(k, m) == v"))

    def testStripForall1(self):
        thy = basic_thy()

        var_ctxt = parse_context(
            thy, """context {
                fixes x: int;
                fixes z: int
            }"""
        )

        t = parse_term(
            thy, var_ctxt, """
            forall (int a, int y) {
                x < z && a < y
            }"""
        )
        var, body, var_ctxt2 = os_term.strip_forall1(var_ctxt, t)
        self.assertEqual(var.name, "a")
        self.assertEqual(body, parse_term(thy, var_ctxt2, "forall (int y) {x < z && a < y}"))

    def testStripImpliesGen(self):
        thy = basic_thy()

        var_ctxt = parse_context(
            thy, """context {
                fixes x: int
            }"""
        )
        
        t = parse_term(
            thy, var_ctxt, """
            x > 1 -> (x > 2 && (x > 3 -> x > 4))
            """
        )
        imps = os_term.strip_implies_gen(t)
        t2 = os_term.list_implies_gen(imps)
        
        expected_t2 = parse_term(
            thy, var_ctxt, """
            (x > 1 -> x > 2) &&
            (x > 1 -> x > 3 -> x > 4)
            """
        )
        self.assertEqual(t2, expected_t2)

    def testListIte(self):
        thy = basic_thy()

        var_ctxt = parse_context(
            thy, """context {
                fixes x: int;
                fixes y: int
            }"""
        )

        t1 = parse_term(thy, var_ctxt, "x")
        t2 = parse_term(thy, var_ctxt, "y")
        cond1 = parse_term(thy, var_ctxt, "x < y")
        cond2 = parse_term(thy, var_ctxt, "x >= y")
        expected_t = parse_term(thy, var_ctxt, "if (x < y) { x } else { y }")
        self.assertEqual(os_term.list_ite([cond1], [t1, t2]), expected_t)
        self.assertEqual(os_term.list_ite([cond1, cond2], [t1, t2]), expected_t)
        

if __name__ == "__main__":
    unittest.main()
