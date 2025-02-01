"""Unit test for simplify."""

import unittest

from osverify import os_parser
from osverify import os_simplify
from osverify import os_tactics
from osverify import auto_tactics


def basic_thy():
    return os_parser.load_theory("basic", verbose=False)

class OSSimplifyTest(unittest.TestCase):
    def testSimplifySwitch(self):
        thy = basic_thy()

        # Add some simple structures and datatypes
        struct = """
        struct A { int32u x; int32u y; }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))

        datatype = """
        datatype B = f(A u) | g(int32u v) | h(A u, int32u v)
        """
        thy.add_datatype(os_parser.parse_datatype(thy, datatype))

        var_ctxt = os_parser.parse_context(
            thy, """context {
                fixes x: Option<int32u>;
                fixes y: Option<int32u>;
                fixes m: int32u;
                fixes a: A;
                fixes b: B
            }
            """
        )

        # Each test case is in the form (t1, t2), where t1 should be
        # simplified version of t2
        test_data = [
            # reduction for wildcard, variable, and default
            ("switch (x) { case _: true; default: false; }",
             "true"),

            ("switch (x) { default: false; case _: true; }",
             "false"),

            # reduction for constant
            ("switch (m) { case 1: x; default: y; }",
             "if (m == 1) { x } else { y }"),

            # reduction for structure literal: reduction in 3 steps
            ("switch (a) { case A{{x: v, y: w}}: v + w; }",
             "a.x + a.y"),

            ("switch (a) { case A{{y: w}}: 1 + w; }",
             "1 + a.y"),

            ("switch (a) { case A{{}}: true; default: false; }",
             "true"),

            # reduction for datatype: inner patterns
            ("switch (b) {                                      \
                case f(A{{x: v, y: w}}): v + w;                 \
                default: 0;                                     \
              }",
             "if (b.id == 0) {                                  \
                b.u.x + b.u.y                                   \
              } else {                                          \
                0                                               \
              }"),

            # reduction for datatype: inner patterns #2
            ("switch (b) {                                     \
                case h(A{{x: v, y: w}}, z): v + w + z;         \
                default: 0;                                    \
              }",
             "if (b.id == 2) {                                  \
                b.u.x + b.u.y + b.v                             \
              } else {                                          \
                0                                               \
              }"),
        ]

        for s, s2 in test_data:
            t = os_parser.parse_term(thy, var_ctxt, s)
            t2 = os_parser.parse_term(thy, var_ctxt, s2)
            self.assertEqual(os_simplify.normalize_switch(thy, t), t2)

    def testSimplifySwitch2(self):
        thy = basic_thy()

        datatype = """
        datatype A = f(int32u x) | g(int32u x) | h(int32u x)
        """
        thy.add_datatype(os_parser.parse_datatype(thy, datatype))

        struct = """
        struct B { A a; }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))

        var_ctxt = os_parser.parse_context(
            thy, """context {
                fixes b: B
            }"""
        )

        t = """
        switch (b) {
            case B{{a: a}}:
                switch (a) {
                    case f(x): x > 0;
                    case g(x): x > 1;
                    default: true;
                };
        }
        """
        t = os_parser.parse_term(thy, var_ctxt, t)
        t2 = t.transform(var_ctxt, os_simplify.SimplifySwitch(thy))

        expected_t2 = """
        if (b.a.id == 0) {
            b.a.x > 0
        } else {
            if (b.a.id == 1) {
                b.a.x > 1
            } else {
                true
            }
        }
        """
        self.assertEqual(t2, os_parser.parse_term(thy, var_ctxt, expected_t2))

    def testSimplifySwitch3(self):
        # In this example, we intentionally repeat the name "a" to test
        # handling of name conflicts.
        thy = basic_thy()

        datatype = """
        datatype A = f(int32u x) | g(int32u x) | h(int32u x)
        """
        thy.add_datatype(os_parser.parse_datatype(thy, datatype))

        datatype = """
        datatype A2 = m(A a, int32u t)
        """
        thy.add_datatype(os_parser.parse_datatype(thy, datatype))

        struct = """
        struct B { A2 a; }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))

        var_ctxt = os_parser.parse_context(
            thy, """context {
                fixes b: B
            }"""
        )

        t = """
        switch (b) {
            case B{{a: a}}:
                switch (a) {
                    case m(f(x), _): x > 0;
                    case m(g(x), _): x > 1;
                    default: true;
                };
        }
        """
        t = os_parser.parse_term(thy, var_ctxt, t)
        t2 = t.transform(var_ctxt, os_simplify.SimplifySwitch(thy))

        expected_t2 = """
        if (b.a.id == 0 && b.a.a.id == 0) {
            b.a.a.x > 0
        } else {
            if (b.a.id == 0 && b.a.a.id == 1) {
                b.a.a.x > 1
            } else {
                true
            }
        }
        """
        self.assertEqual(t2, os_parser.parse_term(thy, var_ctxt, expected_t2))

    def testSimplifySwitch4(self):
        thy = basic_thy()

        datatype = """
        datatype stat = os_sem(int32u id) | os_time
        """
        thy.add_datatype(os_parser.parse_datatype(thy, datatype))

        datatype = """
        datatype status = rdy | wait(stat st)
        """
        thy.add_datatype(os_parser.parse_datatype(thy, datatype))

        var_ctxt = os_parser.parse_context(
            thy, """context {
                fixes s: status
            }"""
        )

        t = """
        switch (s) {
            case rdy: true;
            case wait(os_time): true;
            default: false;
        }
        """
        t = os_parser.parse_term(thy, var_ctxt, t)
        t2 = t.transform(var_ctxt, os_simplify.SimplifySwitch(thy))

        expected_t2 = """
        if (s.id == 0) {
            true
        } else {
            if (s.id == 1 && s.st.id == 1) {
                true
            } else {
                false
            }
        }
        """
        self.assertEqual(t2, os_parser.parse_term(thy, var_ctxt, expected_t2))

    def testSimplifySwitch5(self):
        thy = basic_thy()

        struct = """
        struct A {
            int32u field1;
            int32u field2;
        }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))

        var_ctxt = """
        context {
            fixes a: A
        }
        """
        var_ctxt = os_parser.parse_context(thy, var_ctxt)

        t = """
        switch (a) {
            case A{{field1: v, field2: 1}}:
                v + 1;
            case A{{field1: v, field2: 2}}:
                v + 2;
            default:
                0;
        }
        """
        t = os_parser.parse_term(thy, var_ctxt, t)
        t2 = t.transform(var_ctxt, os_simplify.SimplifySwitch(thy))

        exp_t2 = """
        if (a.field2 == 1) {
            a.field1 + 1
        } else {
            if (a.field2 == 2) {
                a.field1 + 2
            } else {
                0
            }
        }
        """
        self.assertEqual(t2, os_parser.parse_term(thy, var_ctxt, exp_t2))

    def testSimplifySwitch6(self):
        thy = basic_thy()

        datatype = """
        datatype stat =
            os_stat_sem(int32u id) |
            os_stat_q(int32u id)
        """
        thy.add_datatype(os_parser.parse_datatype(thy, datatype))

        datatype = """
        datatype status =
            rdy |
            wait(stat st, int32u dly)
        """
        thy.add_datatype(os_parser.parse_datatype(thy, datatype))

        var_ctxt = """
        context {
            fixes s: status
        }
        """
        var_ctxt = os_parser.parse_context(thy, var_ctxt)

        t = """
        switch (s) {
            case wait(os_stat_sem(_), dly):
                dly == 1;
            case wait(os_stat_q(_), dly):
                dly == 2;
            default:
                false;
        }
        """
        t = os_parser.parse_term(thy, var_ctxt, t)
        t2 = t.transform(var_ctxt, os_simplify.SimplifySwitch(thy))

        expected_t2 = """
        if (s.id == 1 && s.st.id == 0) {
            s.dly == 1
        } else {
            if (s.id == 1 && s.st.id == 1) {
                s.dly == 2
            } else {
                false
            }
        }
        """
        self.assertEqual(t2, os_parser.parse_term(thy, var_ctxt, expected_t2))

    def testSimplifySwitchNameConflict(self):
        thy = basic_thy()

        struct = """
        struct A {
            int32u field1;
            int32u field2;
        }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))

        var_ctxt = """
        context {
            fixes a: A;
            fixes x: int32u
        }
        """
        var_ctxt = os_parser.parse_context(thy, var_ctxt)

        t = """
        switch (a) {
            case A{{field1: x, field2: y}}:
                x + y;
        }
        """
        t = os_parser.parse_term(thy, var_ctxt, t)
        t2 = t.transform(var_ctxt, os_simplify.SimplifySwitch(thy))

        exp_t2 = """
        a.field1 + a.field2
        """
        self.assertEqual(t2, os_parser.parse_term(thy, var_ctxt, exp_t2))

    def testProcessUpdateGen(self):
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
        var_ctxt = os_parser.parse_context(
            thy, """context {
                fixes a: A;
                fixes b: B
            }"""
        )

        test_data = [
            ("a{|x := 3|}",
             "a{x := 3}"),
            ("a{|ys[0] := 3|}",
             "a{ys := seq_update(0, 3, a.ys)}"),
            ("b{|as[0].x := 3|}",
             "b{as := seq_update(0, [[ b.as[0] ]]{x := 3}, b.as)}"),
            ("b{|as[0].ys[1] := 3|}",
             "b{as := seq_update(0, [[ b.as[0] ]]{ys := seq_update(1, 3, b.as[0].ys)}, b.as)}"),
        ]

        for s1, s2 in test_data:
            t1 = os_parser.parse_term(thy, var_ctxt, s1)
            t2 = os_simplify.expand_process_update_gen(thy, t1)
            self.assertEqual(t2, os_parser.parse_term(thy, var_ctxt, s2))

    def testReplaceTerm(self):
        thy = basic_thy()
        ctxt = """
        context {
            fixes x: int32u;
            fixes y: int32u;
            fixes z: int32u
        }
        """
        ctxt = os_parser.parse_context(thy, ctxt)
        t = os_parser.parse_term(thy, ctxt, "forall (int32u z in range(0, 10)) { x + z < y }")

        eq = os_parser.parse_term(thy, ctxt, "x + z == y")
        t2 = t.transform(ctxt, os_simplify.Rewrite(eq))

        # x + z is not replaced since z is a bound variable. However, the
        # bound variable is renamed to avoid conflicts.
        expected_t2 = os_parser.parse_term(
            thy, ctxt, "forall (int32u z0 in range(0, 10)) { x + z0 < y }")
        self.assertEqual(t2, expected_t2)

    def testSimplifyDefineEqs(self):
        thy = basic_thy()
        ctxt = """context {
            fixes a: Map<int32u, int32u>;
            fixes b: Map<int32u, int32u>;
            fixes c: Map<int32u, int32u>
        }
        """
        ctxt = os_parser.parse_context(thy, ctxt)

        define_eqs = [
            "b == updateMap(3, 5, a)",
            "c == updateMap(4, 6, b)"
        ]
        define_eqs = [os_parser.parse_term(thy, ctxt, t) for t in define_eqs]

        t = "get(2, c) == 3"
        t = os_parser.parse_term(thy, ctxt, t)

        res_t = "get(2, updateMap(4, 6, updateMap(3, 5, a))) == 3"
        res_t = os_parser.parse_term(thy, ctxt, res_t)

        self.assertEqual(os_simplify.simplify_define_eqs(ctxt, define_eqs, t), res_t)

    def testNormalize(self):
        thy = basic_thy()

        datatype = """
        datatype A = f(int32u x) | g(int32u x) | h(int32u x)
        """
        thy.add_datatype(os_parser.parse_datatype(thy, datatype))

        ctxt = os_parser.parse_context(
            thy, """context {
                fixes a: A
            }
            """
        )

        t = os_parser.parse_term(thy, ctxt, "a != f(3)")
        t2 = t.transform(ctxt, os_simplify.Normalize(thy))

        expected_t2 = os_parser.parse_term(thy, ctxt, "!(0 == a.id && a.x == 3)")
        self.assertEqual(t2, expected_t2)

    def testSimplifyQuant(self):
        thy = basic_thy()
        ctxt = os_parser.parse_context(
            thy, """context {
                fixes j: int32u
            }"""
        )
        t = os_parser.parse_term(thy, ctxt, """
            forall (int32u i in range(0, 32)) {
                i > j
            }
            """
        )
        t2 = os_simplify.normalize(thy, t)
        expected_t2 = os_parser.parse_term(thy, ctxt, """
            forall (int32u i) {
                i >= 0 && i < 32 -> i > j
            }"""
        )
        self.assertEqual(t2, expected_t2)

    def testDistributeQuant1(self):
        thy = basic_thy()
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes x: int;
                assumes x == 1 -> exists (int x) {x == 2};
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
                assumes exists (int x0) {x == 1 -> x0 == 2};
                shows true
            }"""
        )
        self.assertEqual(res_state, state2)

    def testDistributeQuant2(self):
        thy = basic_thy()
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes x: int;
                assumes x == 1 -> exists (int x) {
                            x == 2 -> exists (int x) {
                                x == 3
                            }
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
                assumes exists (int x0) {
                            exists (int x1) {
                                x == 1 -> x0 == 2 -> x1 == 3
                            }
                        };
                shows true
            }"""
        )
        self.assertEqual(res_state, state2)

    def testDistributeQuant3(self):
        thy = basic_thy()
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes x: int;
                assumes !(exists (int x0) {x0 == x + 1});
                assumes !(forall (int x0) {x0 != x + 1});
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
                            x0 != x + 1
                        };
                assumes exists (int x0) {
                            x0 == x + 1
                        };
                shows true
            }"""
        )
        self.assertEqual(res_state, state2)

    def testDistributeQuant4(self):
        thy = basic_thy()
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes x: int;
                assumes forall (int x) {
                            x == 1
                        } ||
                        x == 2;
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
                    x0 == 1 ||
                    x == 2
                };
                shows true
            }"""
        )
        self.assertEqual(res_state, state2)

    def testDistributeQuant5(self):
        thy = basic_thy()
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes x: int;
                assumes forall (int x) {
                            x == 1
                        } &&
                        exists (int x0) {
                            x0 == 1
                        } || forall (int x1) {
                            x1 == x
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
                assumes forall (int x1) {
                            forall (int x0) {
                                x0 == 1
                            } && exists (int x0) {
                                x0 == 1
                            } || x1 == x
                        };
                shows true
            }"""
        )
        self.assertEqual(res_state, state2)

    def testDistributeQuant6(self):
        thy = basic_thy()
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes x: int;
                assumes if (x == 1) {
                            forall (int x) {
                                x > 0
                            }
                        } else {
                            forall (int x) {
                                x < 0
                            }
                        };
                shows true
            }""")
        res_state = auto_tactics.ApplyAll([
            auto_tactics.SplitConjAuto(),
            os_tactics.ApplyTransformerThy(os_simplify.Normalize)
        ]).exec(thy, state)

        state2 = os_parser.parse_proof_state(
            thy, """state {
                fixes x: int;
                assumes forall (int x0) {
                            x == 1 -> x0 > 0
                        };
                assumes forall (int x0) {
                            x != 1 -> x0 < 0
                        };
                shows true
            }""")
        self.assertEqual(res_state, state2)

    def testDistributeQuant7(self):
        thy = basic_thy()
        state = os_parser.parse_proof_state(
            thy, """state {
                fixes x: int;
                assumes if (x == 1) {
                            forall (int x) {
                                x == 1
                            }
                        } else {
                            exists (int x) {
                                x != 1
                            }
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
                            x == 1 -> x0 == 1
                        };
                assumes exists (int x0) {
                            x != 1 -> x0 != 1
                        };
                shows true
            }"""
        )
        self.assertEqual(res_state, state2)

    def testExtractConstFact(self):
        thy = basic_thy()
        ctxt = os_parser.parse_context(
            thy, """context {
                fixes x: int
            }
            """
        )

        t = os_parser.parse_term(
            thy, ctxt, """forall (int y) {
                x > 1 && x > y
            }
            """
        )

        t2 = os_simplify.extract_const_fact(ctxt, t)
        expected_t2 = os_parser.parse_term(thy, ctxt, "x > 1")
        self.assertEqual(t2, expected_t2)

    def testExtractConstFact2(self):
        thy = basic_thy()
        ctxt = os_parser.parse_context(
            thy, """context {
                fixes x: int
            }
            """
        )

        t = os_parser.parse_term(
            thy, ctxt, """forall (int y) {
                (x > 1 -> x > 2 && x > y) &&
                (x > y -> x > 3)
            }
            """
        )

        t2 = os_simplify.extract_const_fact(ctxt, t)
        expected_t2 = os_parser.parse_term(thy, ctxt, "x > 1 -> x > 2")
        self.assertEqual(t2, expected_t2)

    def testExtractConstFact3(self):
        thy = basic_thy()
        ctxt = os_parser.parse_context(
            thy, """context {
                fixes x: int
            }
            """
        )

        t = os_parser.parse_term(
            thy, ctxt, """forall (int y) {
                (x > y -> x > 3)
            }
            """
        )

        t2 = os_simplify.extract_const_fact(ctxt, t)
        expected_t2 = os_parser.parse_term(thy, ctxt, "true")
        self.assertEqual(t2, expected_t2)


if __name__ == "__main__":
    unittest.main()
