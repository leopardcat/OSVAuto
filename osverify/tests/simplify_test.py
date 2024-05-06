"""Unit test for simplify."""

import unittest

from osverify import os_parser
from osverify import os_simplify
from osverify import os_theory

def basic_thy():
    return os_parser.load_theory("basic", verbose=False)

class OSSimplifyTest(unittest.TestCase):
    def testRewrite(self):
        thy = basic_thy()
        ctxt = os_parser.parse_context(
            thy, "context { type T; fixes i : T; fixes xs : List<T>; fixes ys : List<T>; fixes zs : List<T> }"
        )

        t = os_parser.parse_term(thy, ctxt, "append(cons(i, append(xs, ys)), zs)")
        t2 = os_parser.parse_term(thy, ctxt, "cons(i, append(append(xs, ys), zs))")
        eq_th = thy.get_sch_theorem('append_simps2')
        self.assertEqual(os_simplify.rewrite(thy, eq_th, t), t2)
        
    def testSimplify(self):
        thy = basic_thy()
        ctxt = os_parser.parse_context(
            thy, "context { type T; fixes x : T; fixes xs : List<T>; fixes ys : List<T>; fixes zs : List<T> }"
        )

        # Each test case is in the form (t1, t2), where t1 should be simplified
        # into t2.
        test_data = [
            ("append(nil, ys)",
             "ys"),

            ("append(append(cons(x, xs), ys), zs)",
             "cons(x, append(append(xs, ys), zs))"),

            ("append(cons(x, nil), ys)",
             "cons(x, ys)"),

            ("append(cons(x, nil), ys) == cons(x, ys)",
             "cons(x, ys) == cons(x, ys)"),

            ("rev(cons(x, nil))",
             "cons(x, nil)"),

            # No simplification should be performed
            ("append(xs, ys)",
             "append(xs, ys)")
        ]

        for s, s2 in test_data:
            t = os_parser.parse_term(thy, ctxt, s)
            t2 = os_parser.parse_term(thy, ctxt, s2)
            self.assertEqual(os_simplify.simplify(thy, t), t2)

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

        ctxt = """
        context {
            fixes xs: List<int32u>;
            fixes ys: List<int32u>;
            fixes m: int32u;
            fixes a: A;
            fixes b: B
        }
        """
        ctxt = os_parser.parse_context(thy, ctxt)

        # Each test case is in the form (t1, t2), where t1 should be simplified
        # into t2 in one step of simplify_switch.
        test_data = [
            # reduction for wildcard, variable, and default
            ("switch (xs) { case _: true; default: false; }",
             "true"),

            ("switch (xs) { case v: append(v, ys); default: ys; }",
             "append(xs, ys)"),

            ("switch (xs) { default: false; case _: true; }",
             "false"),

            # reduction for constant
            ("switch (m) { case 1: xs; default: ys; }",
             "if (m == 1) { xs } else { switch (m) { default: ys; } }"),

            # reduction for structure literal: reduction in 3 steps
            ("switch (a) { case A{{x: v, y: w}}: v + w; default: 0; }",
             "switch (a.x) { case v: switch (a) { case A{{y: w}}: v + w; default: 0; }; default: 0; }"),

            ("switch (a) { case A{{y: w}}: 1 + w; default: 0; }",
             "switch (a.y) { case w: switch (a) { case A{{}}: 1 + w; default: 0; }; default: 0; }"),

            ("switch (a) { case A{{}}: true; default: false; }",
             "true"),

            # reduction for datatype: inner patterns
            ("switch (b) {                                      \
                case f(A{{x: v, y: w}}): v + w;                 \
                default: 0;                                     \
              }",
             "switch (b) {                                      \
                case f(u):                                      \
                    switch (u) {                                \
                        case A{{x: v, y: w}}: v + w;            \
                        default: switch (b) { default: 0; };    \
                    };                                          \
                default: switch (b) { default: 0; };            \
             }"),

            # reduction for datatype: inner patterns #2
            ("switch (b) {                                     \
                case h(A{{x: v, y: w}}, z): v + w + z;         \
                default: 0;                                    \
              }",
             "switch (b) {                                     \
                case h(u, z):                                  \
                    switch (u) {                               \
                        case A{{x: v, y: w}}: v + w + z;       \
                        default: switch (b) { default: 0; };   \
                    };                                         \
                default: switch (b) { default: 0; };           \
              }"),
        ]

        for s, s2 in test_data:
            t = os_parser.parse_term(thy, ctxt, s)
            t2 = os_parser.parse_term(thy, ctxt, s2)
            self.assertEqual(os_simplify.simplify_switch_once(thy, t), t2)

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

        ctxt = """
        context {
            fixes b: B
        }
        """
        ctxt = os_parser.parse_context(thy, ctxt)

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
        t = os_parser.parse_term(thy, ctxt, t)
        t2 = os_simplify.simplify_switch(thy, t)
        self.assertTrue(os_theory.is_standard_switch(thy, t2))

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

        ctxt = """
        context {
            fixes b: B
        }
        """
        ctxt = os_parser.parse_context(thy, ctxt)

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
        t = os_parser.parse_term(thy, ctxt, t)
        t2 = os_simplify.simplify_switch(thy, t)
        self.assertTrue(os_theory.is_standard_switch(thy, t2))

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

        ctxt = """
        context {
            fixes s: status
        }
        """
        ctxt = os_parser.parse_context(thy, ctxt)

        t = """
        switch (s) {
            case rdy: true;
            case wait(os_time): true;
            default: false;
        }
        """
        t = os_parser.parse_term(thy, ctxt, t)
        t2 = os_simplify.simplify_switch(thy, t)
        self.assertTrue(os_theory.is_standard_switch(thy, t2))


if __name__ == "__main__":
    unittest.main()
