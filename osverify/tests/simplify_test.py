"""Unit test for simplify."""

import unittest

from osverify import os_parser
from osverify import os_simplify


basic_thy = os_parser.load_theory("basic", verbose=False)

class OSSimplifyTest(unittest.TestCase):
    def testRewrite(self):
        thy = basic_thy
        ctxt = os_parser.parse_context(
            thy, "context { type T; fixes i : T; fixes xs : List<T>; fixes ys : List<T>; fixes zs : List<T> }"
        )

        t = os_parser.parse_term(thy, ctxt, "append(cons(i, append(xs, ys)), zs)")
        t2 = os_parser.parse_term(thy, ctxt, "cons(i, append(append(xs, ys), zs))")
        eq_th = thy.get_sch_theorem('append_simps2')
        self.assertEqual(os_simplify.rewrite(thy, eq_th, t), t2)
        
    def testSimplify(self):
        thy = basic_thy
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
        thy = basic_thy

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


if __name__ == "__main__":
    unittest.main()
