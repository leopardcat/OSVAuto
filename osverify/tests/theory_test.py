"""Unit test for theory."""

import unittest

from osverify import os_theory
from osverify import os_parser


basic_thy = os_parser.load_theory("basic", verbose=False)

class OSTheoryTest(unittest.TestCase):
    def testBasicTheoryTypes(self):
        thy = basic_thy

        # Datatypes in basic
        self.assertEqual(thy.datatypes.keys(), {"Prod", "nat", "List", "Option"})

        # Axiomatic types in basic
        self.assertEqual(thy.axiom_types.keys(), {"Map"})

    def testBasicTheoryMap(self):
        thy = basic_thy

        # Axiomatic functions for Map
        self.assertEqual(thy.axiom_func.keys(), {"indom", "get", "emptyMap", "updateMap"})

        # Various definitions are in theorems, but not in rewrite
        for th_name in ('join_def', 'remove_def', 'mapEq_def', 'merge_def', 'minus_def'):
            self.assertIn(th_name, thy.theorems)
            self.assertNotIn(th_name, thy.attribute_map['rewrite'])

    def testTheoremLength(self):
        thy = basic_thy
        ctxt = os_theory.OSContext(thy)

        length_def = os_parser.parse_term(
            thy, ctxt,
            """
            length(?xs::List<?T>) == (switch (?xs::List<?T>) {
                case nil:
                    0;
                case cons(i, xs2):
                    succ(length(xs2));
            })
            """
        )
        self.assertEqual(thy.get_sch_theorem('length_def'), length_def)
        self.assertNotIn('length_def', thy.attribute_map['rewrite'])

        length_simps1 = os_parser.parse_term(
            thy, ctxt,
            "length(nil::List<?T>) == 0"
        )
        self.assertEqual(thy.get_sch_theorem('length_simps1'), length_simps1)
        self.assertIn('length_simps1', thy.attribute_map['rewrite'])

        length_simps2 = os_parser.parse_term(
            thy, ctxt,
            "length(cons(?i::?T, ?xs2)) == succ(length(?xs2::List<?T>))"
        )
        self.assertEqual(thy.get_sch_theorem('length_simps2'), length_simps2)
        self.assertIn('length_simps2', thy.attribute_map['rewrite'])

    def testTheoremAppend(self):
        thy = basic_thy
        ctxt = os_theory.OSContext(thy)

        append_def = os_parser.parse_term(
            thy, ctxt,
            """
            append(?xs::List<?T>, ?ys) == (switch (?xs::List<?T>) {
                case nil:
                    ?ys;
                case cons(i, xs2):
                    cons(i, append(xs2, ?ys));
                })
            """
        )
        self.assertEqual(thy.get_sch_theorem('append_def'), append_def)
        self.assertNotIn('append_def', thy.attribute_map['rewrite'])

        append_simps1 = os_parser.parse_term(
            thy, ctxt,
            "append(nil, ?ys::List<?T>) == ?ys"
        )
        self.assertEqual(thy.get_sch_theorem('append_simps1'), append_simps1)
        self.assertIn('append_simps1', thy.attribute_map['rewrite'])

        append_simps2 = os_parser.parse_term(
            thy, ctxt,
            "append(cons(?i::?T, ?xs2), ?ys) == cons(?i::?T, append(?xs2, ?ys))"
        )
        self.assertEqual(thy.get_sch_theorem('append_simps2'), append_simps2)
        self.assertIn('append_simps2', thy.attribute_map['rewrite'])


if __name__ == "__main__":
    unittest.main()
