"""Unit test for theory."""

import unittest

from osverify import os_theory
from osverify import os_parser
from osverify import os_struct


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
        self.assertEqual(thy.axiom_func.keys(), {"range", "indom", "get", "emptyMap", "updateMap"})

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

    def testGetTheorem(self):
        thy = basic_thy
        ctxt = os_theory.OSContext(thy)

        inlist_simps1 = os_parser.parse_term(
            thy, ctxt,
            """
            forall (int32u x) {
              inlist(x, []) == false
            }
            """
        )
        inlist_simps2 = os_parser.parse_term(
            thy, ctxt,
            """
            forall (int32u x, int32u y, List<int32u> xs2) {
              inlist(x, cons(y, xs2)) == if (x == y) {
                true
              } else {
                inlist(x, xs2)
              }
            }
            """
        )
        self.assertEqual(thy.get_forall_theorem("inlist_simps1", [os_struct.Int32U]), inlist_simps1)
        self.assertEqual(thy.get_forall_theorem("inlist_simps2", [os_struct.Int32U]), inlist_simps2)

        rev_simps1 = os_parser.parse_term(
            thy, ctxt, "rev(nil::List<int32u>) == nil"
        )
        self.assertEqual(thy.get_forall_theorem("rev_simps1", [os_struct.Int32U]), rev_simps1)

    def testGetFuncType(self):
        thy = basic_thy
        ctxt = os_parser.parse_context(thy, "context { type E; type T; type K; type V }")

        data = [
            ("List.id", ["E"], "List<E> -> int"),
            ("nil", ["E"], "List<E>"),
            ("cons", ["E"], "E -> List<E> -> List<E>"),
            ("inlist", ["T"], "T -> List<T> -> bool"),
            ("indom", ["K", "V"], "K -> Map<K, V> -> bool"),
            ("get", ["K", "V"], "K -> Map<K, V> -> V"),
        ]

        for func_name, expected_params, ty_str in data:
            func_ty, ty_params = thy.get_func_type(func_name)
            expected_ty = os_parser.parse_type(thy, ctxt, ty_str)
            self.assertEqual(func_ty, expected_ty, "%s != %s" % (func_ty, expected_ty))
            self.assertEqual(ty_params, tuple(expected_params))


if __name__ == "__main__":
    unittest.main()
