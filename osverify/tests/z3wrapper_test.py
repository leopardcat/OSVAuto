"""Unit test for Z3 conversion"""

import unittest

from osverify import os_theory
from osverify import os_parser
from osverify import os_z3wrapper
from osverify import os_tactics

def initTheory() -> os_theory.OSTheory:
    return os_parser.load_theory("basic", verbose=False)


class Z3WrapperTest(unittest.TestCase):
    def testStructEqual(self):
        thy = initTheory()

        struct = """
        struct A { int32u x; int32u y; }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))

        query = os_parser.parse_query(thy, """
        query testStructEqual {
            fixes a: struct A;
            shows a == A {{ x: a.x, y: a.y }}
        }
        """)
        self.assertTrue(os_z3wrapper.solve_query(thy, query))

    def testStructVal(self):
        thy = initTheory()

        struct = """
        struct A { int32u x; int32u y; }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))

        query = """
        query testStructVal {
            fixes a: struct A;
            assumes a == A {{ x: 1, y: 2}};
            shows a.x == 1
        }
        """
        query = os_parser.parse_query(thy, query)
        self.assertTrue(os_z3wrapper.solve_query(thy, query))

    def testStructUpdate(self):
        thy = initTheory()

        struct = """
        struct A { int32u x; int32u y; }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))

        query = """
        query testStructUpdate {
            fixes a: struct A;
            fixes b: struct A;
            assumes b == a{ x := 1 };
            shows b.x == 1 && b.y == a.y
        }
        """
        query = os_parser.parse_query(thy, query)
        self.assertTrue(os_z3wrapper.solve_query(thy, query))

    def testStructUpdate2(self):
        thy = initTheory()

        datatype = """
        datatype A = f(int32u x) | g(int32u y)
        """
        thy.add_datatype(os_parser.parse_datatype(thy, datatype))

        struct = """
        struct B { A u; A v; }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))

        query = """
        query testStructUpdate {
            fixes a: B;
            fixes b: B;
            assumes b == a{ u := f(1) };
            shows b.u.x == 1
        }
        """
        query = os_parser.parse_query(thy, query)
        self.assertTrue(os_z3wrapper.solve_query(thy, query))

    def testDatatypeEqual(self):
        thy = initTheory()

        datatype = """
        datatype A = f(int32u x) | g(int32u y)
        """
        thy.add_datatype(os_parser.parse_datatype(thy, datatype))

        query = """
        query testDatatypeEqual {
            fixes a: A;
            fixes b: A;
            assumes switch (a) {
                case f(u):
                    switch (b) {
                        case f(v): u == v;
                        default: false;
                    };
                default: false;
            };
            shows a == b
        }
        """
        query = os_parser.parse_query(thy, query)
        self.assertTrue(os_z3wrapper.solve_query(thy, query))

    def testDatatypeEqual2(self):
        thy = initTheory()

        datatype = """
        datatype A = f(int32u x) | g(int32u y)
        """
        thy.add_datatype(os_parser.parse_datatype(thy, datatype))

        # TODO: remove the default case for a
        query = """
        query testDatatypeEqual2 {
            fixes a: A;
            fixes b: A;
            assumes a == b;
            shows switch (a) {
                case f(u):
                    switch (b) {
                        case f(v): u == v;
                        default: false;
                    };
                case g(u):
                     switch (b) {
                        case g(v): u == v;
                        default: false;
                     };
                default: false;
            }
        }
        """
        query = os_parser.parse_query(thy, query)
        self.assertTrue(os_z3wrapper.solve_query(thy, query))

    def testDatatypeEqual3(self):
        thy = initTheory()

        datatype = """
        datatype A = f(int32u x) | g(int32u y)
        """
        thy.add_datatype(os_parser.parse_datatype(thy, datatype))

        query = """
        query testDatatypeEqual3 {
            fixes a: A;
            assumes a == f(1);
            shows a.x == 1
        }
        """
        query = os_parser.parse_query(thy, query)
        self.assertTrue(os_z3wrapper.solve_query(thy, query))

    def testDatatypeEqual4(self):
        thy = initTheory()

        query = """
        query testDatatypeEqual4 {
            fixes xs: List<int32u>;
            assumes xs == cons(1, cons(2, nil));
            shows xs.ele == 1 && xs.rest.ele == 2 && xs.rest.rest == nil
        }
        """
        query = os_parser.parse_query(thy, query)
        self.assertTrue(os_z3wrapper.solve_query(thy, query))

    def testDatatypeEqual5(self):
        thy = initTheory()

        query = """
        query testDatatypeEqual4 {
            fixes xs: List<int32u>;
            fixes ys: List<int32u>;
            fixes zs: List<int32u>;
            assumes xs == cons(1, ys);
            assumes ys == cons(2, zs);
            shows xs.ele == 1 && xs.rest.ele == 2 && xs.rest.rest == zs
        }
        """
        query = os_parser.parse_query(thy, query)
        self.assertTrue(os_z3wrapper.solve_query(thy, query))
        
    def testDatatypeEqual6(self):
        thy = initTheory()

        datatype = """
        datatype A = f(int32u x) | g(int32u y)
        """
        thy.add_datatype(os_parser.parse_datatype(thy, datatype))

        query = """
        query testDatatypeEqual6 {
            fixes a: A;
            fixes b: A;
            fixes h: A -> A;
            assumes switch (a) {
                case f(u):
                    switch (b) {
                        case f(v): u == v;
                        default: false;
                    };
                default: false;
            };
            shows h(a) == h(b)
            proof {
                assert (H: a == b) { auto };;
                auto
            }
        }
        """
        query = os_parser.parse_query(thy, query)
        os_tactics.check_proof(thy, query)

    def testDatatypeEqual7(self):
        thy = initTheory()

        datatype = """
        datatype A = f(int32u x) | g(int32u y)
        """
        thy.add_datatype(os_parser.parse_datatype(thy, datatype))

        query = """
        query testDatatypeEqual7 {
            fixes a: A;
            shows switch (a) {
                case f(u): a == f(a.x);
                case g(v): a == g(a.y);
                default: false;
            }
        }
        """
        query = os_parser.parse_query(thy, query)
        self.assertTrue(os_z3wrapper.solve_query(thy, query))


if __name__ == "__main__":
    unittest.main()
