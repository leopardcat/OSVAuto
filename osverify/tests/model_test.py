"""Unit test for model construction"""

import unittest

from osverify import os_theory
from osverify import os_parser
from osverify import os_z3wrapper

def initTheory() -> os_theory.OSTheory:
    return os_parser.load_theory("basic", verbose=False)


class ModelTest(unittest.TestCase):
    def testVar(self):
        thy = initTheory()

        query = """
        query testVar {
            fixes i : int32u;
            fixes j : int32u;
            assumes i == 32 && j == 64
        }
        """
        query = os_parser.parse_query(thy, query)
        model = os_z3wrapper.solve_model(thy, query)
        self.assertEqual(str(model.data["i"]), "32")
        self.assertEqual(str(model.data["j"]), "64")

    def testList(self):
        thy = initTheory()

        query = """
        query testDatatype {
            fixes xs : List<int32u>;
            assumes xs == [1, 2]
        }
        """
        query = os_parser.parse_query(thy, query)
        model = os_z3wrapper.solve_model(thy, query)
        self.assertEqual(str(model.data["xs"]), "[1, 2]")

    def testArray(self):
        thy = initTheory()

        query = """
        query testArray {
            fixes a : int32u[];
            fixes x : int32u;
            fixes y : int32u;
            assumes x == 0 && y == 1;
            assumes a[x] == 1 && a[y] == 3
        }
        """
        query = os_parser.parse_query(thy, query)
        model = os_z3wrapper.solve_model(thy, query)
        self.assertEqual(str(model.data["a"]), "K(3)[0 := 1]")

    def testMap(self):
        thy = initTheory()

        query = """
        query testMap {
            fixes x: int32u;
            fixes y: int32u;
            fixes z: int32u;
            fixes m: Map<int32u, int32u>;
            assumes indom(x, m) && indom(y, m) && indom(z, m);
            assumes get(x, m) == 1 && get(y, m) == 2 && get(z, m) == 3
        }
        """
        query = os_parser.parse_query(thy, query)
        model = os_z3wrapper.solve_model(thy, query)
        self.assertEqual(str(model.data["m"]), "{\n    0: 3,\n    2: 1,\n    1: 2,\n}")

    def testMap2(self):
        thy = initTheory()

        struct = """
        struct Point {
            int32u x;
            int32u y;
        }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))

        query = """
        query testMap2 {
            fixes p: Point;
            fixes q: Point;
            fixes m: Map<Point, int32u>;
            assumes p == Point {{x: 0, y: 1}};
            assumes q == Point {{x: 2, y: 3}};
            assumes indom(p, m) && get(p, m) == 0;
            assumes indom(q, m) && get(q, m) == 1
        }
        """
        query = os_parser.parse_query(thy, query)
        model = os_z3wrapper.solve_model(thy, query)
        self.assertEqual(
            str(model.data["m"]),
            "{\n    Point{{x: 2, y: 3}}: 1,\n    Point{{x: 0, y: 1}}: 0,\n}")

    def testStruct(self):
        thy = initTheory()

        struct = """
        struct Point {
            int32u x;
            int32u y;
        }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))

        query = """
        query testStruct {
            fixes p: Point;
            fixes q: Point;
            assumes p.x == 2 && p.y == 3 && q.x == 4 && q.y == 5
        }
        """
        query = os_parser.parse_query(thy, query)
        model = os_z3wrapper.solve_model(thy, query)
        self.assertEqual(str(model.data['p']), "Point{{x: 2, y: 3}}")
        self.assertEqual(str(model.data['q']), "Point{{x: 4, y: 5}}")

    def testDatatype(self):
        thy = initTheory()

        datatype = """
        datatype Point =
            PointA(int32u x, int32u y) | PointB (int32u x, int32u z)
        """
        thy.add_datatype(os_parser.parse_datatype(thy, datatype))

        query = """
        query testDatatype {
            fixes v: Point;
            fixes w: Point;
            assumes v == PointA(2, 3) && w == PointB(4, 5)
        }
        """
        query = os_parser.parse_query(thy, query)
        model = os_z3wrapper.solve_model(thy, query)
        self.assertEqual(str(model.data['v']), "PointA(2, 3)")
        self.assertEqual(str(model.data['w']), "PointB(4, 5)")


if __name__ == "__main__":
    unittest.main()
