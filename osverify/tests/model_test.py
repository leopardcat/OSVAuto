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


if __name__ == "__main__":
    unittest.main()
