"""Unit test for parsing"""

import sys
sys.path.append("../../")

import unittest

from osverify import os_parser
from osverify import os_theory
from osverify import os_tactics
from osverify import os_z3wrapper

def initTheory() -> os_theory.OSTheory:
    return os_parser.load_theory("basic", verbose=False)

class OSParserTest(unittest.TestCase):
    def testMap(self):
        os_parser.load_theory("testMap", verbose=True, check_proof=True)
        
    def testList(self):
        os_parser.load_theory("testList", verbose=True, check_proof=True)

    def testListInt32(self):
        os_parser.load_theory("testListInt32", verbose=True, check_proof=True)

    def testBitvector(self):
        os_parser.load_theory("testBit", verbose=True, check_proof=True)

    def testUcos(self):
        os_parser.load_theory("ucos", verbose=True, check_proof=True)


if __name__ == "__main__":
    unittest.main()
