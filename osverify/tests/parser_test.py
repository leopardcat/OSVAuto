"""Unit test for parsing"""

import unittest

from osverify import os_parser
from osverify import os_theory
from osverify import os_tactics
from osverify import os_z3wrapper

def initTheory() -> os_theory.OSTheory:
    return os_parser.load_theory("basic", verbose=False)

class OSParserTest(unittest.TestCase):

    def testBitvector(self):
        os_parser.load_theory("testBit", verbose=True, check_proof=True)

    def testUcos(self):
        os_parser.load_theory("ucos", verbose=True, check_proof=True)

    def testLiteOS(self):
        os_parser.load_theory("liteos2", verbose=True, check_proof=True)

    def testSeqTest(self):
        os_parser.load_theory("testSeq", verbose=True, check_proof=True)

    def testCCW(self):
        os_parser.load_theory("ccw", verbose=True, check_proof=True)


if __name__ == "__main__":
    unittest.main()
