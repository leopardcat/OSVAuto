"""Unit test for utility functions"""

import unittest

from osverify import os_util

class UtilTest(unittest.TestCase):
    def testTopologicalSort(self):
        graph = {
            5: [2, 0],
            4: [0, 1],
            2: [3],
            3: [1],
            0: [],
            1: []
        }
        self.assertEqual(os_util.topological_sort(graph), [5, 4, 2, 0, 3, 1])


if __name__ == "__main__":
    unittest.main()
