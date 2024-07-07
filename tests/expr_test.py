"""Unit test for expressions."""

import unittest

from integral import parser


class ExprTest(unittest.TestCase):
    def testAlphaEquiv(self):
        t1 = parser.parse_expr("INT x:[1,2]. x ^ 2")
        t2 = parser.parse_expr("INT y:[1,2]. y ^ 2")
        self.assertEqual(t1, t2)
        self.assertEqual(hash(t1), hash(t2))


if __name__ == "__main__":
    unittest.main()
