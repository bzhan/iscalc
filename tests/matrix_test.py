import unittest
from typing import List
from integral.expr import Op, Var, Const, Matrix, Vector, Expr
class MatrixTest(unittest.TestCase):

    def testTranspose1(self):
        m = Matrix((2,3), [[1,2,3],[4,5,6]])
        res = "[1, 4]\n[2, 5]\n[3, 6]"
        assert str(m.t) == res

    def testTranspose2(self):
        m = Matrix((3, 3), [[1, 2, 3], [4, 5, 6], [7,8,9]])
        res = "[1, 4, 7]\n[2, 5, 8]\n[3, 6, 9]"
        assert str(m.t) == res

    def testMultiplication1(self):
        m1 = Matrix((2,3), [[Const(1), Const(3), Const(5)],
                            [Const(2), Const(4), Const(7)]])
        m2 = Matrix((3,3), [[Const(-5), Const(8), Const(11)],
                            [Const(3), Const(9), Const(21)],
                            [Const(4), Const(0), Const(8)]])
        res = "[1 * -5 + 3 * 3 + 5 * 4, 1 * 8 + 3 * 9 + 5 * 0, 1 * 11 + 3 * 21 + 5 * 8]\n\
[2 * -5 + 4 * 3 + 7 * 4, 2 * 8 + 4 * 9 + 7 * 0, 2 * 11 + 4 * 21 + 7 * 8]"
        assert res == str(m1 * m2)

    def testMultiplication2(self):
        v1 = Vector([Const(1), Const(1), Const(0), Const(0)], is_column=False)
        v2 = Vector([Const(1), Const(2), Const(3), Const(4)])
        res = "1 * 1 + 1 * 2 + 0 * 3 + 0 * 4"
        self.assertEqual(str(v1 * v2), res)
        self.assertIsInstance(v1*v2, Expr)

    def testMultiplication3(self):
        m = Matrix((2,3), [[Const(1), Const(3), Const(5)],
                            [Const(2), Const(4), Const(7)]])
        v = Vector([Const(1), Const(2), Const(1)])
        res = m * v
        s = "[1 * 1 + 3 * 2 + 5 * 1]\n\
[2 * 1 + 4 * 2 + 7 * 1]"
        self.assertIsInstance(res, Vector)
        self.assertTrue(res.is_column)
        self.assertEqual(str(res), s)

    def testMultiplication4(self):
        v = Vector([Const(1), Const(2)], is_column=False)
        m = Matrix((2, 3), [[Const(1), Const(3), Const(5)],
                            [Const(2), Const(4), Const(7)]])

        res = v * m
        s = "[1 * 1 + 2 * 2, 1 * 3 + 2 * 4, 1 * 5 + 2 * 7]"
        self.assertIsInstance(res, Vector)
        self.assertTrue(res.is_row)
        self.assertEqual(str(res), s)

    def testHatAndVee1(self):
        v = Vector([Var('a1'), Var('a2'), Var('a3')])
        s = "[0, -a3, a2]\n\
[a3, 0, -a1]\n\
[-a2, a1, 0]"
        self.assertEqual(str(v.hat), s)
        self.assertEqual(str(v.hat.vee), str(v))

    def testHatAndVee2(self):
        v = Vector([Var('v1'), Var('v2'), Var('v3'), Var('w1'), Var('w2'), Var('w3')])
        s = "[0, -w3, w2, v1]\n\
[w3, 0, -w1, v2]\n\
[-w2, w1, 0, v3]\n\
[0, 0, 0, 0]"
        self.assertEqual(str(v.hat), s)
        self.assertEqual(str(v.hat.vee), str(v))



