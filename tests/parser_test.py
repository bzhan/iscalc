"""Unit test for parsing."""

import unittest
from fractions import Fraction
from decimal import Decimal

from integral import expr
from integral.expr import Var, Const, Op, Fun, Matrix
from integral.parser import parse_expr


class ParserTest(unittest.TestCase):
    def testParseType(self):
        test_data = [
            "$real",
            "$tensor($real, 3)",
            "$tensor($real, 2, 3)",
        ]

        for s in test_data:
            t = parse_expr(s)
            self.assertEqual(str(t), s)

    def testParseTerm(self):
        test_data = [
            "x", "1", "11/10", "-1", "-11/10",
            "x + y", "x - y", "-x", "x * y", "x / y", "x ^ y",
            "x + y * z", "(x + y) * z",
            "x * y + z", "x * (y + z)",
            "x * y ^ 2", "(x * y) ^ 2",
            "sin(x)", "cos(x)", "log(x)", "exp(x)",
            "D x. 3 * x",
            "INT x:[1,2]. 3 * x",
            "[3 * x]_x=1,2",
            "INT x:[0,pi / 4]. sin(x)",
            "x ^ (1/2)",
            '(-2) ^ n',
            '(-2) ^ (n + 1)',
            'a ^ b * c ^ d',
            '(-1) ^ n * factorial(n) / (m + 1) ^ (n + 1)',
            'x ^ m * log(x) ^ n',
            '(-c) ^ k / (k * a + 1) ^ (k + 1)',
            'x ^ (c * x ^ a)',
            '(c * x ^ a * log(x)) ^ k',
            '(c * x ^ a) ^ k * log(x) ^ k',
        ]

        for s in test_data:
            e = parse_expr(s)
            self.assertEqual(str(e), s)

    def testParseTerm2(self):
        test_data = [
            ("-x", -Var("x")),
            ("-2", Const(-2)),
            ("1/2", Const(Fraction(1) / 2)),
            ("-1/2", Const(Fraction(-1) / 2)),
            # ("0.5", Const(Decimal("0.5"))),
            ("pi", Fun("pi")),
            ("-x^2", Op("-", Op("^", Var("x"), Const(2)))),
            ('a ^ b * c ^ d', Op('*', Op('^', Var('a'), Var('b')), Op('^', Var('c'), Var('d')))),
            ('a * -b', Op('*', Var('a'), Op('-', Var('b')))),
            ('(-x) ^ k * log(x)', Op('*', Op('^', Op('-',Var('x')), Var('k')), Fun('log', Var('x')))),
            ("x^m * log(x) ^ n", Op('*', Op('^', Var('x'), Var('m')), Op('^', Fun('log',Var('x')), Var('n')))),
            ("(-1)^n * factorial(n) / (m+1) ^ (n+1)", Op('/', Op('*', Op('^', Const(-1), Var('n')), Fun("factorial", Var('n'))), Op('^', Op('+', Var('m'), Const(1)), Op('+', Var('n'), Const(1))))),
            ("(-c) ^ k / (k * a + 1) ^ (k + 1)", Op('/', Op('^', Op('-', Var('c')), Var('k')), Op('^', Op('+', Op('*', Var('k'), Var('a')), Const(1)), Op('+', Var('k'), Const(1))))),
        ]

        for s, e, in test_data:
            self.assertEqual(parse_expr(s), e)

    def testParseVector(self):
        test_data = [
            ("[[1],[2],[3]]", Matrix([[Const(1)], [Const(2)], [Const(3)]])),
            ("T([[1],[2],[3]])", Fun("T",Matrix([[Const(1)], [Const(2)], [Const(3)]])))
        ]
        for s, r in test_data:
            e = parse_expr(s)
            self.assertEqual(e, r)
    def testParseMatrix(self):
        test_data = [
            ("{{1,2,3}, {4,5,6}}", Matrix([Vector([Const(1), Const(2), Const(3)], is_column=False),\
                                           Vector([Const(4), Const(5), Const(6)], is_column=False)],\
                                           is_row=True)),
            ("{T({1,2,3}), T({4,5,6})}", Matrix([Vector([Const(1), Const(2), Const(3)], is_column=True), \
                                             Vector([Const(4), Const(5), Const(6)], is_column=True)], \
                                             is_row=False)),
            ("T({T({1,2,3}), T({4,5,6})})", Matrix([Vector([Const(1), Const(2), Const(3)], is_column=False),\
                                           Vector([Const(4), Const(5), Const(6)], is_column=False)],\
                                           is_row=True))
        ]
        for s, r in test_data:
            e = parse_expr(s)
            self.assertEqual(e, r)

    def testMatrixVar(self):
        test_data = [("matrix a[2][3]", "matrix a[2][3]"),
                     ("matrix A[n][n]", "matrix A[n][n]"),
                     ("a", "a")]
        for s, res in test_data:
            self.assertEqual(str(parse_expr(s)), res)

if __name__ == "__main__":
    unittest.main()
