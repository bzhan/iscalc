import unittest
from integral.rules import SplitSummation
from integral.parser import parse_expr
from integral.context import Context
from integral.poly import normalize


class SummationTest(unittest.TestCase):

    def testSplitSummation1(self):
        test_data = [
            ("SUM(i, 1, 7, i / (i + 1))", "i <= 4", "SUM(n, 1, 4, n / (n + 1)) + SUM(n, 4 + 1, 7, n / (n + 1))"),
            ("SUM(i, 1, 7, i / (i + 1))", "i <= 1", "SUM(n, 1, 1, n / (n + 1)) + SUM(n, 1 + 1, 7, n / (n + 1))"),
            ("SUM(i, 1, 7, i / (i + 1))", "i > 6", "SUM(n, 1, 6, n / (n + 1)) + SUM(n, 6 + 1, 7, n / (n + 1))"),
            ("SUM(i, 1, oo, i / (i + 1))", "i > -1", "SUM(i, 1, oo, i / (i + 1))"),
            ("SUM(i, 1, oo, i / (i + 1))", "i > 7", "SUM(n, 1, 7, n / (n + 1)) + SUM(n, 7 + 1, oo, n / (n + 1))"),
            ("SUM(i, 1, oo, i / (i + 1))", "i < 7", "SUM(n, 1, 7 - 1, n / (n + 1)) + SUM(n, 7, oo, n / (n + 1))"),
            ("SUM(i, 1, oo, i / (i + 1))", "i <= -1", "SUM(i, 1, oo, i / (i + 1))"),
            ("SUM(i, 1, 4, i / (i + 1))", "i > 4", "SUM(i, 1, 4, i / (i + 1))"),
            ("SUM(i, 1, 1, i / (i + 1))", "i = 2", "SUM(i, 1, 1, i / (i + 1))"),
            ("SUM(i, 1, -1, i / (i + 1))", "i = 3", "SUM(i, 1, -1, i / (i + 1))"),
            ("SUM(i, 3, 9, i / (i + 1))", "i < 3", "SUM(i, 3, 9, i / (i + 1))"),
            ("SUM(i, 3, 9, i / (i + 1))", "i >= 6", "SUM(n, 3, 6 - 1, n / (n + 1)) + SUM(n, 6, 9, n / (n + 1))"),
            ("SUM(i, 3, 9, i / (i + 1))", "i >= 9", "SUM(n, 3, 9 - 1, n / (n + 1)) + SUM(n, 9, 9, n / (n + 1))"),
            ("SUM(i, 2, 3, i / (i + 1))", "i = 2", "SUM(n, 2, 2, n / (n + 1)) + SUM(n, 2 + 1, 3, n / (n + 1))"),
            ("SUM(i, 2, 3, i / (i + 1))", "i = 3", "SUM(n, 2, 3 - 1, n / (n + 1)) + SUM(n, 3, 3, n / (n + 1))"),
            ("SUM(i, 2, 3, i / (i + 1))", "i = 1", "SUM(i, 2, 3, i / (i + 1))"),
            ("SUM(i, 2, 4, i / (i + 1))", "i = 3", "SUM(n, 2, 3 - 1, n / (n + 1)) + SUM(n, 3, 3, n / (n + 1)) + SUM(n, 3 + 1, 4, n / (n + 1))"),
            ("SUM(i, 2, 8, i / (i + 1))", "i = 6", "SUM(n, 2, 6 - 1, n / (n + 1)) + SUM(n, 6, 6, n / (n + 1)) + SUM(n, 6 + 1, 8, n / (n + 1))")
        ]
        ctx = Context()
        ctx.load_book('base')
        for e, cond, res in test_data:
            e = parse_expr(e)
            print(e)
            s = SplitSummation(parse_expr(cond))
            print(cond)
            r = s.eval(e, ctx)
            print(r)
            self.assertEqual(str(r), res)

    def testSplitSummation2(self):
        test_data = [
            # ("SUM(i, 1, oo, i / (i + 1))",
            #  "i % 4",
            #  "SUM(j, 0, 4 - 1, SUM(n, 0, floor((oo - 1 - j) / 4), (4 * n + 1 + j) / (4 * n + 1 + j + 1)))"),
            # ("SUM(i, 5, 21, i / (i + k))",
            #  "i % 3",
            #  "SUM(j, 0, 3 - 1, SUM(n, 0, floor((21 - 5 - j) / 3), (3 * n + 5 + j) / (3 * n + 5 + j + k)))"),
            # ("SUM(i, -4, -oo, i / (i + k))",
            #  "i % 100",
            #  "SUM(j, 0, 100 - 1, SUM(n, 0, floor((-oo - -4 - j) / 100), (100 * n + -4 + j) / (100 * n + -4 + j + k)))"),
            # ("SUM(i, -7, -2, i / (i + k))",
            #  "i % 2",
            #  "SUM(j, 0, 2 - 1, SUM(n, 0, floor((-2 - -7 - j) / 2), (2 * n + -7 + j) / (2 * n + -7 + j + k)))"),
            # ("SUM(i, -7, oo, i / (i + k))",
            #  "i % 1",
            #  "SUM(j, 0, 1 - 1, SUM(n, 0, floor((oo - -7 - j) / 1), (1 * n + -7 + j) / (1 * n + -7 + j + k)))"),
            ("SUM(i, m, n, (i + j) / (i + k + l + a))",
             "i % 3",
             "SUM(m, 0, 3 - 1, SUM(n, 0, floor((4 - -7 - m) / 3), (3 * n + -7 + m + j) / (3 * n + -7 + m + k + l + a)))"),
        ]
        ctx = Context()
        ctx.load_book('base')
        for e, cond, res in test_data:
            e = parse_expr(e)
            print(e)
            s = SplitSummation(parse_expr(cond))
            print(cond)
            r = s.eval(e, ctx)
            print(r)
            self.assertEqual(str(r), res)
if __name__ == "__main__":
    unittest.main()