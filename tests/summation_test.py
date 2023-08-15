import unittest
from integral.rules import SplitSummation
from integral.parser import parse_expr
from integral.context import Context


class SummationTest(unittest.TestCase):

    def testSplitSummation1(self):
        test_data = [
            ("SUM(i, 1, 7, i / (i + 1))", "i <= 4", "SUM(i, 1, 4, i / (i + 1)) + SUM(i, 5, 7, i / (i + 1))"),
            ("SUM(i, 1, 7, i / (i + 1))", "i <= 1", "SUM(i, 2, 7, i / (i + 1)) + 1/2"),
            ("SUM(i, 1, 7, i / (i + 1))", "i > 6", "SUM(i, 1, 6, i / (i + 1)) + 7/8"),
            ("SUM(i, 1, oo, i / (i + 1))", "i > -1", "SUM(i, 1, oo, i / (i + 1))"),
            ("SUM(i, 1, oo, i / (i + 1))", "i > 7", "SUM(i, 1, 7, i / (i + 1)) + SUM(i, 8, oo, i / (i + 1))"),
            ("SUM(i, 1, oo, i / (i + 1))", "i < 7", "SUM(i, 1, 6, i / (i + 1)) + SUM(i, 7, oo, i / (i + 1))"),
            ("SUM(i, 1, oo, i / (i + 1))", "i <= -1", "SUM(i, 1, oo, i / (i + 1))"),
            ("SUM(i, 1, 4, i / (i + 1))", "i > 4", "SUM(i, 1, 4, i / (i + 1))"),
            ("SUM(i, 1, 1, i / (i + 1))", "i = 2", "1/2"),
            ("SUM(i, 1, -1, i / (i + 1))", "i = 3", "0"),
            ("SUM(i, 3, 9, i / (i + 1))", "i < 3", "SUM(i, 3, 9, i / (i + 1))"),
            ("SUM(i, 3, 9, i / (i + 1))", "i >= 6", "SUM(i, 3, 5, i / (i + 1)) + SUM(i, 6, 9, i / (i + 1))"),
            ("SUM(i, 3, 9, i / (i + 1))", "i >= 9", "SUM(i, 3, 8, i / (i + 1)) + 9/10"),
            ("SUM(i, 2, 3, i / (i + 1))", "i = 2", "17/12"),
            ("SUM(i, 2, 3, i / (i + 1))", "i = 3", "17/12"),
            ("SUM(i, 2, 3, i / (i + 1))", "i = 1", "SUM(i, 2, 3, i / (i + 1))"),
            ("SUM(i, 2, 4, i / (i + 1))", "i = 3", "133/60"),
            ("SUM(i, 2, 8, i / (i + 1))", "i = 6", "SUM(i, 2, 5, i / (i + 1)) + SUM(i, 7, 8, i / (i + 1)) + 6/7")
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
            ("SUM(i, 1, oo, i / (i + 1))",
             "i % 4",
             "SUM(i, 0, oo, (4 * i + 1) / (4 * i + 2)) + "
             "SUM(i, 0, oo, (4 * i + 2) / (4 * i + 3)) + "
             "SUM(i, 0, oo, (4 * i + 3) / (4 * i + 4)) + "
             "SUM(i, 0, oo, (4 * i + 4) / (4 * i + 5))"),
            ("SUM(i, 5, 21, i / (i + k))",
             "i % 3",
             "SUM(i, 0, 5, (3 * i + 5) / (3 * i + k + 5)) + "
             "SUM(i, 0, 5, (3 * i + 6) / (3 * i + k + 6)) + "
             "SUM(i, 0, 4, (3 * i + 7) / (3 * i + k + 7))"),
            ("SUM(i, -4, -oo, i / (i + k))",
             "i % 100",
             "0"),
            ("SUM(i, -7, -2, i / (i + k))",
             "i % 2",
             "SUM(i, 0, 2, (2 * i - 6) / (2 * i + k - 6)) + "
             "SUM(i, 0, 2, (2 * i - 7) / (2 * i + k - 7))"),
            ("SUM(i, -7, oo, i / (i + k))",
             "i % 1",
             "SUM(i, 0, oo, (i - 7) / (i + k - 7))")
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
