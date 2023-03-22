import unittest

import integral.context
from integral.parser import parse_expr
from integral.condprover import init_all_conds, check_cond, saturate_expr, check_condition, \
    subject_of, print_all_conds
from integral.conditions import Conditions
from integral.context import Identity, Context


class CondProverTest(unittest.TestCase):
    def testCheckCondConstant(self):
        test_data = [
            # Basic
            ("-1 < 0", True),
            ("0 < 0", False),
            ("0 <= 0", True),
            ("1 <= 0", False),
            ("0 > -1", True),
            ("0 > 0", False),
            ("0 >= 0", True),
            ("0 >= 1", False),
            ("0 = 0", True),
            ("0 != 0", False),

            # Trigonometric
            ("sin(0) = 0", True),
            ("cos(0) = 1", True),
            ("sin(pi/2) = 1", True),
            ("cos(pi/2) = 0", True),
            ("sin(pi) = 0", True),
            ("cos(pi) = -1", True),
            ("sin(pi/4) = sqrt(2)/2", True),
            ("cos(pi/4) = sqrt(2)/2", True),
            ("tan(pi/4) = 1", True),

            # Exponential and log
            ("exp(0) = 1", True),
            ("log(1) = 0", True),
        ]

        all_conds = dict()
        for s, res in test_data:
            e = parse_expr(s)
            inst = dict()
            self.assertEqual(len(check_cond(e, all_conds, inst)) == 1, res, s)

    def testCheckCond(self):
        test_data = [
            # less and less_eq
            ("x < 0", ["x < 0"], True),
            ("x < 0", ["x <= 0"], False),
            ("x < 0", ["x <= -1"], True),
            ("x <= 0", ["x <= 0"], True),
            ("x <= 0", ["x < 0"], True),
            ("x <= 0", ["x <= -1"], True),

            # greater and greater_eq
            ("x > 0", ["x > 0"], True),
            ("x > 0", ["x >= 0"], False),
            ("x > 0", ["x >= 1"], True),
            ("x >= 0", ["x >= 0"], True),
            ("x >= 0", ["x > 0"], True),
            ("x >= 0", ["x >= 1"], True),
        ]

        for s, conds, res in test_data:
            e = parse_expr(s)
            conds = Conditions(conds)
            all_conds = init_all_conds(conds)
            inst = dict()
            self.assertEqual(len(check_cond(e, all_conds, inst)) == 1, res, "%s [%s]" % (e, conds))

    def testSaturateExpr(self):
        cos_identity = Identity("cos(?x) >= 0", conds=Conditions(["?x >= -pi / 2", "?x <= pi / 2"]))
        test_data = [
            (["x >= 0", "x <= pi / 2"], True),
            (["x >= 0", "x < pi / 2"], True),
            (["x >= -pi / 2", "x <= pi / 2"], True),
            (["x >= 0", "x <= pi"], False),
        ]
        ctx = integral.context.Context()
        for conds, res in test_data:
            conds = Conditions(conds)
            all_conds = init_all_conds(conds)
            saturate_expr(parse_expr("cos(x)"), cos_identity, all_conds, ctx)
            inst = dict()
            e = parse_expr("cos(x) >= 0")
            self.assertEqual(len(check_cond(e, all_conds, inst)) == 1, res, conds)

    def testSaturateExpr2(self):
        log_identity = Identity("log(?x) >= 0", conds=Conditions(["?x >= 1"]))
        test_data = [
            (["x > 1"], True),
            (["x > 0"], False),
        ]
        ctx = integral.context.Context()
        for conds, res in test_data:
            conds = Conditions(conds)
            all_conds = init_all_conds(conds)
            saturate_expr(parse_expr("log(x)"), log_identity, all_conds, ctx)
            inst = dict()
            e = parse_expr("log(x) >= 0")
            self.assertEqual(len(check_cond(e, all_conds, inst)) == 1, res, conds)

    def testSaturateExpr3(self):
        ineq_identity = Identity("?a + ?c != ?b + ?c", conds=Conditions(["?a != ?b"]))
        test_data = [
            ("k + 1 != 0", ["k != -1"], True),
        ]
        ctx = integral.context.Context()
        for s, conds, res in test_data:
            e = parse_expr(s)
            conds = Conditions(conds)
            all_conds = init_all_conds(conds)
            saturate_expr(subject_of(e), ineq_identity, all_conds, ctx)
            inst = dict()
            self.assertEqual(len(check_cond(e, all_conds, inst)) == 1, res, "%s [%s]" % (e, conds))

    def testCheckCondition(self):
        test_data = [
            ("cos(x) >= 0", ["x > 0", "x < pi / 2"], True),
            ("log(x) >= 0", ["x > 1"], True),
            ("1 + x ^ 2 > 0", ["x > 0"], True),
            ("1 + x ^ 2 > 0", ["x > 0", 'x<1'], True),
            ("sin(x) > 0", ["x > 0", "x < pi / 2"], True),
            ("x ^ 2 < 1", ["abs(x) < 1"], True),
            ("2 * k + 1 > 0", ["k >= 0"], True),
            ("sqrt(1 - x ^ 2) > 0", ["x > 0", "x < 1"], True),
            ("y * x > -1", ["y > -1", "y < 1", "x > 0", "x < 1"], True),
            ("a ^ 2 + b ^ 2 > 0", ["a != 0"], True),
            ("-k + 1 != 0", ["k > 1"], True),
            ("(p ^ 2 - 5) ^ 2 - 16 != 0", ["p > 3"], True),
        ]

        for s, conds, res in test_data:
            e = parse_expr(s)
            ctx = Context()
            ctx.load_book("base")
            conds = Conditions(conds)
            ctx.extend_condition(conds)
            self.assertEqual(check_condition(e, ctx), res, "%s [%s]" % (e, conds))


if __name__ == "__main__":
    unittest.main()