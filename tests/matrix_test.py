import json
import os
import sys
import unittest
from typing import List

from integral import rules, context, parser, compstate, matrix, expr
from integral.context import Context
from integral.expr import Op, Var, Const, Matrix, Expr, Fun

BASE_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.append(BASE_DIR)

class MatrixTest(unittest.TestCase):
    def checkAndOutput(self, file: compstate.CompFile, omit_finish: bool = False):
        # Test parsing of json file
        json_file = file.export()
        for i, item in enumerate(json_file['content']):
            self.assertEqual(compstate.parse_item(file.content[i].parent, item).export(), file.content[i].export())

        # Output to file
        with open('examples/' + file.name + '.json', 'w', encoding='utf-8') as f:
        # with open('../examples/' + file.name + '.json', 'w', encoding='utf-8') as f:
            json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)

        # Test goals are finished
        if not omit_finish:
            for content in file.content:
                self.assertTrue(content.is_finished())

    def testParseMatrix(self):
        test_data = [
            "[[3]]"
        ]

        for s in test_data:
            t = parser.parse_expr(s)
            self.assertEqual(str(t), s)

    def testTranspose1(self):
        test_data = [
            ("[[1,2,3],[4,5,6]]", "[[1,4],[2,5],[3,6]]"),
            ("[[1,2,3],[4,5,6],[7,8,9]]", "[[1,4,7],[2,5,8],[3,6,9]]")
        ]

        for a, b in test_data:
            a = parser.parse_expr(a)
            b = parser.parse_expr(b)
            self.assertEqual(matrix.transpose(a), b)

    def testMultiplication(self):
        test_data = [
            ("[[1,3,5],[2,4,7]]", "[[-5,8,11],[3,9,21],[4,0,8]]", "[[24,35,114],[30,52,162]]"),
            ("[[1,1,0,0]]", "[[1],[2],[3],[4]]", "[[3]]"),
            ("[[1,2]]", "[[1,3,5],[2,4,7]]", "[[5,11,19]]")
        ]

        ctx = Context()
        for a, b, c in test_data:
            a = parser.parse_expr(a)
            b = parser.parse_expr(b)
            c = parser.parse_expr(c)
            res = matrix.multiply(a, b, ctx)
            self.assertEqual(res, c)

    def testHat(self):
        test_data = [
            ("[[a1],[a2],[a3]]", "[[0,-a3,a2],[a3,0,-a1],[-a2,a1,0]]"),
            ("[[v1],[v2],[v3],[w1],[w2],[w3]]",
             "[[0, -w3, w2, v1], [w3, 0, -w1, v2], [-w2, w1, 0, v3], [0,0,0,0]]")
        ]

        for a, b in test_data:
            a = parser.parse_expr(a)
            b = parser.parse_expr(b)
            self.assertEqual(matrix.hat(a), b)

    def testExample01(self):
        file = compstate.CompFile("MIRM", "matrix_example01")
        raw_fixes = [
            ("n", "$int"),
            ("P", "$tensor($real, n, n)"),
            ("A", "$tensor($real, n, n)")
        ]
        fixes = dict()
        for a, b in raw_fixes:
            fixes[a] = parser.parse_expr(b, fixes= fixes)

        goal = file.add_goal("(inv(P) * A * P) ^ n = inv(P) * (A ^ n) * P",
                             fixes=fixes,
                             conds=["invertible(P)", "n > 0"])
        fixes = goal.ctx.get_fixes()
        proof = goal.proof_by_induction(induct_var='n', start=0)
        base_proof = proof.base_case.proof_by_calculation()
        induct_proof = proof.induct_case.proof_by_calculation()
        calc = base_proof.lhs_calc
        calc = base_proof.rhs_calc
        calc = induct_proof.lhs_calc
        old_expr = parser.parse_expr("(inv(P) * A * P) ^ (n + 1)", fixes=fixes)
        new_expr = parser.parse_expr("(inv(P) * A * P) ^ n * (inv(P) * A * P)", fixes=fixes)
        calc.perform_rule(rules.ApplyIdentity(old_expr, new_expr))
        calc.perform_rule(rules.OnSubterm(rules.ApplyInductHyp()))
        calc.perform_rule(rules.FullSimplify())
        old_expr = parser.parse_expr("inv(P) * A ^ n * A * P", fixes=fixes)
        new_expr = parser.parse_expr("inv(P) * (A ^ n * A) * P", fixes=fixes)
        calc.perform_rule(rules.Equation(old_expr, new_expr))
        old_expr = parser.parse_expr("A ^ n * A", fixes=fixes)
        new_expr = parser.parse_expr("A ^ (n + 1)", fixes=fixes)
        calc.perform_rule(rules.ApplyIdentity(old_expr, new_expr))
        assert goal.is_finished()
        self.checkAndOutput(file)

    def testExample02(self):
        file = compstate.CompFile("matrix", "matrix_example02")
        raw_fixes = [
            ("w", "$tensor($real, 3, 1)"),
            ("n", "$int")
        ]
        fixes = dict()
        for s, t in raw_fixes:
            fixes[s] = parser.parse_expr(t, fixes=fixes)
        file.add_definition("w = [[a_1],[a_2],[a_3]]", fixes=fixes)
        goal01 = file.add_goal('hat(w)^2 = w * T(w) - norm(w)^2 * unit_matrix(3)', fixes = fixes)
        proof = goal01.proof_by_calculation()
        calc = proof.rhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandMatFunc()))
        calc.perform_rule(rules.FullSimplify())
        calc = proof.lhs_calc
        old_expr = parser.parse_expr("hat(w) ^ 2", fixes=fixes)
        new_expr = parser.parse_expr("hat(w) ^ 1 * hat(w) ^ 1", fixes=fixes)
        calc.perform_rule(rules.ApplyIdentity(old_expr, new_expr))
        calc.perform_rule(rules.OnSubterm(rules.ExpandMatFunc()))
        calc.perform_rule(rules.FullSimplify())
        assert goal01.is_finished()
        goal02 = file.add_goal("w*T(w)*hat(w) = zero_matrix(3,3)", fixes=fixes)
        proof = goal02.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandMatFunc()))
        calc.perform_rule(rules.FullSimplify())
        calc = proof.rhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandMatFunc()))
        calc.perform_rule(rules.FullSimplify())
        assert goal02.is_finished()

        goal03 = file.add_goal("hat(w)^(2*n+1) = (-1)^n * hat(w)", conds = ["n>=0", "norm(w)=1"], fixes=fixes)
        proof = goal03.proof_by_induction('n', 0)
        base_proof = proof.base_case.proof_by_calculation()
        induct_proof = proof.induct_case.proof_by_calculation()
        calc = induct_proof.lhs_calc
        old_expr = parser.parse_expr("(2 * n + 3)", fixes=fixes)
        new_expr = parser.parse_expr("2 + (2 * n + 1)", fixes=fixes)
        calc.perform_rule(rules.Equation(old_expr, new_expr))
        old_expr = parser.parse_expr("hat(w)^(2 + (2 * n + 1))", fixes=fixes)
        new_expr = parser.parse_expr("hat(w)^2* hat(w)^(2 * n + 1)", fixes=fixes)
        calc.perform_rule(rules.ApplyIdentity(old_expr, new_expr))
        calc.perform_rule(rules.OnSubterm(rules.ApplyInductHyp()))
        eq = parser.parse_expr("hat(w)^2 = w * T(w) - norm(w)^2 * unit_matrix(3)", fixes=fixes)
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(eq), "0"))
        eq = parser.parse_expr("norm(w) = 1", fixes=fixes)
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(eq), "0.1.0.0"))
        calc.perform_rule(rules.ExpandPolynomial())
        old_e = parser.parse_expr("(-1) ^  n *  w * T(w) * hat(w)", fixes=fixes)
        new_e = parser.parse_expr("(-1) ^  n * (w * T(w) * hat(w))", fixes=fixes)
        calc.perform_rule(rules.Equation(old_e, new_e))
        eq = parser.parse_expr("w * T(w) * hat(w) = zero_matrix(3,3)", fixes=fixes)
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(eq), "0.1"))
        # TODO: remove expand func def on subterm
        calc.perform_rule(rules.OnSubterm(rules.ExpandMatFunc()))
        calc.perform_rule(rules.FullSimplify())
        calc = induct_proof.rhs_calc
        # TODO: remove expand func def on subterm
        calc.perform_rule(rules.OnSubterm(rules.ExpandMatFunc()))
        calc.perform_rule(rules.FullSimplify())
        assert goal03.is_finished()

        goal04 = file.add_goal("hat(w) ^ (2 * (n + 1)) = (-1) ^ n * hat(w) ^ 2", conds=["n>=0", "norm(w)=1"], fixes=fixes)
        proof = goal04.proof_by_induction('n', 0)
        base_proof = proof.base_case.proof_by_calculation()
        induct_proof = proof.induct_case.proof_by_calculation()
        calc = induct_proof.lhs_calc
        old_expr = parser.parse_expr("(2 * n + 4)", fixes=fixes)
        new_expr = parser.parse_expr("2 + (2 * (n + 1))", fixes=fixes)
        calc.perform_rule(rules.Equation(old_expr, new_expr))
        old_expr = parser.parse_expr("hat(w) ^ (2 + (2 * (n + 1)))", fixes=fixes)
        new_expr = parser.parse_expr("hat(w) ^ 2 * hat(w) ^ (2 * (n + 1))", fixes=fixes)
        calc.perform_rule(rules.ApplyIdentity(old_expr, new_expr))
        calc.perform_rule(rules.OnSubterm(rules.ApplyInductHyp()))
        eq = parser.parse_expr("hat(w)^2 = w * T(w) - norm(w)^2 * unit_matrix(3)", fixes=fixes)
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(eq), "0"))
        eq = parser.parse_expr("norm(w) = 1", fixes=fixes)
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(eq), "0.1.0.0"))
        calc.perform_rule(rules.ExpandPolynomial())
        old_e = parser.parse_expr("(-1) ^ n *  w * T(w) * hat(w)", fixes=fixes)
        new_e = parser.parse_expr("(-1) ^ n * (w * T(w) * hat(w))", fixes=fixes)
        calc.perform_rule(rules.Equation(old_e, new_e))
        eq = parser.parse_expr("w * T(w) * hat(w) = zero_matrix(3,3)", fixes=fixes)
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(eq), "0.0.1"))
        # TODO: remove expand func def on subterm
        calc.perform_rule(rules.OnSubterm(rules.ExpandMatFunc()))
        calc.perform_rule(rules.FullSimplify())
        calc = induct_proof.rhs_calc
        old_e = parser.parse_expr("hat(w) ^ 2", fixes=fixes)
        new_e = parser.parse_expr("hat(w) * hat(w)", fixes=fixes)
        calc.perform_rule(rules.Equation(old_e, new_e))
        # TODO: remove expand func def on subterm
        calc.perform_rule(rules.OnSubterm(rules.ExpandMatFunc()))
        calc.perform_rule(rules.FullSimplify())
        assert goal04.is_finished()

        self.checkAndOutput(file)


    def testGetType(self):
        raw_fixes = [('n', '$int'), ('P', '$tensor($real, n, n)'), ('A', '$tensor($real, n, n)')]
        fixes = dict()
        for a, b in raw_fixes:
            fixes[a] = parser.parse_expr(b, fixes=fixes)
        e = parser.parse_expr("inv(P) * A * P", fixes=fixes)

        assert e.type == expr.MatrixType(expr.RealType, Var('n', type=expr.IntType), Var('n', type=expr.IntType))
        e = e ^ Const(0)
        from integral import poly
        from integral.poly import normalize
        ctx = Context()
        e = normalize(e, ctx)
        assert e == parser.parse_expr("unit_matrix(n)", fixes=fixes)

    def testExample06(self):
        file = compstate.CompFile("base", "matrix_example06")
        fixes = dict()
        fixes['n'] = parser.parse_expr('$int')
        goal01 = file.add_goal('1 - cos(a) = SUM(n, 0, oo, (-1) ^ n * a ^ (2 * (n + 1)) / factorial(2 * (n + 1)))', fixes=fixes)
        proof = goal01.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.SeriesExpansionIdentity(old_expr="cos(a)"))
        s = parser.parse_expr("n = 0", fixes=fixes)
        calc.perform_rule(rules.OnLocation(rules.SplitSummation(s), "1"))
        calc.perform_rule(rules.FullSimplify())
        s1 = "-SUM(n, 1, oo, a ^ (2 * n) * (-1) ^ n / factorial(2 * n))"
        s2 = "SUM(n, 1, oo, (-1) * ((-1) ^ n * a ^ (2 * n) / factorial(2 * n)))"
        calc.perform_rule(rules.Equation(s1, s2))
        calc.perform_rule(rules.ChangeSummationIndex(new_lower='0'))
        calc.perform_rule(rules.FullSimplify())
        s3 = parser.parse_expr("a ^ (2 * n + 2) * (-1) ^ n / factorial(2 * n + 2)", fixes=fixes)
        s4 = parser.parse_expr("(-1) ^ n * a ^ (2 * (n + 1)) / factorial(2 * (n + 1))", fixes=fixes)
        calc.perform_rule(rules.Equation(s3, s4))
        self.checkAndOutput(file)


    def testRodrigues(self):
        file = compstate.CompFile("MIRM", "matrix_rodrigues")
        fixes = dict()
        fixes['w'] = parser.parse_expr('$tensor($real, 3, 1)')
        fixes['n'] = parser.parse_expr('$int')
        file.add_definition("w = [[a_1],[a_2],[a_3]]", fixes=fixes)
        goal01 = file.add_goal("exp(hat(w) * x) = unit_matrix(3) + sin(x) * hat(w) + (1 - cos(x)) * (hat(w)) ^ 2",
                               conds=["x >= 0", "norm(w)=1"],
                               fixes=fixes)
        proof = goal01.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.SeriesExpansionIdentity())
        cond = parser.parse_expr("n % 2", fixes=fixes)
        calc.perform_rule(rules.SplitSummation(cond))
        cond = parser.parse_expr("n = 0", fixes=fixes)
        calc.perform_rule(rules.OnLocation(rules.SplitSummation(cond), "1"))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.ChangeSummationIndex(new_lower="0"), "0.1"))
        s1 = parser.parse_expr("(x * hat(w)) ^ (2 * n + 1)", fixes=fixes)
        s2 = parser.parse_expr("x ^ (2 * n + 1) * hat(w) ^ (2 * n + 1)", fixes=fixes)
        calc.perform_rule(rules.ApplyIdentity(s1, s2))
        s3 = parser.parse_expr("(x * hat(w)) ^ (2 * (n + 1))", fixes=fixes)
        s4 = parser.parse_expr("x ^ (2 * (n + 1)) * hat(w) ^ (2 * (n + 1))", fixes=fixes)
        calc.perform_rule(rules.ApplyIdentity(s3, s4))
        s5 = parser.parse_expr("hat(w) ^ (2 * n + 1) = (-1) ^ n * hat(w)", fixes=fixes)
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(s5), "0.0.0.0.1"))
        s6 = parser.parse_expr("hat(w) ^ (2 * (n + 1)) = (-1) ^ n * hat(w) ^ 2", fixes=fixes)
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(s6), "0.1.0.0.1"))
        s7 = parser.parse_expr("SUM(n, 0, oo, x ^ (2 * n + 1) * ((-1) ^ n * hat(w)) / factorial(2 * n + 1))", fixes=fixes)
        s8 = parser.parse_expr("hat(w) * SUM(n, 0, oo, (-1) ^ n * x ^ (2 * n + 1) / factorial(2 * n + 1))", fixes=fixes)

        calc.perform_rule(rules.Equation(s7, s8))
        calc.perform_rule(rules.OnLocation(rules.SeriesEvaluationIdentity(), "0.0.1"))
        s = parser.parse_expr("SUM(n, 0, oo, x ^ (2 * (n + 1)) * ((-1) ^ n * hat(w) ^ 2) / factorial(2 * (n + 1)))", fixes=fixes)
        t = parser.parse_expr("hat(w) ^ 2 * SUM(n, 0, oo, (-1) ^ n * x ^ (2 * (n + 1)) / factorial(2 * (n + 1)))", fixes=fixes)
        calc.perform_rule(rules.Equation(s, t))
        t = parser.parse_expr("SUM(n, 0, oo, (-1) ^ n * a ^ (2 * (n + 1)) / factorial(2 * (n + 1)))", fixes=fixes)
        s = parser.parse_expr("1 - cos(a)", fixes=fixes)
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(Op('=', s, t)), "0.1.1"))
        calc.perform_rule(rules.FullSimplify())
        calc = proof.rhs_calc
        calc.perform_rule(rules.FullSimplify())
        assert goal01.is_finished()
        self.checkAndOutput(file)

    def testMy(self):
        e = parser.parse_expr("SKOLEM_FUNC(C(a))")
        pat = expr.expr_to_pattern(e)
        print(pat)

if __name__ == "__main__":
    unittest.main()
