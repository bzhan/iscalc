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
        proof = goal.proof_by_induction(induct_var='n', start=0)
        _ = proof.base_case.proof_by_calculation()
        induct_proof = proof.induct_case.proof_by_calculation()
        calc = induct_proof.lhs_calc
        old_expr = calc.parse_expr("(inv(P) * A * P) ^ (n + 1)")
        new_expr = calc.parse_expr("(inv(P) * A * P) ^ n * (inv(P) * A * P)")
        calc.perform_rule(rules.ApplyIdentity(old_expr, new_expr))
        calc.perform_rule(rules.OnSubterm(rules.ApplyInductHyp()))
        calc.perform_rule(rules.FullSimplify())
        old_expr = calc.parse_expr("inv(P) * A ^ n * A * P")
        new_expr = calc.parse_expr("inv(P) * (A ^ n * A) * P")
        calc.perform_rule(rules.Equation(old_expr, new_expr))
        old_expr = calc.parse_expr("A ^ n * A")
        new_expr = calc.parse_expr("A ^ (n + 1)")
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

        goal01 = file.add_goal('hat(w)^2 = w * T(w) - norm(w)^2 * unit_matrix(3)', fixes = fixes)
        proof = goal01.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandMatFunc()))
        calc = proof.rhs_calc
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
        assert goal02.is_finished()

        goal03 = file.add_goal("hat(w)^(2*n+1) = (-1)^n * hat(w)", conds = ["n>=0", "norm(w)=1"], fixes=fixes)
        proof = goal03.proof_by_induction('n', 0)
        _ = proof.base_case.proof_by_calculation()
        induct_proof = proof.induct_case.proof_by_calculation()
        calc = induct_proof.lhs_calc
        old_expr = calc.parse_expr("(2 * n + 3)")
        new_expr = calc.parse_expr("2 + (2 * n + 1)")
        calc.perform_rule(rules.Equation(old_expr, new_expr))
        old_expr = calc.parse_expr("hat(w)^(2 + (2 * n + 1))")
        new_expr = calc.parse_expr("hat(w)^2* hat(w)^(2 * n + 1)")
        calc.perform_rule(rules.ApplyIdentity(old_expr, new_expr))
        calc.perform_rule(rules.OnSubterm(rules.ApplyInductHyp()))
        eq = calc.parse_expr("hat(w)^2 = w * T(w) - norm(w)^2 * unit_matrix(3)")
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(eq), "0"))
        eq = calc.parse_expr("norm(w) = 1")
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(eq), "0.1.0.0"))
        calc.perform_rule(rules.ExpandPolynomial())
        old_e = calc.parse_expr("(-1) ^  n *  w * T(w) * hat(w)")
        new_e = calc.parse_expr("(-1) ^  n * (w * T(w) * hat(w))")
        calc.perform_rule(rules.Equation(old_e, new_e))
        eq = calc.parse_expr("w * T(w) * hat(w) = zero_matrix(3,3)")
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(eq), "0.1"))
        calc.perform_rule(rules.FullSimplify())
        calc = induct_proof.rhs_calc
        assert goal03.is_finished()

        goal04 = file.add_goal("hat(w) ^ (2 * (n + 1)) = (-1) ^ n * hat(w) ^ 2", conds=["n>=0", "norm(w)=1"], fixes=fixes)
        proof = goal04.proof_by_induction('n', 0)
        _ = proof.base_case.proof_by_calculation()
        induct_proof = proof.induct_case.proof_by_calculation()
        calc = induct_proof.lhs_calc
        old_expr = calc.parse_expr("(2 * n + 4)")
        new_expr = calc.parse_expr("2 + (2 * (n + 1))")
        calc.perform_rule(rules.Equation(old_expr, new_expr))
        old_expr = calc.parse_expr("hat(w) ^ (2 + (2 * (n + 1)))")
        new_expr = calc.parse_expr("hat(w) ^ 2 * hat(w) ^ (2 * (n + 1))")
        calc.perform_rule(rules.ApplyIdentity(old_expr, new_expr))
        calc.perform_rule(rules.OnSubterm(rules.ApplyInductHyp()))
        eq = calc.parse_expr("hat(w)^2 = w * T(w) - norm(w)^2 * unit_matrix(3)")
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(eq), "0"))
        eq = calc.parse_expr("norm(w) = 1")
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(eq), "0.1.0.0"))
        calc.perform_rule(rules.ExpandPolynomial())
        old_e = calc.parse_expr("(-1) ^ n *  w * T(w) * hat(w)")
        new_e = calc.parse_expr("(-1) ^ n * (w * T(w) * hat(w))")
        calc.perform_rule(rules.Equation(old_e, new_e))
        eq = calc.parse_expr("w * T(w) * hat(w) = zero_matrix(3,3)")
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(eq), "0.0.1"))
        calc.perform_rule(rules.FullSimplify())
        calc = induct_proof.rhs_calc
        old_e = calc.parse_expr("hat(w) ^ 2")
        new_e = calc.parse_expr("hat(w) * hat(w)")
        calc.perform_rule(rules.Equation(old_e, new_e))
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

        goal01 = file.add_goal("exp(hat(w) * x) = unit_matrix(3) + sin(x) * hat(w) + (1 - cos(x)) * (hat(w)) ^ 2",
                               conds=["norm(w) = 1"],
                               fixes=fixes)
        proof = goal01.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.SeriesExpansionIdentity())
        cond = calc.parse_expr("n % 2")
        calc.perform_rule(rules.SplitSummation(cond))
        cond = parser.parse_expr("i = 0", fixes=fixes)
        calc.perform_rule(rules.OnLocation(rules.SplitSummation(cond), "1"))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.ChangeSummationIndex(new_lower="0"), "0.1"))
        s1 = calc.parse_expr("(x * hat(w)) ^ (2 * i + 1)")
        s2 = calc.parse_expr("x ^ (2 * i + 1) * hat(w) ^ (2 * i + 1)")
        calc.perform_rule(rules.ApplyIdentity(s1, s2))
        s3 = calc.parse_expr("(x * hat(w)) ^ (2 * (n + 1))")
        s4 = calc.parse_expr("x ^ (2 * (n + 1)) * hat(w) ^ (2 * (n + 1))")
        calc.perform_rule(rules.ApplyIdentity(s3, s4))
        s5 = calc.parse_expr("hat(w) ^ (2 * n + 1) = (-1) ^ n * hat(w)")
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(s5), "0.0.0.0.1"))
        s6 = calc.parse_expr("hat(w) ^ (2 * (n + 1)) = (-1) ^ n * hat(w) ^ 2")
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(s6), "0.1.0.0.1"))

        s7 = calc.parse_expr("SUM(n, 0, oo, x ^ (2 * n + 1) * ((-1) ^ n * hat(w)) / factorial(2 * n + 1))")
        s8 = calc.parse_expr("hat(w) * SUM(n, 0, oo, (-1) ^ n * x ^ (2 * n + 1) / factorial(2 * n + 1))")
        calc.perform_rule(rules.Equation(s7, s8))
        calc.perform_rule(rules.OnLocation(rules.SeriesEvaluationIdentity(), "0.0.1"))
        s = calc.parse_expr("SUM(n, 0, oo, x ^ (2 * (n + 1)) * ((-1) ^ n * hat(w) ^ 2) / factorial(2 * (n + 1)))")
        t = calc.parse_expr("hat(w) ^ 2 * SUM(n, 0, oo, (-1) ^ n * x ^ (2 * (n + 1)) / factorial(2 * (n + 1)))")
        calc.perform_rule(rules.Equation(s, t))
        t = calc.parse_expr("SUM(n, 0, oo, (-1) ^ n * a ^ (2 * (n + 1)) / factorial(2 * (n + 1)))")
        s = calc.parse_expr("1 - cos(a)")
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(Op('=', s, t)), "0.1.1"))
        calc.perform_rule(rules.FullSimplify())
        calc = proof.rhs_calc
        calc.perform_rule(rules.FullSimplify())
        assert goal01.is_finished()
        self.checkAndOutput(file)

    def testTwistMatrixExpInv(self):
        file = compstate.CompFile("MIRM", "twist_matrix_exp_inv")
        fixes = dict()
        fixes['w'] = parser.parse_expr('$tensor($real, 3, 1)')
        fixes['v'] = parser.parse_expr('$tensor($real, 3, 1)')
        fixes2 = dict()
        fixes['R'] = parser.parse_expr('$tensor($real, 3, 1)')
        fixes['p'] = parser.parse_expr('$tensor($real, 3, 1)')
        file.add_definition("hm(R, p) = rcon(ccon(R,p), ccon(zero_matrix(1,3),unit_matrix(1)))", fixes=fixes2,
                            conds=['type(R, 0, 3, 3)', 'type(p, 0 ,3, 1)'])
        file.add_definition("hmf(t, w, v) = hm(unit_matrix(3), t*v)", fixes=fixes,
                            conds=['type(w, 0 ,3)', 'type(v, 0 ,3)', 'norm(w)=0'])
        file.add_definition("hmf(t, w, v) = hm(exp(t*hat(w)), (unit_matrix(3)-exp(t*hat(w)))*(hat(w)*v)+(w*T(w)*v*t))", fixes=fixes,
                            conds=['type(w, 0, 3)', 'type(v, 0, 3)', 'norm(w)!=0'])
        goal01 = file.add_goal("exp(t * hat(w)) * exp(-(t * hat(w))) = unit_matrix(3)", fixes=fixes)
        proof = goal01.proof_by_calculation()
        calc = proof.lhs_calc
        lemma = calc.parse_expr("exp(t * hat(w)) = unit_matrix(3) + sin(t) * hat(w) + (1 - cos(t)) * (hat(w)) ^ 2")
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(lemma), '0'))
        s1 = calc.parse_expr("-(t * hat(w))")
        s2 = calc.parse_expr("-t * hat(w)")
        calc.perform_rule(rules.Equation(s1, s2))
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(lemma), '1'))
        calc.perform_rule(rules.ExpandPolynomial())
        calc.perform_rule(rules.FullSimplify())
        s1 = calc.parse_expr("(-cos(t) + 1) ^ 2 * hat(w) ^ 2 * hat(w) ^ 2")
        s2 = calc.parse_expr("(-cos(t) + 1) ^ 2 * (hat(w) ^ 2 * hat(w) ^ 2)")
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = calc.parse_expr("hat(w) ^ 2 * hat(w) ^ 2")
        s2 = calc.parse_expr("hat(w) ^ (2 + 2)")
        calc.perform_rule(rules.OnLocation(rules.ApplyIdentity(s1, s2), "0.0.0.0.0.1"))
        print(goal01)
        goal02 = file.add_goal("hmf(t, w, v) * hmf(-t, w, v) = unit_matrix(4)", fixes=fixes,
                               conds=['norm(w)=1'])
        split_cond = parser.parse_expr("norm(w)!=0", fixes=fixes)
        proof = goal02.proof_by_case(split_cond=split_cond)
        case1 = proof.cases[0].proof_by_calculation()
        calc = case1.lhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hmf'), '0'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hmf'), '1'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hm'), '0'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hm'), '1'))
        calc.perform_rule(rules.FullSimplify())
        # print(case1)
        case2 = proof.cases[1].proof_by_calculation()
        calc = case2.lhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hmf'), '0'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hmf'), '1'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hm'), '0'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hm'), '1'))
        calc.perform_rule(rules.FullSimplify())
        # print(case2)
        # self.checkAndOutput(file, omit_finish=True)

    def testMy(self):

        ctx = Context()
        ctx.add_condition("x > 0")
        ctx.add_condition("x < pi/2")
        e = parser.parse_expr("cos(x) != 0")
        p = ctx.check_condition(e)
        print(p)

if __name__ == "__main__":
    unittest.main()
