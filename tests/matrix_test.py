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
        source = calc.parse_expr("hat(w)^2")
        calc.perform_rule(rules.ApplyEquation(eq, source))
        # cond in self context
        eq = calc.parse_expr("norm(w) = 1")
        source = calc.parse_expr("norm(w)")
        calc.perform_rule(rules.ApplyEquation(eq, source))
        calc.perform_rule(rules.ExpandPolynomial())
        old_e = calc.parse_expr("(-1) ^  n *  w * T(w) * hat(w)")
        new_e = calc.parse_expr("(-1) ^  n * (w * T(w) * hat(w))")
        calc.perform_rule(rules.Equation(old_e, new_e))
        source = calc.parse_expr("w * T(w) * hat(w)")
        calc.perform_rule(rules.ApplyEquation(goal02.goal, source))
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
        source = calc.parse_expr("hat(w) ^ 2")
        calc.perform_rule(rules.ApplyEquation(goal01.goal, source))
        eq = calc.parse_expr("norm(w) = 1")
        source = calc.parse_expr("norm(w)")
        calc.perform_rule(rules.ApplyEquation(eq, source))
        calc.perform_rule(rules.ExpandPolynomial())
        old_e = calc.parse_expr("(-1) ^ n *  w * T(w) * hat(w)")
        new_e = calc.parse_expr("(-1) ^ n * (w * T(w) * hat(w))")
        calc.perform_rule(rules.Equation(old_e, new_e))
        source = calc.parse_expr("w * T(w) * hat(w)")
        calc.perform_rule(rules.ApplyEquation(goal02.goal, source))
        calc.perform_rule(rules.FullSimplify())
        calc = induct_proof.rhs_calc
        old_e = calc.parse_expr("hat(w) ^ 2")
        new_e = calc.parse_expr("hat(w) * hat(w)")
        calc.perform_rule(rules.Equation(old_e, new_e))
        calc.perform_rule(rules.FullSimplify())
        assert goal04.is_finished()
        self.checkAndOutput(file)


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
        s5 = parser.parse_expr("hat(w) ^ (2 * n + 1) = (-1) ^ n * hat(w)")
        source = calc.parse_expr("hat(w) ^ (2 * i + 1)")
        calc.perform_rule(rules.ApplyEquation(s5, source))
        s6 = parser.parse_expr("hat(w) ^ (2 * (n + 1)) = (-1) ^ n * hat(w) ^ 2")
        source = calc.parse_expr("hat(w) ^ (2 * (n + 1))")
        calc.perform_rule(rules.ApplyEquation(s6, source))

        s7 = calc.parse_expr("SUM(n, 0, oo, x ^ (2 * n + 1) * ((-1) ^ n * hat(w)) / factorial(2 * n + 1))")
        s8 = calc.parse_expr("hat(w) * SUM(n, 0, oo, (-1) ^ n * x ^ (2 * n + 1) / factorial(2 * n + 1))")
        calc.perform_rule(rules.Equation(s7, s8))
        calc.perform_rule(rules.OnLocation(rules.SeriesEvaluationIdentity(), "0.0.1"))
        s = calc.parse_expr("SUM(n, 0, oo, x ^ (2 * (n + 1)) * ((-1) ^ n * hat(w) ^ 2) / factorial(2 * (n + 1)))")
        t = calc.parse_expr("hat(w) ^ 2 * SUM(n, 0, oo, (-1) ^ n * x ^ (2 * (n + 1)) / factorial(2 * (n + 1)))")
        calc.perform_rule(rules.Equation(s, t))
        eq = parser.parse_expr("1 - cos(a) = SUM(n, 0, oo, (-1) ^ n * a ^ (2 * (n + 1)) / factorial(2 * (n + 1)))")
        source = calc.parse_expr("SUM(n, 0, oo, (-1) ^ n * x ^ (2 * (n + 1)) / factorial(2 * (n + 1)))")
        calc.perform_rule(rules.ApplyEquation(eq, source))
        calc.perform_rule(rules.FullSimplify())
        calc = proof.rhs_calc
        calc.perform_rule(rules.FullSimplify())
        assert goal01.is_finished()
        self.checkAndOutput(file)


    def testTwistMatrixExpInv(self):
        file = compstate.CompFile("MIRM", "twist_matrix_exp_inv")
        fixes = dict()
        fixes['w'] = parser.parse_expr('$tensor($real, 3, 1)')
        file.add_definition("hm(R, p) = rcon(ccon(R,p), ccon(zero_matrix(1,3),unit_matrix(1)))",
                            conds=['type(R, 0, 3, 3)', 'type(p, 0 ,3)'])
        file.add_definition("hmf(t, w, v) = hm(unit_matrix(3), t*v)",
                            conds=['type(w, 0 ,3)', 'type(v, 0 ,3)', 'norm(w)=0'])
        file.add_definition("hmf(t, w, v) = hm(exp(t*hat(w)), (unit_matrix(3)-exp(t*hat(w)))*(hat(w)*v)+(w*T(w)*v*t))",
                            conds=['type(w, 0, 3)', 'type(v, 0, 3)', 'norm(w)=1'])
        goal01 = file.add_goal("exp(t * hat(w)) * exp(-(t * hat(w))) = unit_matrix(3)", fixes=fixes, conds=["norm(w)=1"])
        proof = goal01.proof_by_calculation()
        calc = proof.lhs_calc
        lemma = parser.parse_expr("exp(t * hat(w)) = unit_matrix(3) + sin(t) * hat(w) + (1 - cos(t)) * (hat(w)) ^ 2")
        source = calc.parse_expr("exp(t * hat(w))")
        calc.perform_rule(rules.ApplyEquation(lemma, source))
        s1 = calc.parse_expr("-(t * hat(w))")
        s2 = calc.parse_expr("-t * hat(w)")
        calc.perform_rule(rules.Equation(s1, s2))
        source = calc.parse_expr("exp(-t * hat(w))")
        calc.perform_rule(rules.ApplyEquation(lemma, source))
        calc.perform_rule(rules.ExpandPolynomial())
        calc.perform_rule(rules.FullSimplify())
        s1 = calc.parse_expr("sin(t) * (-cos(t) + 1) * hat(w) * hat(w) ^ 2")
        s2 = calc.parse_expr("sin(t) * (-cos(t) + 1) * (hat(w)^3)")
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = calc.parse_expr("sin(t) * (-cos(t) + 1) * hat(w)^2 * hat(w)")
        s2 = calc.parse_expr("sin(t) * (-cos(t) + 1) * (hat(w)^3)")
        calc.perform_rule(rules.Equation(s1, s2))
        calc.perform_rule(rules.FullSimplify())
        s1 = calc.parse_expr("(-cos(t) + 1) ^ 2 * hat(w) ^ 2 * hat(w) ^ 2")
        s2 = calc.parse_expr("(-cos(t) + 1) ^ 2 * (hat(w) ^ 2 * hat(w) ^ 2)")
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = calc.parse_expr("hat(w) ^ 2 * hat(w) ^ 2")
        s2 = calc.parse_expr("hat(w) ^ (2*(1+1))")
        calc.perform_rule(rules.ApplyIdentity(s1, s2))
        lemma = parser.parse_expr("hat(w) ^ (2 * (n + 1)) = (-1) ^ n * hat(w) ^ 2")
        source = calc.parse_expr("hat(w) ^ (2*(1+1))")
        calc.perform_rule(rules.ApplyEquation(lemma, source))
        s1 = calc.parse_expr("sin(t) ^ 2 * hat(w) * hat(w)")
        s2 = calc.parse_expr("sin(t) ^ 2 * hat(w)^2")
        calc.perform_rule(rules.Equation(s1, s2))
        calc.perform_rule(rules.FullSimplify())
        s1 = calc.parse_expr("-((-cos(t) + 1) ^ 2 * hat(w) ^ 2)")
        s2 = calc.parse_expr("(-cos(t)^2 - 1 + 2* cos(t)) * hat(w) ^ 2")
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = calc.parse_expr("(-cos(t)^2 - 1 + 2 * cos(t)) * hat(w) ^ 2 + (-(2 * cos(t)) + 2) * hat(w) ^ 2")
        s2 = calc.parse_expr("(-cos(t)^2 + 1) * hat(w) ^ 2 ")
        calc.perform_rule(rules.ApplyIdentity(s1, s2))
        s1 = calc.parse_expr("(-(cos(t) ^ 2) + 1) * hat(w) ^ 2 - sin(t) ^ 2 * hat(w) ^ 2")
        s2 = calc.parse_expr("(-(sin(t)^2 + cos(t)^2) + 1) * hat(w) ^ 2 ")
        calc.perform_rule(rules.ApplyIdentity(s1, s2))
        s1 = calc.parse_expr("(sin(t)^2 + cos(t)^2)")
        s2 = calc.parse_expr("1")
        calc.perform_rule(rules.ApplyIdentity(s1, s2))
        calc.perform_rule(rules.FullSimplify())

        fixes = dict()
        fixes['w'] = parser.parse_expr('$tensor($real, 3, 1)')
        fixes['n'] = parser.parse_expr("$int")
        goal02 = file.add_goal("hat(w) ^ n * w = zero_matrix(3,1)", fixes = fixes, conds=["n>=1"])
        proof = goal02.proof_by_induction('n', start=1)
        base_proof = proof.base_case.proof_by_calculation()
        calc = base_proof.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandMatFunc()))
        calc.perform_rule(rules.FullSimplify())
        calc = base_proof.rhs_calc
        calc.perform_rule(rules.ExpandMatFunc())
        induct_proof = proof.induct_case.proof_by_calculation()
        calc = induct_proof.lhs_calc
        s1 = calc.parse_expr("hat(w) ^ (n + 1)")
        s2 = calc.parse_expr("hat(w) * hat(w) ^ n")
        calc.perform_rule(rules.ApplyIdentity(s1,s2))
        s1 = calc.parse_expr("hat(w) * hat(w) ^ n * w")
        s2 = calc.parse_expr("hat(w) * (hat(w) ^ n * w)")
        calc.perform_rule(rules.Equation(s1, s2))
        calc.perform_rule(rules.OnLocation(rules.ApplyInductHyp(), '1'))
        calc.perform_rule(rules.FullSimplify())
        assert goal02.is_finished()
        fixes = dict()
        fixes['w'] = parser.parse_expr('$tensor($real, 3, 1)')
        goal03 = file.add_goal("exp(t * hat(w)) * w = w", fixes = fixes, conds=["norm(w) = 1"])
        proof = goal03.proof_by_calculation()
        calc = proof.lhs_calc
        lemma = parser.parse_expr("exp(t * hat(w)) = unit_matrix(3) + sin(t) * hat(w) + (1 - cos(t)) * (hat(w)) ^ 2")
        source = calc.parse_expr("exp(t * hat(w))")
        calc.perform_rule(rules.ApplyEquation(lemma, source))
        calc.perform_rule(rules.ExpandPolynomial())
        s1 = calc.parse_expr("sin(t) * hat(w) * w")
        s2 = calc.parse_expr("sin(t) * (hat(w)^1 * w)")
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = calc.parse_expr("(-cos(t) + 1) * hat(w) ^ 2 * w")
        s2 = calc.parse_expr("(-cos(t) + 1) * (hat(w) ^ 2 * w)")
        calc.perform_rule(rules.Equation(s1, s2))
        source = calc.parse_expr("hat(w) ^ 2 * w")
        calc.perform_rule(rules.ApplyEquation(goal02.goal, source))
        source = calc.parse_expr("hat(w) ^ 1 * w")
        calc.perform_rule(rules.ApplyEquation(goal02.goal, source))
        calc.perform_rule(rules.FullSimplify())
        assert goal03.is_finished()
        fixes = dict()
        fixes['w'] = parser.parse_expr('$tensor($real, 3, 1)')
        fixes['v'] = parser.parse_expr('$tensor($real, 3, 1)')
        goal04 = file.add_goal("hmf(t, w, v) * hmf(-t, w, v) = unit_matrix(4)", fixes=fixes,
                               conds=['norm(w)=1'])
        proof = goal04.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hmf'), '0'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hmf'), '1'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hm'), '0'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hm'), '1'))
        calc.perform_rule(rules.FullSimplify())
        source = calc.parse_expr("exp(t * hat(w)) * exp(-(t * hat(w)))")
        calc.perform_rule(rules.ApplyEquation(goal01.goal, source))
        calc.perform_rule(rules.OnSubterm(rules.ExpandPolynomial()))
        calc.perform_rule(rules.FullSimplify())
        source = calc.parse_expr("exp(t * hat(w)) * exp(-(t * hat(w)))")
        calc.perform_rule(rules.ApplyEquation(goal01.goal, source))
        calc.perform_rule(rules.FullSimplify())
        s1 = calc.parse_expr("t * exp(t * hat(w)) * w * T(w) * v")
        s2 = calc.parse_expr("t * (exp(t * hat(w)) * w) * T(w) * v")
        calc.perform_rule(rules.Equation(s1,s2))
        source = calc.parse_expr("exp(t * hat(w)) * w")
        calc.perform_rule(rules.ApplyEquation(goal03.goal, source))
        calc.perform_rule(rules.FullSimplify())
        fixes = dict()
        fixes['w'] = parser.parse_expr('$tensor($real, 3, 1)')
        fixes['v'] = parser.parse_expr('$tensor($real, 3, 1)')
        goal05 = file.add_goal("hmf(t, w, v) * hmf(-t, w, v) = unit_matrix(4)", fixes=fixes,
                               conds=['norm(w)=0'])
        proof = goal05.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hmf'), '0'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hmf'), '1'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hm'), '0'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hm'), '1'))
        calc.perform_rule(rules.FullSimplify())
        self.checkAndOutput(file)


    def testHMFDerive(self):
        file = compstate.CompFile("MIRM", "twist_derive_hmf")
        file.add_definition("twist(w, v) = hat(rcon(w, v))", conds=["type(w, 0, 3)", "type(v, 0, 3)"])
        fixes = dict()
        fixes['w'] = parser.parse_expr("$tensor($real, 3, 1)")
        fixes['v'] = parser.parse_expr("$tensor($real, 3, 1)")
        goal01 = file.add_goal("(D t. hmf(t, w, v)) = twist(w, v) * hmf(t, w, v)",
                      conds=["norm(w)=0"], fixes=fixes)
        proof = goal01.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition("hmf"), "0"))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition("hm"), "0"))
        calc.perform_rule(rules.FullSimplify())
        calc = proof.rhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition("twist"), "0"))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition("hmf"), "1"))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition("hm"), "1"))
        calc.perform_rule(rules.OnLocation(rules.ExpandMatFunc(), "0"))
        s = calc.parse_expr("w")
        t = calc.parse_expr("zero_matrix(3,1)")
        calc.perform_rule(rules.Equation(s, t))
        calc.perform_rule(rules.FullSimplify())
        assert goal01.is_finished()
        fixes = dict()
        fixes['w'] = parser.parse_expr("$tensor($real, 3, 1)")
        lemma = file.add_goal("(D t. exp(t * hat(w))) = hat(w)*exp(t*hat(w))",
                             conds=["norm(w)=1"], fixes=fixes)
        proof = lemma.proof_by_calculation()
        calc = proof.lhs_calc
        eq = parser.parse_expr("exp(t * hat(w)) = unit_matrix(3) + sin(t) * hat(w) + (1 - cos(t)) * (hat(w)) ^ 2")
        source = calc.parse_expr("exp(t * hat(w))")
        calc.perform_rule(rules.ApplyEquation(eq, source))
        calc.perform_rule(rules.FullSimplify())
        calc = proof.rhs_calc
        eq = parser.parse_expr("exp(t * hat(w)) = unit_matrix(3) + sin(t) * hat(w) + (1 - cos(t)) * (hat(w)) ^ 2")
        source = calc.parse_expr("exp(t * hat(w))")
        calc.perform_rule(rules.ApplyEquation(eq, source))
        calc.perform_rule(rules.ExpandPolynomial())
        s = calc.parse_expr("(-cos(t) + 1) * hat(w) * hat(w) ^ 2")
        t = calc.parse_expr("(-cos(t) + 1) * (hat(w) * hat(w) ^ 2)")
        calc.perform_rule(rules.Equation(s, t))
        s = calc.parse_expr("hat(w) * hat(w) ^ 2")
        t = calc.parse_expr("hat(w) ^ (2*1 + 1)")
        calc.perform_rule(rules.ApplyIdentity(s, t))
        eq = parser.parse_expr("hat(w)^(2*n+1) = (-1)^n * hat(w)")
        source = calc.parse_expr("hat(w) ^ (2 * 1 + 1)")
        calc.perform_rule(rules.ApplyEquation(eq, source))
        calc.perform_rule(rules.OnLocation(rules.ExpandPolynomial(), '0.0'))
        calc.perform_rule(rules.FullSimplify())
        s = calc.parse_expr("sin(t) * hat(w) * hat(w)")
        t = calc.parse_expr("sin(t) * (hat(w) * hat(w))")
        calc.perform_rule(rules.Equation(s, t))
        s = calc.parse_expr("hat(w) * hat(w)")
        t = calc.parse_expr("hat(w)^2")
        calc.perform_rule(rules.ApplyIdentity(s, t))
        assert lemma.is_finished()
        fixes = dict()
        fixes['w'] = parser.parse_expr("$tensor($real, 3, 1)")
        fixes['v'] = parser.parse_expr("$tensor($real, 3, 1)")
        goal02 = file.add_goal("(D t. hmf(t, w, v)) = twist(w, v) * hmf(t, w, v)",
                             conds=["norm(w)=1"], fixes=fixes)
        proof = goal02.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hmf'), '0'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hm'), '0'))
        calc.perform_rule(rules.FullSimplify())
        source = calc.parse_expr("D t. exp(t * hat(w))")
        calc.perform_rule(rules.ApplyEquation(lemma.goal, source))
        source = calc.parse_expr("D t. exp(t * hat(w))")
        calc.perform_rule(rules.ApplyEquation(lemma.goal, source))
        calc = proof.rhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition("twist"), '0'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition("hmf"), '1'))
        calc.perform_rule(rules.OnLocation(rules.ExpandMatFunc(),'0'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hm'),'1'))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.ExpandPolynomial(), '0.1.0'))
        calc.perform_rule(rules.OnLocation(rules.ExpandPolynomial(), '0.1.0.0.0'))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.ExpandPolynomial(), '0.1.0.0'))
        s = calc.parse_expr("hat(w) * hat(w)")
        t = calc.parse_expr("hat(w)^2")
        calc.perform_rule(rules.ApplyIdentity(s, t))
        eq = parser.parse_expr("hat(w)^2 =  w * T(w) - norm(w)^2 * unit_matrix(3)")
        source = calc.parse_expr("hat(w)^2")
        calc.perform_rule(rules.ApplyEquation(eq, source))
        eq = calc.parse_expr("norm(w) = 1")
        source = calc.parse_expr("norm(w)")
        calc.perform_rule(rules.ApplyEquation(eq, source))
        calc.perform_rule(rules.OnLocation(rules.ExpandPolynomial(), '0.1.0.0.1'))
        calc.perform_rule(rules.FullSimplify())
        s = calc.parse_expr("t * hat(w) * w * T(w) * v")
        t = calc.parse_expr("t * (hat(w) * w) * T(w) * v")
        calc.perform_rule(rules.Equation(s, t))
        eq = parser.parse_expr("hat(w) * w = zero_matrix(3,1)")
        source = calc.parse_expr("hat(w) * w")
        calc.perform_rule(rules.ApplyEquation(eq, source))
        calc.perform_rule(rules.FullSimplify())
        assert goal02.is_finished()
        self.checkAndOutput(file)

    def testFixes01(self):
        file = compstate.CompFile("base", "test_fixes_01")
        fixes = dict()
        fixes['x'] = parser.parse_expr('$real')
        fixes['y'] = parser.parse_expr('$real')
        goal = file.add_goal("(cos(y) + (sin(x)^2+cos(x)^2)) = " + \
                             "SUM(k, 0, oo, (-1)^k*y^(2*k) / factorial(2*k)) + 1",
                             fixes=fixes)
        proof = goal.proof_by_calculation()
        calc = proof.lhs_calc
        s1 = calc.parse_expr("sin(x)^2 + cos(x)^2")
        s2 = calc.parse_expr("1")
        calc.perform_rule(rules.ApplyIdentity(s1, s2))
        assert calc.ctx.get_fixes() == {'y': expr.RealType}
        assert calc.ctx.dead_vars == {'x': None}
        calc.perform_rule(rules.OnLocation(rules.SeriesExpansionIdentity(index_var='x'), '0'))
        assert calc.ctx.get_fixes() == {'y': expr.RealType, 'x': expr.IntType}
        assert calc.ctx.dead_vars == dict()
        assert goal.is_finished()

        self.checkAndOutput(file)

    def testFixes02(self):
        file = compstate.CompFile("base", "test_fixes_02")
        fixes = dict()
        fixes['x'] = parser.parse_expr('$real')
        goal = file.add_goal("1 / cos(x) = sec(x)",
                             fixes=fixes,
                             conds=["cos(x)!=0"])
        proof = goal.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnLocation(rules.SeriesExpansionIdentity(),'1'))
        assert file.get_item_label(goal) == compstate.Label("1")
        assert calc.ctx.get_fixes() == {'x': expr.RealType, 'n':expr.IntType}
        assert calc.ctx.dead_vars == dict()
        assert calc.ctx.fixes == {'n':expr.IntType}
        calc.perform_rule(rules.OnLocation(rules.SeriesEvaluationIdentity(),'1'))
        assert calc.ctx.fixes == dict()
        assert calc.ctx.dead_vars == dict()
        assert calc.ctx.get_fixes() == {'x': expr.RealType}
        calc.perform_rule(rules.ApplyIdentity("1/cos(x)", "sec(x)"))
        assert goal.is_finished()
        self.checkAndOutput(file)


    def testFixes03(self):
        file = compstate.CompFile("base", "test_fixes_03")
        fixes = dict()
        fixes['k'] = parser.parse_expr('$int')
        fixes['g'] = parser.parse_expr("$int")
        goal = file.add_goal("cos(x) = cos(x) + SUM(k, 0, 6, a) - SUM(g, 0, 6, a)",
                             fixes=fixes)
        proof = goal.proof_by_calculation()
        calc = proof.rhs_calc
        assert calc.ctx.fixes == dict()
        assert calc.ctx.dead_vars == dict()
        calc.perform_rule(rules.FullSimplify())
        assert calc.ctx.dead_vars == {'g':None, 'k':None}
        assert calc.ctx.fixes == dict()
        assert goal.is_finished()
        fixes = dict()
        fixes['x'] = expr.RealType
        fixes['n'] = expr.RealType
        goal02 = file.add_goal("SUM(n, 0, oo, (-1)^n*x^(2*n)/factorial(2*n))=cos(x)", fixes=fixes)
        proof = goal02.proof_by_rewrite_goal(begin=goal)
        calc = proof.begin
        calc.perform_rule(rules.FullSimplify())
        calc.ctx.fixes = dict()
        calc.ctx.dead_vars = {'g':None, 'k':None}
        calc.perform_rule(rules.OnLocation(rules.SeriesExpansionIdentity(), '0'))
        calc.ctx.fixes = {'n': expr.IntType}
        calc.ctx.dead_vars = {'g':None, 'k':None}
        self.checkAndOutput(file)

if __name__ == "__main__":
    unittest.main()
