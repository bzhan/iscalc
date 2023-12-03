import json
import os
import sys
import unittest

from integral import rules, parser, compstate, matrix, expr
from integral.context import Context
from integral.poly import normalize

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
            self.assertEqual(normalize(res, ctx), c)

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
            ("m", "$int"),
            ("P", "$tensor($real, m, m)"),
            ("A", "$tensor($real, m, m)")
        ]
        fixes = dict()
        for a, b in raw_fixes:
            fixes[a] = parser.parse_expr(b, fixes= fixes)
        goal = file.add_goal("(inv(P) * A * P) ^ n = inv(P) * (A ^ n) * P",
                             fixes=fixes,
                             conds=["invertible(P)", "n >= 0", "m>=1"])
        proof = goal.proof_by_induction(induct_var='n', start=0)
        _ = proof.base_case.proof_by_calculation()
        induct_proof = proof.induct_case.proof_by_calculation()
        calc = induct_proof.lhs_calc
        old_expr = calc.parse_expr("(inv(P) * A * P) ^ (n + 1)")
        new_expr = calc.parse_expr("(inv(P) * A * P) ^ n * (inv(P) * A * P)")
        calc.perform_rule(rules.ApplyIdentity(old_expr, new_expr))
        calc.perform_rule(rules.OnSubterm(rules.ApplyInductHyp()))
        calc.perform_rule(rules.FullSimplify())
        assert goal.is_finished()
        fixes = dict()
        fixes['A'] = parser.parse_expr("$tensor($real, 3, 3)")
        fixes['B'] = parser.parse_expr("$tensor($real, 3, 3)")
        goal_str = "(inv(B)*A*B)^4"
        goal_expr = parser.parse_expr(goal_str, fixes = fixes)
        conds_str = ["invertible(B)"]
        conds_expr = [parser.parse_expr(s, fixes = fixes) for s in conds_str]
        calc1 = file.add_calculation(calc=goal_expr, conds=conds_expr, fixes=fixes)
        calc1.perform_rule(rules.ApplyEquation(goal.goal, None))
        res = calc1.parse_expr("inv(B)*A^4*B")
        self.assertEqual(calc1.last_expr, res)
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
        calc.perform_rule(rules.ApplyEquation(eq, source, calc.get_fixes()))
        # cond in self context
        eq = calc.parse_expr("norm(w) = 1")
        source = calc.parse_expr("norm(w)")
        calc.perform_rule(rules.ApplyEquation(eq, source, calc.get_fixes()))
        calc.perform_rule(rules.ExpandPolynomial())
        old_e = calc.parse_expr("(-1) ^  n *  w * T(w) * hat(w)")
        new_e = calc.parse_expr("(-1) ^  n * (w * T(w) * hat(w))")
        calc.perform_rule(rules.Equation(old_e, new_e))
        source = calc.parse_expr("w * T(w) * hat(w)")
        calc.perform_rule(rules.ApplyEquation(goal02.goal, source, calc.get_fixes()))
        calc.perform_rule(rules.FullSimplify())
        calc = induct_proof.rhs_calc
        assert goal03.is_finished()

        goal04 = file.add_goal("hat(w) ^ (2 * (n + 1)) = (-1) ^ n * hat(w) ^ 2", conds=["n>=0", "norm(w)=1"], fixes=fixes)
        proof = goal04.proof_by_induction('n', 0)
        _ = proof.base_case.proof_by_calculation()
        induct_proof = proof.induct_case.proof_by_calculation()
        calc = induct_proof.lhs_calc
        new_expr = calc.parse_expr("hat(w) ^ 2 * hat(w) ^ (2 * (n + 1))")
        calc.perform_rule(rules.Equation(None, new_expr))
        calc.perform_rule(rules.OnSubterm(rules.ApplyInductHyp()))
        eq = calc.parse_expr("hat(w)^2 = w * T(w) - norm(w)^2 * unit_matrix(3)")
        source = calc.parse_expr("hat(w) ^ 2")
        calc.perform_rule(rules.ApplyEquation(goal01.goal, source, calc.get_fixes()))
        eq = calc.parse_expr("norm(w) = 1")
        source = calc.parse_expr("norm(w)")
        calc.perform_rule(rules.ApplyEquation(eq, source, calc.get_fixes()))
        calc.perform_rule(rules.ExpandPolynomial())
        old_e = calc.parse_expr("(-1) ^ n *  w * T(w) * hat(w) ^ 2")
        new_e = calc.parse_expr("(-1) ^ n * (w * T(w) * hat(w)) * hat(w)")
        calc.perform_rule(rules.Equation(old_e, new_e))
        source = calc.parse_expr("w * T(w) * hat(w)")
        calc.perform_rule(rules.ApplyEquation(goal02.goal, source, calc.get_fixes()))
        calc.perform_rule(rules.FullSimplify())
        calc = induct_proof.rhs_calc
        old_e = calc.parse_expr("hat(w) ^ 2")
        new_e = calc.parse_expr("hat(w) * hat(w)")
        calc.perform_rule(rules.Equation(old_e, new_e))
        calc.perform_rule(rules.FullSimplify())
        assert goal04.is_finished()
        self.checkAndOutput(file)

    def testExample05Input(self):
        dirname = os.path.dirname(__file__)
        file_path = os.path.join(dirname, "../examples/matrix_example02.json")
        with open(file_path, 'r', encoding='utf-8') as f:
            f_data = json.load(f)
        book_name = "matrix"
        file_name = 'matrix_example02'
        file = compstate.CompFile(book_name, file_name)

        for idx, item in enumerate(f_data['content']):
            st = compstate.parse_item(file, item)
            file.add_item(st)
        # print(file)

    def testExample06(self):
        file = compstate.CompFile("base", "matrix_example06")
        fixes = dict()
        fixes['n'] = parser.parse_expr('$int')
        goal01 = file.add_goal('1 - cos(a) = SUM(n, 0, oo, (-1) ^ n * a ^ (2 * (n + 1)) / factorial(2 * (n + 1)))', fixes=fixes)
        proof = goal01.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.SeriesExpansionIdentity(old_expr="cos(a)"))
        s = parser.parse_expr("n = 0", fixes=fixes)
        calc.perform_rule(rules.OnLocation(rules.SplitItem(s), "1"))
        calc.perform_rule(rules.FullSimplify())
        s1 = calc.parse_expr("-SUM(i, 1, oo, a ^ (2 * i) * (-1) ^ i / factorial(2 * i))")
        s2 = calc.parse_expr("SUM(i, 1, oo, (-1) * ((-1) ^ i * a ^ (2 * i) / factorial(2 * i)))")
        calc.perform_rule(rules.Equation(s1, s2))
        calc.perform_rule(rules.ChangeSummationIndex(new_lower='0'))
        calc.perform_rule(rules.FullSimplify())
        s3 = calc.parse_expr("a ^ (2 * i + 2) * (-1) ^ i / factorial(2 * i + 2)", fixes=fixes)
        s4 = calc.parse_expr("(-1) ^ i * a ^ (2 * (i+ 1)) / factorial(2 * (i + 1))", fixes=fixes)
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
        calc.perform_rule(rules.SplitItem(cond))
        cond = calc.parse_expr("i = 0")
        calc.perform_rule(rules.OnLocation(rules.SplitItem(cond), "1"))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.ChangeSummationIndex(new_lower="0"), "0.1"))
        s1 = calc.parse_expr("(x * hat(w)) ^ (2 * i + 1)")
        s2 = calc.parse_expr("x ^ (2 * i + 1) * hat(w) ^ (2 * i + 1)")
        calc.perform_rule(rules.ApplyIdentity(s1, s2))
        s3 = calc.parse_expr("(x * hat(w)) ^ (2 * (n + 1))")
        s4 = calc.parse_expr("x ^ (2 * (n + 1)) * hat(w) ^ (2 * (n + 1))")
        calc.perform_rule(rules.ApplyIdentity(s3, s4))
        s5 = calc.parse_expr("hat(w) ^ (2 * n + 1) = (-1) ^ n * hat(w)")
        source = calc.parse_expr("hat(w) ^ (2 * i + 1)")
        calc.perform_rule(rules.ApplyEquation(s5, source))
        s6 = calc.parse_expr("hat(w) ^ (2 * (n + 1)) = (-1) ^ n * hat(w) ^ 2")
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
        fixes['R'] = parser.parse_expr('$tensor($real, 3, 3)')
        fixes['p'] = parser.parse_expr('$tensor($real, 3, 1)')
        fixes['hm'] = parser.parse_expr("$fun($tensor($real, 3, 3), $tensor($real,3, 1), $tensor($real,4,4))")
        file.add_definition("hm(R, p) = rcon(ccon(R,p), ccon(zero_matrix(1,3),unit_matrix(1)))", fixes=fixes)
        fixes = dict()
        fixes['t'] = parser.parse_expr('$real')
        fixes['w'] = parser.parse_expr("$tensor($real, 3, 1)")
        fixes['v'] = parser.parse_expr("$tensor($real, 3, 1)")
        fixes['hm'] = parser.parse_expr("$fun($tensor($real, 3, 3), $tensor($real,3, 1), $tensor($real,4,4))")
        fixes['hmf'] = parser.parse_expr("$fun($real, $tensor($real, 3, 1), $tensor($real,3,1), $tensor($real, 4, 4))")
        file.add_definition("hmf(t, w, v) = hm(unit_matrix(3), t*v)",
                            conds=['norm(w)=0'], fixes=fixes)
        fixes = dict()
        fixes['t'] = parser.parse_expr('$real')
        fixes['w'] = parser.parse_expr("$tensor($real, 3, 1)")
        fixes['v'] = parser.parse_expr("$tensor($real, 3, 1)")
        fixes['hm'] = parser.parse_expr("$fun($tensor($real, 3, 3), $tensor($real,3, 1), $tensor($real,4,4))")
        fixes['hmf'] = parser.parse_expr("$fun($real, $tensor($real, 3, 1), $tensor($real,3,1), $tensor($real, 4, 4))")
        file.add_definition("hmf(t, w, v) = hm(exp(t*hat(w)), (unit_matrix(3)-exp(t*hat(w)))*(hat(w)*v)+(w*T(w)*v*t))",
                            conds=['norm(w)!=0'], fixes=fixes)
        goal01 = file.add_goal("exp(t * hat(w)) * exp(-(t * hat(w))) = unit_matrix(3)", fixes=fixes, conds=["norm(w)=1"])
        proof = goal01.proof_by_calculation()
        calc = proof.lhs_calc
        lemma = calc.parse_expr("exp(t * hat(w)) = unit_matrix(3) + sin(t) * hat(w) + (1 - cos(t)) * (hat(w)) ^ 2")
        source = calc.parse_expr("exp(t * hat(w))")
        calc.perform_rule(rules.ApplyEquation(lemma, source))
        s1 = calc.parse_expr("-(t * hat(w))")
        s2 = calc.parse_expr("-t * hat(w)")
        calc.perform_rule(rules.Equation(s1, s2))
        source = calc.parse_expr("exp(-t * hat(w))")
        calc.perform_rule(rules.ApplyEquation(lemma, source))
        calc.perform_rule(rules.ExpandPolynomial())
        calc.perform_rule(rules.FullSimplify())
        s1 = calc.parse_expr("hat(w) ^ 4")
        s2 = calc.parse_expr("hat(w) ^ (2*(1+1))")
        calc.perform_rule(rules.Equation(s1, s2))
        fixes = dict()
        fixes['w'] = parser.parse_expr("$tensor($real, 3, 1)")
        fixes['n'] = expr.IntType
        lemma = calc.parse_expr("hat(w) ^ (2 * (n + 1)) = (-1) ^ n * hat(w) ^ 2", fixes=fixes)
        source = calc.parse_expr("hat(w) ^ (2*(1+1))")
        calc.perform_rule(rules.ApplyEquation(lemma, source))
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
        assert goal01.is_finished()
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
        fixes = dict()
        fixes['w'] = parser.parse_expr("$tensor($real, 3, 1)")
        fixes['n'] = expr.IntType
        fixes['t'] = expr.RealType
        lemma = calc.parse_expr("exp(t * hat(w)) = unit_matrix(3) + sin(t) * hat(w) + (1 - cos(t)) * (hat(w)) ^ 2", fixes=fixes)
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
        fixes['hmf'] = parser.parse_expr("$fun($real, $tensor($real, 3, 1), $tensor($real,3,1), $tensor($real, 4, 4))")
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
        assert goal04.is_finished()
        fixes = dict()
        fixes['w'] = parser.parse_expr('$tensor($real, 3, 1)')
        fixes['v'] = parser.parse_expr('$tensor($real, 3, 1)')
        fixes['hmf'] = parser.parse_expr("$fun($real, $tensor($real, 3, 1), $tensor($real,3,1), $tensor($real, 4, 4))")
        goal05 = file.add_goal("hmf(t, w, v) * hmf(-t, w, v) = unit_matrix(4)", fixes=fixes,
                               conds=['norm(w)=0'])
        proof = goal05.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hmf'), '0'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hmf'), '1'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hm'), '0'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('hm'), '1'))
        calc.perform_rule(rules.FullSimplify())
        assert goal05.is_finished()
        self.checkAndOutput(file)


    def testHMFDerive(self):
        file = compstate.CompFile("MIRM", "twist_derive_hmf")
        fixes = dict()
        fixes['w'] = parser.parse_expr("$tensor($real, 3, 1)")
        fixes['v'] = parser.parse_expr("$tensor($real, 3, 1)")
        fixes['twist'] = parser.parse_expr("$fun($tensor($real, 3, 1), $tensor($real, 3, 1), $tensor($real, 6, 1))")
        file.add_definition("twist(w, v) = hat(rcon(w, v))", fixes = fixes)
        fixes = dict()
        fixes['w'] = parser.parse_expr("$tensor($real, 3, 1)")
        fixes['v'] = parser.parse_expr("$tensor($real, 3, 1)")
        fixes['hmf'] = parser.parse_expr("$fun($real, $tensor($real, 3, 1), $tensor($real, 3, 1), $tensor($real, 4, 4))")
        fixes['twist'] = parser.parse_expr("$fun($tensor($real, 3, 1), $tensor($real, 3, 1), $tensor($real, 6, 1))")
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
        fixes['t'] = parser.parse_expr("$real")
        fixes['w'] = parser.parse_expr("$tensor($real, 3, 1)")
        lemma = file.add_goal("(D t. exp(t * hat(w))) = hat(w)*exp(t*hat(w))",
                             conds=["norm(w)=1"], fixes=fixes)
        proof = lemma.proof_by_calculation()
        calc = proof.lhs_calc
        eq = calc.parse_expr("exp(t * hat(w)) = unit_matrix(3) + sin(t) * hat(w) + (1 - cos(t)) * (hat(w)) ^ 2")
        source = calc.parse_expr("exp(t * hat(w))")
        calc.perform_rule(rules.ApplyEquation(eq, source))
        calc.perform_rule(rules.FullSimplify())
        calc = proof.rhs_calc
        eq = calc.parse_expr("exp(t * hat(w)) = unit_matrix(3) + sin(t) * hat(w) + (1 - cos(t)) * (hat(w)) ^ 2")
        source = calc.parse_expr("exp(t * hat(w))")
        calc.perform_rule(rules.ApplyEquation(eq, source))
        calc.perform_rule(rules.ExpandPolynomial())
        s = calc.parse_expr("hat(w) ^ 3")
        t = calc.parse_expr("hat(w) ^ (2*1 + 1)")
        calc.perform_rule(rules.Equation(s, t))
        tmp = dict()
        tmp['n'] = parser.parse_expr("$int")
        eq = calc.parse_expr("hat(w)^(2*n+1) = (-1)^n * hat(w)", fixes=tmp)
        source = calc.parse_expr("hat(w) ^ (2 * 1 + 1)")
        calc.perform_rule(rules.ApplyEquation(eq, source))
        calc.perform_rule(rules.OnLocation(rules.ExpandPolynomial(), '0.0'))
        calc.perform_rule(rules.FullSimplify())
        assert lemma.is_finished()
        fixes = dict()
        fixes['w'] = parser.parse_expr("$tensor($real, 3, 1)")
        fixes['v'] = parser.parse_expr("$tensor($real, 3, 1)")
        fixes['hmf'] = parser.parse_expr(
            "$fun($real, $tensor($real, 3, 1), $tensor($real, 3, 1), $tensor($real, 4, 4))")
        fixes['twist'] = parser.parse_expr("$fun($tensor($real, 3, 1), $tensor($real, 3, 1), $tensor($real, 6, 1))")
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
        calc.perform_rule(rules.OnSubterm(rules.ExpandPolynomial()))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnSubterm(rules.ExpandPolynomial()))

        eq = calc.parse_expr("hat(w)^2 =  w * T(w) - norm(w)^2 * unit_matrix(3)")
        source = calc.parse_expr("hat(w)^2")
        calc.perform_rule(rules.ApplyEquation(eq, source))
        eq = calc.parse_expr("norm(w) = 1")
        source = calc.parse_expr("norm(w)")
        calc.perform_rule(rules.ApplyEquation(eq, source))
        calc.perform_rule(rules.OnSubterm(rules.ExpandPolynomial()))
        calc.perform_rule(rules.FullSimplify())
        s = calc.parse_expr("t * hat(w) * w * T(w) * v")
        t = calc.parse_expr("t * (hat(w) * w) * T(w) * v")
        calc.perform_rule(rules.Equation(s, t))
        eq = calc.parse_expr("hat(w) * w = zero_matrix(3,1)")
        source = calc.parse_expr("hat(w) * w")
        calc.perform_rule(rules.ApplyEquation(eq, source))
        calc.perform_rule(rules.FullSimplify())
        assert goal02.is_finished()
        self.checkAndOutput(file)

    def testMatrixPoeInv(self):
        file = compstate.CompFile("MIRM", "matrix_poe_inv")
        # ic: initial configuration
        d = "gst(t, n, w, v, ic) = MUL(i, 0, n-1, hmf(nth(t, i, 0), nthc(w, i), nthc(v, i))) * ic"
        conds = ['n>=1']
        fixes = dict()
        fixes['n'] = parser.parse_expr("$int")
        fixes['t'] = parser.parse_expr("$tensor($real, n, 1)", fixes=fixes)
        fixes['w'] = parser.parse_expr("$tensor($real, 3, n)", fixes=fixes)
        fixes['v'] = parser.parse_expr("$tensor($real, 3, n)", fixes=fixes)
        fixes['ic'] = parser.parse_expr("$tensor($real, 4, 4)")
        fixes['hmf'] = parser.parse_expr(
            "$fun($real, $tensor($real, 3, 1), $tensor($real, 3, 1), $tensor($real, 4, 4))", fixes=fixes)

        s = "$fun($tensor($real, n, 1),$int, $tensor($real, 3, n),$tensor($real, 3, n),$tensor($real, 4, 4)," \
            "$tensor($real, 4, 4)) "
        fixes['gst'] = parser.parse_expr(s, fixes=fixes)
        file.add_definition(d, conds=conds, fixes=fixes)
        fixes = dict()
        fixes['n'] = parser.parse_expr('$int')
        fixes['t'] = parser.parse_expr("$tensor($real, n, 1)", fixes=fixes)
        fixes['w'] = parser.parse_expr("$tensor($real, 3, n)", fixes=fixes)
        fixes['v'] = parser.parse_expr("$tensor($real, 3, n)", fixes=fixes)
        fixes['ic'] = parser.parse_expr("$tensor($real, 4, 4)", fixes=fixes)
        fixes['hmf'] = parser.parse_expr(
            "$fun($real, $tensor($real, 3, 1), $tensor($real, 3, 1), $tensor($real, 4, 4))", fixes=fixes)
        s = "$fun($tensor($real, n, 1),$int, $tensor($real, 3, n),$tensor($real, 3, n),$tensor($real, 4, 4)," \
            "$tensor($real, 4, 4)) "
        fixes['gst'] = parser.parse_expr(s, fixes=fixes)
        g = "(inv(ic) * MUL(i, 0, n-1, hmf(-nth(t, n-i-1, 0), nthc(w, n-i-1), nthc(v, n-i-1))))*\
                gst(t, n, w, v, ic) = unit_matrix(4)"
        conds = ["n>=1"]  # "isColumnOrthogonalMatrix(w)"
        goal01 = file.add_goal(g, fixes=fixes, conds=conds)
        cases = goal01.proof_by_induction(induct_var='n', start=1)
        proof = cases.base_case.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('gst'), '1'))
        s = calc.parse_expr(
            "inv(ic) * hmf(-nth(t,0,0),nthc(w,0),nthc(v,0)) * (hmf(nth(t,0,0),nthc(w,0),nthc(v,0)) * ic) ")
        t = calc.parse_expr(
            "inv(ic) * (hmf(-nth(t,0,0),nthc(w,0),nthc(v,0)) * hmf(nth(t,0,0),nthc(w,0),nthc(v,0))) * ic")
        calc.perform_rule(rules.Equation(s, t))
        eq = calc.parse_expr("hmf(-t, w, v) * hmf(t, w, v) = unit_matrix(4)", fixes={'t': expr.RealType})
        s = calc.parse_expr("hmf(-nth(t,0,0),nthc(w,0),nthc(v,0)) * hmf(nth(t,0,0),nthc(w,0),nthc(v,0))")
        calc.perform_rule(rules.ApplyEquation(eq, s))
        calc.perform_rule(rules.FullSimplify())

        proof = cases.induct_case.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('gst'), '1'))
        cond = calc.parse_expr("i=n")
        calc.perform_rule(rules.OnLocation(rules.SplitItem(cond), '0.1'))
        cond = calc.parse_expr("i=0")
        calc.perform_rule(rules.OnLocation(rules.SplitItem(cond), '1.0'))
        calc.perform_rule(rules.FullSimplify())
        s = calc.parse_expr(
            "inv(ic) * MUL(j, 0, n - 1, hmf(-nth(t,-j + n,0),nthc(w,-j + n),nthc(v,-j + n))) * hmf(-nth(t,0,0),nthc(w,0),nthc(v,0)) * hmf(nth(t,0,0),nthc(w,0),nthc(v,0)) * MUL(j, 1, n, hmf(nth(t,j,0),nthc(w,j),nthc(v,j))) * ic")
        t = calc.parse_expr(
            "inv(ic) * MUL(j, 0, n - 1, hmf(-nth(t,-j + n,0),nthc(w,-j + n),nthc(v,-j + n))) * (hmf(-nth(t,0,0),nthc(w,0),nthc(v,0)) * hmf(nth(t,0,0),nthc(w,0),nthc(v,0))) * MUL(j, 1, n, hmf(nth(t,j,0),nthc(w,j),nthc(v,j))) * ic")
        calc.perform_rule(rules.Equation(s, t))
        fixes = dict()
        fixes['t'] = expr.RealType
        fixes['w'] = parser.parse_expr("$tensor($real, 3, 1)")
        fixes['v'] = parser.parse_expr("$tensor($real, 3, 1)")
        eq = calc.parse_expr("hmf(-t, w, v) * hmf(t, w, v) = unit_matrix(4)", fixes=fixes)
        s = calc.parse_expr("hmf(-nth(t,0,0),nthc(w,0),nthc(v,0)) * hmf(nth(t,0,0),nthc(w,0),nthc(v,0))")
        calc.perform_rule(rules.ApplyEquation(eq, s))

        calc.perform_rule(rules.FullSimplify())
        s = calc.parse_expr("MUL(j, 0, n - 1, hmf(-nth(t,-j + n, 0),nthc(w,-j + n),nthc(v,-j + n)))")
        t = calc.parse_expr(
            "MUL(j, 0, n-1, hmf(-nth(choose_row(t, 1, n),n-j-1, 0), nthc(choose_col(w,1,n), n-j-1), nthc(choose_col(v, 1, n), n-j-1)))")
        calc.perform_rule(rules.RewriteMatrixMul(s, t))
        s = calc.parse_expr("MUL(j, 1, n, hmf(nth(t,j,0),nthc(w,j),nthc(v,j)))")
        # choose_row: choose row from 1 to n of t to make a new matrix
        t = calc.parse_expr(
            "MUL(j, 0, n-1, hmf(nth(choose_row(t, 1, n),j, 0), nthc(choose_col(w,1, n), j), nthc(choose_col(v, 1, n), j)))")
        calc.perform_rule(rules.RewriteMatrixMul(s, t))
        s = calc.parse_expr(
            "inv(ic) * MUL(j, 0, n - 1, hmf(-nth(choose_row(t,1,n),n - j - 1,0),nthc(choose_col(w,1,n),n - j - 1),nthc(choose_col(v,1,n),n - j - 1))) * MUL(j, 0, n - 1, hmf(nth(choose_row(t,1,n),j,0),nthc(choose_col(w,1,n),j),nthc(choose_col(v,1,n),j))) * ic")
        t = calc.parse_expr(
            "inv(ic) * MUL(j, 0, n - 1, hmf(-nth(choose_row(t,1,n),n - j - 1,0),nthc(choose_col(w,1,n),n - j - 1),nthc(choose_col(v,1,n),n - j - 1))) * (MUL(j, 0, n - 1, hmf(nth(choose_row(t,1,n),j,0),nthc(choose_col(w,1,n),j),nthc(choose_col(v,1,n),j))) * ic)")
        calc.perform_rule(rules.Equation(s, t))
        calc.perform_rule(rules.OnLocation(rules.FoldDefinition('gst'), '1'))
        calc.perform_rule(rules.ApplyInductHyp())
        assert goal01.is_finished()
        self.checkAndOutput(file)

if __name__ == "__main__":
    unittest.main()
