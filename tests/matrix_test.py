import json
import os
import sys
import unittest
from typing import List

from integral import rules, context, parser, compstate, matrix
from integral.context import Context
from integral.expr import Op, Var, Const, Matrix, Expr, Fun

BASE_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.append(BASE_DIR)

class MatrixTest(unittest.TestCase):
    def checkAndOutput(self, file: compstate.CompFile, omit_finish: bool = False):
        # Test parsing of json file
        json_file = file.export()
        for i, item in enumerate(json_file['content']):
            self.assertEqual(compstate.parse_item(file.content[i].parent, item).export(), file.content[i].export(), "%d:%sasdfasdf%s"%(i, compstate.parse_item(file.content[i].parent, item).export(), file.content[i].export()))

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
            ("[a1,a2,a3]", "[[0,-a3,a2],[a3,0,-a1],[-a2,a1,0]]"),
            ("[v1,v2,v3,w1,w2,w3]",
             "[[0, -w3, w2, v1], [w3, 0, -w1, v2], [-w2, w1, 0, v3], [0,0,0,0]]")
        ]

        for a, b in test_data:
            a = parser.parse_expr(a)
            b = parser.parse_expr(b)
            self.assertEqual(matrix.hat(a), b)

    def testExample01(self):
        file = compstate.CompFile("MIRM", "matrix_example01")
        file.add_definition("matrix P[n][n]")
        file.add_definition("matrix A[n][n]")
        file.add_definition("int n")
        file.add_assumption("invertible(P)")
        file.add_assumption("n > 0")
        # find same name variable definition
        # and then use that definition
        goal = file.add_goal("(inv(P)*A*P)^n = inv(P)*A^n*P")
        proof = goal.proof_by_induction(induct_var='n', start=0)
        base_proof = proof.base_case.proof_by_calculation()
        induct_proof = proof.induct_case.proof_by_calculation()
        calc = base_proof.lhs_calc
        calc = base_proof.rhs_calc
        calc = induct_proof.lhs_calc
        old_expr = "(inv(matrix P[n][n]) * matrix A[n][n] * matrix P[n][n]) ^ (int n + 1)"
        new_expr = "(inv(matrix P[n][n]) * matrix A[n][n] * matrix P[n][n]) ^ (int n) * (inv(matrix P[n][n]) * matrix A[n][n] * matrix P[n][n])"
        calc.perform_rule(rules.ApplyIdentity(old_expr, new_expr))
        calc.perform_rule(rules.OnSubterm(rules.ApplyInductHyp()))
        calc.perform_rule(rules.FullSimplify())
        old_expr = "inv(matrix P[n][n]) * matrix A[n][n] ^ int n * matrix A[n][n] * matrix P[n][n]"
        new_expr = "inv(matrix P[n][n]) * (matrix A[n][n] ^ int n * matrix A[n][n]) * matrix P[n][n]"
        calc.perform_rule(rules.Equation(old_expr, new_expr))
        old_expr = "matrix A[n][n] ^ int n * matrix A[n][n]"
        new_expr = "matrix A[n][n] ^ (int n + 1)"
        calc.perform_rule(rules.ApplyIdentity(old_expr, new_expr))
        # print(file)
        self.checkAndOutput(file)

    def testExample02(self):
        file = compstate.CompFile("matrix", "matrix_example02")
        file.add_definition("matrix w[3][1] = {{a_1},{a_2},{a_3}}")
        goal01 = file.add_goal('hat(w)^2 = w * T(w) - norm(w)^2 * unit_matrix(3)')
        proof = goal01.proof_by_calculation()
        calc = proof.rhs_calc
        calc.perform_rule(rules.FullSimplify())
        calc = proof.lhs_calc
        old_expr = "hat(matrix w[3][1]) ^ 2"
        new_expr = "hat(matrix w[3][1]) ^ 1 * hat(matrix w[3][1]) ^ 1"
        calc.perform_rule(rules.ApplyIdentity(old_expr, new_expr))
        calc.perform_rule(rules.FullSimplify())

        goal02 = file.add_goal("w*T(w)*hat(w) = zero_matrix(3,3)")
        proof = goal02.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.FullSimplify())
        calc = proof.rhs_calc
        calc.perform_rule(rules.FullSimplify())

        file.add_definition("int n")
        file.add_assumption("n>=0")
        file.add_assumption("norm(w)=1")
        goal03 = file.add_goal("hat(w)^(2*n+1) = (-1)^n * hat(w)")
        proof = goal03.proof_by_induction('n', 0)
        base_proof = proof.base_case.proof_by_calculation()
        induct_proof = proof.induct_case.proof_by_calculation()
        calc = induct_proof.lhs_calc
        calc.perform_rule(rules.Equation("(2 * int n + 3)", "2 + (2 * int n + 1)"))
        calc.perform_rule(rules.ApplyIdentity("hat(matrix w[3][1])^(2 + (2 * int n + 1))",
                                              "hat(matrix w[3][1])^2* hat(matrix w[3][1])^(2 * int n + 1)"))
        calc.perform_rule(rules.OnSubterm(rules.ApplyInductHyp()))
        eq = "hat(matrix w[3][1])^2 = matrix w[3][1] * T(matrix w[3][1]) - norm(matrix w[3][1])^2 * unit_matrix(3)"
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(eq), "0"))
        eq = "norm(matrix w[3][1]) = 1"
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(eq), "0.1.0.0"))
        calc.perform_rule(rules.ExpandPolynomial())
        old_e = "(-1) ^ int n * matrix w[3][1] * T(matrix w[3][1]) * hat(matrix w[3][1])"
        new_e = "(-1) ^ int n * (matrix w[3][1] * T(matrix w[3][1]) * hat(matrix w[3][1]))"
        calc.perform_rule(rules.Equation(old_e, new_e))
        eq = "matrix w[3][1] * T(matrix w[3][1]) * hat(matrix w[3][1]) = zero_matrix(3,3)"
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(eq), "0.1"))
        calc.perform_rule(rules.FullSimplify())
        calc = induct_proof.rhs_calc
        calc.perform_rule(rules.FullSimplify())
        self.checkAndOutput(file)


    def testGetType(self):
        e = parser.parse_expr("inv(matrix P[n][n]) * matrix A[n][n] * matrix P[n][n]")
        ctx = Context()
        ty = matrix.get_type(e, ctx)
        assert ty == 'matrix'
        e = e ^ Const(0)
        from integral import poly
        from integral.poly import normalize
        e = normalize(e, ctx)
        assert e == parser.parse_expr("unit_matrix(n)")


if __name__ == "__main__":
    unittest.main()
