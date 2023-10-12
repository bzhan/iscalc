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

class BinomTest(unittest.TestCase):
    def checkAndOutput(self, file: compstate.CompFile, omit_finish: bool = False):
        # Test parsing of json file
        json_file = file.export()
        for i, item in enumerate(json_file['content']):
            aa, bb = compstate.parse_item(file.content[i].parent, item), file.content[i]
            a, b = aa.export(), bb.export()
            # if a != b:
            #     if isinstance(aa, compstate.Goal) and isinstance(bb, compstate.Goal):
            #         aa.is_finished()
            #     with open('examples/a.json', 'w', encoding='utf-8') as f:
            #         json.dump(a, f, indent=4, ensure_ascii=False, sort_keys=True)
            #     with open('examples/b.json', 'w', encoding='utf-8') as f:
            #         json.dump(b, f, indent=4, ensure_ascii=False, sort_keys=True)
            self.assertEqual(a, b)
        # Output to file
        with open('examples/' + file.name + '.json', 'w', encoding='utf-8') as f:
        # with open('../examples/' + file.name + '.json', 'w', encoding='utf-8') as f:
            json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)

        # Test goals are finished
        if not omit_finish:
            for content in file.content:
                self.assertTrue(content.is_finished())

    def testExample01(self):
        fixes = dict()
        fixes['m'] = parser.parse_expr('$int')
        fixes['n'] = parser.parse_expr('$int')
        fixes['i'] = parser.parse_expr('$int')
        file = compstate.CompFile("base", "binom_example01")
        goal01 = file.add_goal("binom(n,m) = binom(n,n-m)")
        proof = goal01.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.ExpandDefinition("binom"))
        calc = proof.rhs_calc
        calc.perform_rule(rules.ExpandDefinition("binom"))
        assert goal01.is_finished()
        goal02 = file.add_goal("binom(n,m)*binom(m,r) = binom(n,r)*binom(n-r, m-r)")
        proof = goal02.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition("binom")))
        calc.perform_rule(rules.FullSimplify())
        calc = proof.rhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition("binom")))
        calc.perform_rule(rules.FullSimplify())
        assert goal02.is_finished()
        goal03 = file.add_goal("binom(n,m-1)+binom(n,m) = binom(n+1, m)")
        proof = goal03.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition("binom")))
        s1 = calc.parse_expr("factorial(n) / (factorial(m - 1) * factorial(-m + n + 1))")
        s2 = calc.parse_expr("(factorial(n) * m) / (((m-1+1) * factorial(m - 1)) * factorial(-m + n + 1))")
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = calc.parse_expr("factorial(n) / (factorial(m) * factorial(-m + n))")
        s2 = calc.parse_expr("factorial(n)*(-m+n +1) / (factorial(m) * ((-m+n+1)*factorial(-m + n)))")
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = calc.parse_expr("(-m+n+1)*factorial(-m + n)")
        s2 = calc.parse_expr("factorial(-m+n+1)")
        calc.perform_rule(rules.OnLocation(rules.ApplyIdentity(s1, s2), "1.1.1"))
        s1 = calc.parse_expr("(m - 1 + 1) * factorial(m - 1)")
        s2 = calc.parse_expr("factorial(m-1+1)")
        calc.perform_rule(rules.OnLocation(rules.ApplyIdentity(s1, s2), "0.1.0"))
        calc.perform_rule(rules.FullSimplify())
        s1 = calc.parse_expr("factorial(n) * (-m + n + 1) / (factorial(m) * factorial(-m + n + 1)) + m * factorial(n) / (factorial(m) * factorial(-m + n + 1))")
        s2 = calc.parse_expr("(n+1) * factorial(n) / (factorial(m) * factorial(-m + n + 1))")
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = calc.parse_expr("(n+1) * factorial(n)")
        s2 = calc.parse_expr("factorial(n+1)")
        calc.perform_rule(rules.OnLocation(rules.ApplyIdentity(s1, s2), "0"))
        calc = proof.rhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition("binom")))
        assert goal03.is_finished()
        goal04 = file.add_goal("binom(m+n+1,m) = SUM(i, 0, m, binom(n+i, i))", conds=["m>=0", "n>=0"], fixes=fixes)
        proof = goal04.proof_by_induction("m")
        base_proof = proof.base_case.proof_by_calculation()
        calc = base_proof.lhs_calc
        calc.perform_rule(rules.ExpandDefinition("binom"))
        calc = base_proof.rhs_calc
        calc.perform_rule(rules.ExpandDefinition("binom"))
        induct_proof = proof.induct_case.proof_by_calculation()
        calc = induct_proof.rhs_calc
        cond = calc.parse_expr("i=m+1")
        calc.perform_rule(rules.SplitSummation(cond=cond))
        calc.perform_rule(rules.FullSimplify())
        s1 = calc.parse_expr("j+n")
        s2 = calc.parse_expr("n+j")
        calc.perform_rule(rules.Equation(s1, s2))
        calc.perform_rule(rules.OnLocation(rules.ApplyInductHyp(), "1"))
        s1 = calc.parse_expr("binom(m + n + 1,m + 1) + binom(m + n + 1,m)")
        s2 = calc.parse_expr("binom(m + n + 1,m + 1 - 1) + binom(m + n + 1, m+1)")
        calc.perform_rule(rules.Equation(s1, s2))
        source = calc.parse_expr("binom(m + n + 1,m + 1 - 1) + binom(m + n + 1,m + 1)")
        calc.perform_rule(rules.ApplyEquation(goal03.goal, source))
        calc.perform_rule(rules.FullSimplify())
        assert goal04.is_finished()
        fixes = dict()
        fixes['n'] = parser.parse_expr('$int')
        fixes['k'] = parser.parse_expr('$int')
        goal05 = file.add_goal("(x+y)^n = SUM(k,0,n,binom(n, k)*x^k*y^(n-k))", conds=['x!=0', 'y!=0', 'n>0'], fixes=fixes)
        proof = goal05.proof_by_induction('n', 1)
        base_proof = proof.base_case.proof_by_calculation()
        calc = base_proof.rhs_calc
        cond = calc.parse_expr('k=0')
        calc.perform_rule(rules.SplitSummation(cond))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition("binom")))
        calc.perform_rule(rules.FullSimplify())
        induct_proof = proof.induct_case.proof_by_calculation()
        calc = induct_proof.lhs_calc
        s1 = calc.parse_expr("(x+y)^(n+1)")
        s2 = calc.parse_expr("(x+y)*(x+y)^n")
        calc.perform_rule(rules.Equation(s1, s2))
        calc.perform_rule(rules.OnLocation(rules.ApplyInductHyp(), '1'))
        calc.perform_rule(rules.ExpandPolynomial())

        s1 = calc.parse_expr("x * SUM(k, 0, n, x ^ k * y ^ (-k + n) * binom(n,k))")
        s2 = calc.parse_expr("SUM(k, 0, n, x * (x ^ k * y ^ (-k + n) * binom(n,k)))")
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = calc.parse_expr("y * SUM(k, 0, n, x ^ k * y ^ (-k + n) * binom(n,k))")
        s2 = calc.parse_expr("SUM(k, 0, n, y * (x ^ k * y ^ (-k + n) * binom(n,k)))")
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = calc.parse_expr("x * (x ^ k * y ^ (-k + n) * binom(n,k))")
        s2 = calc.parse_expr("binom(n,k)*x^(k+1)*y^(n-k)")
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = calc.parse_expr("y * (x ^ k * y ^ (-k + n) * binom(n,k))")
        s2 = calc.parse_expr("binom(n,k)*x^k*y^(n-k+1)")
        calc.perform_rule(rules.Equation(s1, s2))
        cond = calc.parse_expr("k=n")
        calc.perform_rule(rules.OnLocation(rules.SplitSummation(cond), '0'))
        cond = calc.parse_expr("k=0")
        calc.perform_rule(rules.OnLocation(rules.SplitSummation(cond), '1'))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('binom'), '0.1.1'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('binom'), '1.1'))
        calc.perform_rule(rules.OnLocation(rules.ChangeSummationIndex("1"), '0.0.0'))
        calc.perform_rule(rules.FullSimplify())
        s1 = calc.parse_expr("SUM(i, 1, n, x ^ i * y ^ (-i + n + 1) * binom(n,i - 1)) + SUM(i, 1, n, x ^ i * y ^ (-i + n + 1) * binom(n,i))")
        s2 = calc.parse_expr("SUM(i, 1, n, x ^ i * y ^ (-i + n + 1) * binom(n,i - 1) + x ^ i * y ^ (-i + n + 1) * binom(n,i))")
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = calc.parse_expr(
            "x ^ i * y ^ (-i + n + 1) * binom(n,i - 1) + x ^ i * y ^ (-i + n + 1) * binom(n,i)")
        s2 = calc.parse_expr(
            "x ^ i * y ^ (-i + n + 1) * (binom(n,i - 1) + binom(n,i))")
        calc.perform_rule(rules.Equation(s1, s2))
        source = calc.parse_expr("binom(n,i - 1) + binom(n,i)")
        calc.perform_rule(rules.ApplyEquation(goal03.goal, source))
        calc = induct_proof.rhs_calc
        cond = calc.parse_expr("k=0")
        calc.perform_rule(rules.SplitSummation(cond))

        cond = calc.parse_expr("i=n+1")
        calc.perform_rule(rules.OnLocation(rules.SplitSummation(cond), '1'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('binom'), '0.1'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('binom'), '1.1.1'))
        calc.perform_rule(rules.FullSimplify())
        self.checkAndOutput(file)


    def testExample02(self):
        fixes = dict()
        fixes['n'] = parser.parse_expr('$int')
        file = compstate.CompFile("base", "binom_example02")
        goal01 = file.add_goal("(LIM {n -> oo}. binom(2 * n,n) / (4 ^ n / sqrt(n * pi))) = 1")
        proof = goal01.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition("binom")))
        s1 = "factorial(2 * n)"
        s2 = "(factorial(2*n)/(sqrt(4*pi*n)*(2*n/exp(1))^(2*n)))*(sqrt(4*pi*n)*(2*n/exp(1))^(2*n))"
        calc.perform_rule(rules.Equation(s1, s2))
        s3 = "factorial(n)"
        s4 = "(factorial(n)/(sqrt(2*pi*n)*(n/exp(1))^n))*(sqrt(2*pi*n)*(n/exp(1))^n)"
        calc.perform_rule(rules.Equation(s3, s4))
        s5 = "(factorial(n) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n) * (sqrt(2 * pi * n) * (n / exp(1)) ^ n)) ^ 2"
        s6 = "(factorial(n) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n)) ^ 2 * (sqrt(2 * pi * n) * (n / exp(1)) ^ n) ^ 2"
        calc.perform_rule(rules.Equation(s5, s6))
        s7 = "factorial(2 * n) / (sqrt(4 * pi * n) * (2 * n / exp(1)) ^ (2 * n)) * (sqrt(4 * pi * n) * (2 * n / exp(1)) ^ (2 * n)) / ((factorial(n) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n)) ^ 2 * (sqrt(2 * pi * n) * (n / exp(1)) ^ n) ^ 2) "
        s8 = "((factorial(2*n)/(sqrt(4*pi*n)*(2*n/exp(1))^(2*n)))/((factorial(n)/(sqrt(2*pi*n)*(n/exp(1))^n))^2))*(sqrt(4*pi*n)*(2*n/exp(1))^(2*n))/((sqrt(2*pi*n)*(n/exp(1))^n)^2)"
        calc.perform_rule(rules.Equation(s7, s8))
        s9 = "factorial(2 * n) / (sqrt(4 * pi * n) * (2 * n / exp(1)) ^ (2 * n)) / (factorial(n) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n)) ^ 2 * (sqrt(4 * pi * n) * (2 * n / exp(1)) ^ (2 * n)) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n) ^ 2 / (4 ^ n / sqrt(n * pi))"
        s10 = "(factorial(2 * n) / (sqrt(4 * pi * n) * (2 * n / exp(1)) ^ (2 * n)) / (factorial(n) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n)) ^ 2) * ((sqrt(4 * pi * n) * (2 * n / exp(1)) ^ (2 * n)) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n) ^ 2 / (4 ^ n / sqrt(n * pi)))"
        calc.perform_rule(rules.Equation(s9, s10))
        calc.perform_rule(rules.OnLocation(rules.FullSimplify(), "0.1"))
        s11 = "2 * n * exp(-1)"
        s12 = "2 * (n * exp(-1))"
        calc.perform_rule(rules.Equation(s11, s12))
        s13 = "(2 * (n * exp(-1))) ^ (2 * n)"
        s14 = "2 ^ (2 * n) * (n * exp(-1)) ^ (2 * n)"
        calc.perform_rule(rules.ApplyIdentity(s13, s14))
        s15 = "2 ^ (2 * n)"
        s16 = "(2 ^ 2) ^ n"
        calc.perform_rule(rules.ApplyIdentity(s15, s16))
        calc.perform_rule(rules.OnLocation(rules.FullSimplify(), "0.1"))
        s17 = "factorial(2 * n) / (sqrt(4 * pi * n) * (2 * n / exp(1)) ^ (2 * n)) / (factorial(n) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n)) ^ 2 * 1"
        s18 = "(factorial(2 * n) / (sqrt(4 * pi * n) * (2 * n / exp(1)) ^ (2 * n))) / (factorial(n) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n)) ^ 2"
        calc.perform_rule(rules.Equation(s17, s18))
        s19 = calc.parse_expr("LIM {n -> oo}. (factorial(2 * n) / (sqrt(4 * pi * n) * (2 * n / exp(1)) ^ (2 * n))) / (factorial(n) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n)) ^ 2")
        s20 = calc.parse_expr("(LIM {n -> oo}. factorial(2 * n) / (sqrt(4 * pi * n) * (2 * n / exp(1)) ^ (2 * n))) / (LIM {n -> oo}. (factorial(n) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n)) ^ 2)")
        calc.perform_rule(rules.Equation(s19, s20))
        s21 = "(factorial(n) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n)) ^ 2"
        s22 = "(factorial(n) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n)) * (factorial(n) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n))"
        calc.perform_rule(rules.Equation(s21, s22))
        s23 = "LIM {n -> oo}. factorial(n) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n) * (factorial(n) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n))"
        s24 = "(LIM {n -> oo}. factorial(n) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n)) * (LIM {n -> oo}. (factorial(n) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n)))"
        calc.perform_rule(rules.Equation(s23, s24))
        calc.perform_rule(rules.OnLocation(rules.Substitution("k", "2 * n"), "0"))
        s25 = "sqrt(2) * factorial(k) * (k * exp(-1)) ^ -k / (2 * sqrt(k) * sqrt(pi))"
        s26 = "factorial(k) / (2 * sqrt(k) * sqrt(pi) / sqrt(2) * (k / exp(1)) ^ k)"
        calc.perform_rule(rules.Equation(s25, s26))
        s27 = "2 * sqrt(k) * sqrt(pi) / sqrt(2)"
        s28 = "sqrt(2 * pi * k)"
        calc.perform_rule(rules.Equation(s27, s28))
        s29 = calc.parse_expr("(LIM {k -> oo}. factorial(k) / (sqrt(2 * pi * k) * (k / exp(1)) ^ k))")
        s30 = calc.parse_expr("1")
        calc.perform_rule(rules.ApplyIdentity(s29, s30))
        s31 = calc.parse_expr("(LIM {n -> oo}. factorial(n) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n))")
        s32 = calc.parse_expr("1")
        calc.perform_rule(rules.ApplyIdentity(s31, s32))
        s33 = calc.parse_expr("(LIM {n -> oo}. factorial(n) / (sqrt(2 * pi * n) * (n / exp(1)) ^ n))")
        s34 = calc.parse_expr("1")
        calc.perform_rule(rules.ApplyIdentity(s33, s34))
        calc.perform_rule(rules.FullSimplify())

        self.checkAndOutput(file)


    def testExample03(self):
        fixes = dict()
        fixes['k'] = parser.parse_expr('$int')
        file = compstate.CompFile("base", "binom_example03")
        goal01 = file.add_goal("binom(2 * k, k) = (k + 1) / (2 * (2 * k + 1)) * binom(2 * k + 2, k + 1)")
        proof = goal01.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.ExpandDefinition("binom"))
        s1 = "factorial(2 * k) / factorial(k) ^ 2"
        s2 = "((k + 1) * (2 * k + 2) * ((2 * k + 1) * factorial(2 * k))) / (2 * ((k + 1) * factorial(k)) * ((k + 1) * factorial(k)) * (2 * k + 1))"
        calc.perform_rule(rules.Equation(s1, s2))
        s3 = "(2 * k + 1) * factorial(2 * k)"
        s4 = "factorial(2 * k + 1)"
        calc.perform_rule(rules.ApplyIdentity(s3, s4))
        s5 = "(k + 1) * factorial(k)"
        s6 = "factorial(k + 1)"
        calc.perform_rule(rules.ApplyIdentity(s5, s6))
        s7 = "(k + 1) * factorial(k)"
        s8 = "factorial(k + 1)"
        calc.perform_rule(rules.ApplyIdentity(s7, s8))
        s9 = "(k + 1) * (2 * k + 2) * factorial(2 * k + 1)"
        s10 = "(k + 1) * ((2 * k + 1 + 1) * factorial(2 * k + 1))"
        calc.perform_rule(rules.Equation(s9, s10))
        s11 = "(2 * k + 1 + 1) * factorial(2 * k + 1)"
        s12 = "factorial(2 * k + 2)"
        calc.perform_rule(rules.ApplyIdentity(s11, s12))
        s13 = "(k + 1) * factorial(2 * k + 2) / (2 * factorial(k + 1) * factorial(k + 1) * (2 * k + 1))"
        s14 = "(k + 1) / (2 * (2 * k + 1)) * (factorial(2 * k + 2) / (factorial(k + 1)) ^ 2)"
        calc.perform_rule(rules.Equation(s13, s14))
        calc = proof.rhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition("binom")))

        self.checkAndOutput(file)

    def testExample04(self):
        fixes = dict()
        fixes['m'] = parser.parse_expr('$int')
        fixes['n'] = parser.parse_expr('$int')
        fixes['k'] = parser.parse_expr('$int')
        file = compstate.CompFile("binom", "binom_example04")
        goal01 = file.add_goal("SUM(k, 0, n, (((8 - m / 8) * k ^ 3 - 4 * k ^ 2 - 2 * k + 1) * binom(2 * k, k) ^ 3) / ((2 * k - 1) ^ 2 * m ^ k)) = (2 * n + 1) / m ^ n * binom(2 * n, n) ^ 3", conds=['m != 0', 'n>=0'], fixes=fixes)
        proof = goal01.proof_by_induction("n", 0)
        proof_base = proof.base_case.proof_by_calculation()
        proof_induct = proof.induct_case.proof_by_calculation()
        calc = proof_base.lhs_calc
        calc = proof_induct.lhs_calc
        cond = calc.parse_expr("k <= n")
        calc.perform_rule(rules.SplitSummation(cond))
        calc.perform_rule(rules.OnLocation(rules.FullSimplify(), "1"))
        s1 = "m ^ -i / (2 * i - 1) ^ 2 * binom(2 * i,i) ^ 3 * (i ^ 3 * (-(m / 8) + 8) - 4 * i ^ 2 - 2 * i + 1)"
        s1 = calc.parse_expr(s1)
        s2 = "(((8 - m / 8) * i ^ 3 - 4 * i ^ 2 - 2 * i + 1) * binom(2 * i, i) ^ 3) / ((2 * i - 1) ^ 2 * m ^ i)"
        s2 = calc.parse_expr(s2)
        calc.perform_rule(rules.Equation(s1, s2))
        calc.perform_rule(rules.OnLocation(rules.ApplyInductHyp(), "0"))
        s3 = "binom(2 * k, k) = (k + 1) / (2 * (2 * k + 1)) * binom(2 * k + 2, k + 1)"
        s3 = calc.parse_expr(s3)
        s4 = "binom(2 * n,n)"
        s4 = calc.parse_expr(s4)
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(s3, s4), "0.1.0"))
        s5 = "(2 * n + 1) / m ^ n * ((n + 1) / (2 * (2 * n + 1)) * binom(2 * n + 2,n + 1)) ^ 3"
        s5 = calc.parse_expr(s5)
        s6 = "((m / 8) * (n + 1) ^ 3) / ((2 * n + 1) ^ 2 * m ^ (n + 1)) * binom(2 * n + 2, n + 1) ^ 3"
        s6 = calc.parse_expr(s6)
        calc.perform_rule(rules.Equation(s5, s6))
        s7 = "m ^ (-n - 1) / (2 * n + 1) ^ 2 * binom(2 * n + 2,n + 1) ^ 3 * ((n + 1) ^ 3 * (-(m / 8) + 8) - 4 * (n + 1) ^ 2 - 2 * n - 1)"
        s7 = calc.parse_expr(s7)
        s8 = "((8 - m / 8) * (n + 1) ^ 3- 4 * (n + 1) ^ 2 - 2 * n - 1) / ((2 * n + 1) ^ 2 * m ^ (n + 1)) * binom(2 * n + 2, n + 1) ^ 3"
        s8 = calc.parse_expr(s8)
        calc.perform_rule(rules.Equation(s7, s8))
        s9 = "m / 8 * (n + 1) ^ 3 / ((2 * n + 1) ^ 2 * m ^ (n + 1)) * binom(2 * n + 2,n + 1) ^ 3 + ((8 - m / 8) * (n + 1) ^ 3 - 4 * (n + 1) ^ 2 - 2 * n - 1) / ((2 * n + 1) ^ 2 * m ^ (n + 1)) * binom(2 * n + 2,n + 1) ^ 3"
        s9 = calc.parse_expr(s9)
        s10 = "(8 * (n + 1) ^ 3 - 4 * (n + 1) ^ 2 - 2 * (n + 1) + 1) / ((2 * n + 1) ^ 2 * m ^ (n + 1)) * binom(2 * n + 2,n + 1) ^ 3"
        s10 = calc.parse_expr(s10)
        calc.perform_rule(rules.Equation(s9, s10))
        s11 = "8 * (n + 1) ^ 3 - 4 * (n + 1) ^ 2 - 2 * (n + 1) + 1"
        s11 = calc.parse_expr(s11)
        s12 = "(2 * n + 1) ^ 2 * (2 * n + 3)"
        s12 = calc.parse_expr(s12)
        calc.perform_rule(rules.Equation(s11, s12))
        calc.perform_rule(rules.FullSimplify())
        fixes = dict()
        fixes['m'] = parser.parse_expr('$int')
        fixes['n'] = parser.parse_expr('$int')
        fixes['k'] = parser.parse_expr('$int')
        goal02 = file.add_goal(
            "(LIM {n->oo}. SUM(k, 0, n, (((8 - m / 8) * k ^ 3 - 4 * k ^ 2 - 2 * k + 1) * binom(2 * k, k) ^ 3) / ((2 * k - 1) ^ 2 * m ^ k))) = LIM {n->oo}. (2 * n + 1) / m ^ n * binom(2 * n, n) ^ 3",
            conds=['m != 0'], fixes=fixes)
        proof = goal02.proof_by_rewrite_goal(begin=goal01)
        calc = proof.begin
        calc.perform_rule(rules.LimitEquation('n', expr.POS_INF))
        assert goal02.is_finished()
        s = "SUM(k, 0, oo, (16*k^3 - 4*k^2-2*k+1) * binom(2*k, k)^3 / ((2*k-1)^2*(-64)^k)) = 0"
        fixes = dict()
        fixes['k'] = expr.IntType
        goal03 = file.add_goal(s, fixes=fixes, conds=["k>=0"])
        proof = goal03.proof_by_calculation()
        calc = proof.lhs_calc
        s1 = calc.parse_expr("16")
        s2 = calc.parse_expr("8-((-64) / 8)")
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = calc.parse_expr("SUM(k, 0, oo, ((8 - -64/8) * k ^ 3 - 4 * k ^ 2 - 2 * k + 1) * binom(2 * k,k) ^ 3 / ((2 * k - 1) ^ 2 * (-64) ^ k))")
        new_v = {'n':expr.IntType}
        s2 = calc.parse_expr("LIM {n->oo}. SUM(k, 0, n, ((8 - -64//8) * k ^ 3 - 4 * k ^ 2 - 2 * k + 1) * binom(2 * k,k) ^ 3 / ((2 * k - 1) ^ 2 * (-64) ^ k))", fixes=new_v)
        calc.perform_rule(rules.Equation(s1, s2))
        source = calc.parse_expr("LIM {n->oo}. SUM(k, 0, n, ((8 - (-64)//8) * k ^ 3 - 4 * k ^ 2 - 2 * k + 1) * binom(2 * k,k) ^ 3 / ((2 * k - 1) ^ 2 * (-64) ^ k))")
        calc.perform_rule(rules.ApplyEquation(goal02.goal, source))
        s3 = "binom(2 * n,n)"
        s3 = calc.parse_expr(s3)
        s4 = "(4 ^ n / sqrt(n * pi)) *binom(2 * n,n) / (4 ^ n / sqrt(n * pi))"
        s4 = calc.parse_expr(s4)
        calc.perform_rule(rules.Equation(s3, s4))
        s5 = calc.parse_expr("(4 ^ n / sqrt(n * pi) * binom(2 * n,n) / (4 ^ n / sqrt(n * pi))) ^ 3")
        s6 = calc.parse_expr("(4 ^ n / sqrt(n * pi)) ^ 3 * (binom(2 * n,n) / (4 ^ n / sqrt(n * pi))) ^ 3")
        calc.perform_rule(rules.ApplyIdentity(s5, s6))
        s7 = "(2 * n + 1) / (-64) ^ n * ((4 ^ n / sqrt(n * pi)) ^ 3 * (binom(2 * n,n) / (4 ^ n / sqrt(n * pi))) ^ 3)"
        s7 = calc.parse_expr(s7)
        s8 = "((2 * n + 1) / (-64) ^ n * ((4 ^ n / sqrt(n * pi)) ^ 3) * (binom(2 * n,n) / (4 ^ n / sqrt(n * pi))) ^ 3)"
        s8 = calc.parse_expr(s8)
        calc.perform_rule(rules.Equation(s7, s8))
        s9 = "LIM {n -> oo}. (2 * n + 1) / (-64) ^ n * (4 ^ n / sqrt(n * pi)) ^ 3 * (binom(2 * n,n) / (4 ^ n / sqrt(n * pi))) ^ 3"
        s9 = calc.parse_expr(s9)
        s10 = "(LIM {n -> oo}. (2 * n + 1) / (-64) ^ n * (4 ^ n / sqrt(n * pi)) ^ 3) * (LIM {n -> oo}. (binom(2 * n,n) / (4 ^ n / sqrt(n * pi))) ^ 3)"
        s10 = calc.parse_expr(s10)
        calc.perform_rule(rules.Equation(s9, s10))
        calc.perform_rule(rules.OnLocation(rules.FullSimplify(), "0.0"))
        s11 = "n ^ (3/2) * pi ^ (3/2)"
        s11 = calc.parse_expr(s11)
        s12 = "(n * pi) ^ (3/2)"
        s12 = calc.parse_expr(s12)
        calc.perform_rule(rules.ApplyIdentity(s11, s12))
        s13 = "4 ^ (3 * n)"
        s13 = calc.parse_expr(s13)
        s14 = "64 ^ n"
        s14 = calc.parse_expr(s14)
        calc.perform_rule(rules.ApplyIdentity(s13, s14))
        s15 = "(-64) ^ -n"
        s15 = calc.parse_expr(s15)
        s16 = "(1 / -64) ^ n"
        s16 = calc.parse_expr(s16)
        calc.perform_rule(rules.ApplyIdentity(s15, s16))
        s17 = "(1 / -64) ^ n * 64 ^ n"
        s17 = calc.parse_expr(s17)
        s18 = "(-1) ^ n"
        s18 = calc.parse_expr(s18)
        calc.perform_rule(rules.ApplyIdentity(s17, s18))
        calc.perform_rule(rules.OnLocation(rules.FullSimplify(), "0"))
        s19 = "LIM {n -> oo}. (binom(2 * n,n) / (4 ^ n / sqrt(n * pi))) ^ 3"
        s19 = calc.parse_expr(s19)
        s20 = "(LIM {n -> oo}. binom(2 * n,n) / (4 ^ n / sqrt(n * pi))) ^ 3"
        s20 = calc.parse_expr(s20)
        calc.perform_rule(rules.Equation(s19, s20))
        s21 = "LIM {n -> oo}. binom(2 * n,n) / (4 ^ n / sqrt(n * pi))"
        s21 = calc.parse_expr(s21)
        s22 = "1"
        s22 = calc.parse_expr(s22)
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(s21, s22), "1.0"))


        goal04 = file.add_goal("SUM(k, 0, oo, (k * (4 * k - 1) * binom(2 * k, k) ^ 3) / ((2 * k - 1) ^ 2 * (-64) ^ k)) = -1 / pi")
        proof = goal04.proof_by_rewrite_goal(begin=goal03)
        calc = proof.begin
        s1 = "16 * k ^ 3 - 4 * k ^ 2 - 2 * k + 1"
        s1 = calc.parse_expr(s1)
        s2 = "(4 * k + 1) * (2 * k - 1) ^ 2 + 2 * k * (4 * k - 1)"
        s2 = calc.parse_expr(s2)
        calc.perform_rule(rules.Equation(s1, s2))
        s3 = "((4 * k + 1) * (2 * k - 1) ^ 2 + 2 * k * (4 * k - 1)) * binom(2 * k,k) ^ 3 / ((2 * k - 1) ^ 2 * (-64) ^ k)"
        s3 = calc.parse_expr(s3)
        s4 = "((4 * k + 1) * (2 * k - 1) ^ 2) * binom(2 * k,k) ^ 3 / ((2 * k - 1) ^ 2 * (-64) ^ k) + (2 * k * (4 * k - 1)) * binom(2 * k,k) ^ 3 / ((2 * k - 1) ^ 2 * (-64) ^ k)"
        s4 = calc.parse_expr(s4)
        calc.perform_rule(rules.Equation(s3, s4))
        s5 = "(4 * k + 1) * (2 * k - 1) ^ 2 * binom(2 * k,k) ^ 3 / ((2 * k - 1) ^ 2 * (-64) ^ k)"
        s5 = calc.parse_expr(s5)
        s6 = "(4 * k + 1) * binom(2 * k,k) ^ 3 / (-64) ^ k"
        s6 = calc.parse_expr(s6)
        calc.perform_rule(rules.Equation(s5, s6))
        s7 = "SUM(k, 0, oo, (4 * k + 1) * binom(2 * k,k) ^ 3 / (-64) ^ k + 2 * k * (4 * k - 1) * binom(2 * k,k) ^ 3 / ((2 * k - 1) ^ 2 * (-64) ^ k))"
        s7 = calc.parse_expr(s7)
        s8 = "SUM(k, 0, oo, (4 * k + 1) * binom(2 * k,k) ^ 3 / (-64) ^ k) + SUM(k, 0, oo, 2 * k * (4 * k - 1) * binom(2 * k,k) ^ 3 / ((2 * k - 1) ^ 2 * (-64) ^ k))"
        s8 = calc.parse_expr(s8)
        calc.perform_rule(rules.Equation(s7, s8))
        calc.perform_rule(rules.OnLocation(rules.SeriesEvaluationIdentity(),'0.0'))
        self.checkAndOutput(file)


if __name__ == "__main__":
    unittest.main()
