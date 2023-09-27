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
        file.add_definition("binom(n,m) = factorial(n) / (factorial(m) * factorial(n-m))")
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
        s1 = parser.parse_expr("factorial(n) / (factorial(m - 1) * factorial(-m + n + 1))")
        s2 = parser.parse_expr("(factorial(n) * m) / (((m-1+1) * factorial(m - 1)) * factorial(-m + n + 1))")
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = parser.parse_expr("factorial(n) / (factorial(m) * factorial(-m + n))")
        s2 = parser.parse_expr("factorial(n)*(-m+n +1) / (factorial(m) * ((-m+n+1)*factorial(-m + n)))")
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = parser.parse_expr("(-m+n+1)*factorial(-m + n)")
        s2 = parser.parse_expr("factorial(-m+n+1)")
        calc.perform_rule(rules.OnLocation(rules.ApplyIdentity(s1, s2), "1.1.1"))
        s1 = parser.parse_expr("(m - 1 + 1) * factorial(m - 1)")
        s2 = parser.parse_expr("factorial(m-1+1)")
        calc.perform_rule(rules.OnLocation(rules.ApplyIdentity(s1, s2), "0.1.0"))
        calc.perform_rule(rules.FullSimplify())
        s1 = parser.parse_expr("factorial(n) * (-m + n + 1) / (factorial(m) * factorial(-m + n + 1)) + m * factorial(n) / (factorial(m) * factorial(-m + n + 1))")
        s2 = parser.parse_expr("(n+1) * factorial(n) / (factorial(m) * factorial(-m + n + 1))")
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = parser.parse_expr("(n+1) * factorial(n)")
        s2 = parser.parse_expr("factorial(n+1)")
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
        cond = parser.parse_expr("i=m+1", fixes=fixes)
        calc.perform_rule(rules.SplitSummation(cond=cond))
        calc.perform_rule(rules.FullSimplify())
        s1 = parser.parse_expr("j+n", fixes=calc.ctx.get_fixes())
        s2 = parser.parse_expr("n+j", fixes=calc.ctx.get_fixes())
        calc.perform_rule(rules.Equation(s1, s2))
        calc.perform_rule(rules.OnLocation(rules.ApplyInductHyp(), "1"))
        s1 = parser.parse_expr("binom(m + n + 1,m + 1) + binom(m + n + 1,m)", fixes=calc.ctx.get_fixes())
        s2 = parser.parse_expr("binom(m + n + 1,m + 1 - 1) + binom(m + n + 1, m+1)", fixes=calc.ctx.get_fixes())
        calc.perform_rule(rules.Equation(s1, s2))
        calc.perform_rule(rules.ApplyEquation(goal03.goal))
        calc.perform_rule(rules.FullSimplify())
        assert goal04.is_finished()
        fixes = dict()
        fixes['n'] = parser.parse_expr('$int')
        fixes['k'] = parser.parse_expr('$int')
        goal05 = file.add_goal("(x+y)^n = SUM(k,0,n,binom(n, k)*x^k*y^(n-k))", conds=['x!=0', 'y!=0', 'n>0'], fixes=fixes)
        proof = goal05.proof_by_induction('n', 1)
        base_proof = proof.base_case.proof_by_calculation()
        calc = base_proof.rhs_calc
        cond = parser.parse_expr('k=0', fixes=fixes)
        calc.perform_rule(rules.SplitSummation(cond))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition("binom")))
        calc.perform_rule(rules.FullSimplify())
        induct_proof = proof.induct_case.proof_by_calculation()
        calc = induct_proof.lhs_calc
        s1 = parser.parse_expr("(x+y)^(n+1)", fixes=fixes)
        s2 = parser.parse_expr("(x+y)*(x+y)^n", fixes=fixes)
        calc.perform_rule(rules.Equation(s1, s2))
        calc.perform_rule(rules.OnLocation(rules.ApplyInductHyp(), '1'))
        calc.perform_rule(rules.ExpandPolynomial())

        s1 = parser.parse_expr("x * SUM(k, 0, n, x ^ k * y ^ (-k + n) * binom(n,k))", fixes=fixes)
        s2 = parser.parse_expr("SUM(k, 0, n, x * (x ^ k * y ^ (-k + n) * binom(n,k)))", fixes=fixes)
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = parser.parse_expr("y * SUM(k, 0, n, x ^ k * y ^ (-k + n) * binom(n,k))", fixes=fixes)
        s2 = parser.parse_expr("SUM(k, 0, n, y * (x ^ k * y ^ (-k + n) * binom(n,k)))", fixes=fixes)
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = parser.parse_expr("x * (x ^ k * y ^ (-k + n) * binom(n,k))", fixes=calc.ctx.get_fixes())
        s2 = parser.parse_expr("binom(n,k)*x^(k+1)*y^(n-k)", fixes=calc.ctx.get_fixes())
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = parser.parse_expr("y * (x ^ k * y ^ (-k + n) * binom(n,k))", fixes=calc.ctx.get_fixes())
        s2 = parser.parse_expr("binom(n,k)*x^k*y^(n-k+1)", fixes=calc.ctx.get_fixes())
        calc.perform_rule(rules.Equation(s1, s2))
        cond = parser.parse_expr("k=n", fixes=fixes)
        calc.perform_rule(rules.OnLocation(rules.SplitSummation(cond), '0'))
        cond = parser.parse_expr("k=0", fixes=fixes)
        calc.perform_rule(rules.OnLocation(rules.SplitSummation(cond), '1'))
        calc.perform_rule(rules.FullSimplify())
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('binom'), '0.1.1'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('binom'), '1.1'))
        calc.perform_rule(rules.OnLocation(rules.ChangeSummationIndex("1"), '0.0.0'))
        calc.perform_rule(rules.FullSimplify())
        s1 = parser.parse_expr("SUM(i, 1, n, x ^ i * y ^ (-i + n + 1) * binom(n,i - 1)) + SUM(i, 1, n, x ^ i * y ^ (-i + n + 1) * binom(n,i))", fixes=calc.ctx.get_fixes())
        s2 = parser.parse_expr("SUM(i, 1, n, x ^ i * y ^ (-i + n + 1) * binom(n,i - 1) + x ^ i * y ^ (-i + n + 1) * binom(n,i))", fixes=calc.ctx.get_fixes())
        calc.perform_rule(rules.Equation(s1, s2))
        s1 = parser.parse_expr(
            "x ^ i * y ^ (-i + n + 1) * binom(n,i - 1) + x ^ i * y ^ (-i + n + 1) * binom(n,i)",
            fixes=calc.ctx.get_fixes())
        s2 = parser.parse_expr(
            "x ^ i * y ^ (-i + n + 1) * (binom(n,i - 1) + binom(n,i))",
            fixes=calc.ctx.get_fixes())
        calc.perform_rule(rules.Equation(s1, s2))
        calc.perform_rule(rules.OnLocation(rules.ApplyEquation(goal03.goal) ,'0.0.0.1'))
        calc = induct_proof.rhs_calc
        cond = parser.parse_expr("k=0", fixes=calc.ctx.get_fixes())
        calc.perform_rule(rules.SplitSummation(cond))

        cond = parser.parse_expr("i=n+1", fixes=calc.ctx.get_fixes())
        calc.perform_rule(rules.OnLocation(rules.SplitSummation(cond), '1'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('binom'), '0.0.1'))
        calc.perform_rule(rules.OnLocation(rules.ExpandDefinition('binom'), '1.1.0.1'))
        calc.perform_rule(rules.FullSimplify())

        self.checkAndOutput(file)

if __name__ == "__main__":
    unittest.main()
