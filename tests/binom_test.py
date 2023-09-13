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
            self.assertEqual(compstate.parse_item(file.content[i].parent, item).export(), file.content[i].export())

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
        file.add_definition("C(n,m) = factorial(n) / (factorial(m) * factorial(n-m))")
        goal01 = file.add_goal("C(n,m) = C(n,n-m)")
        proof = goal01.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.ExpandDefinition("C"))
        calc = proof.rhs_calc
        calc.perform_rule(rules.ExpandDefinition("C"))
        goal02 = file.add_goal("C(n,m)*C(m,r) = C(n,r)*C(n-r, m-r)")
        proof = goal02.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition("C")))
        calc.perform_rule(rules.FullSimplify())
        calc = proof.rhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition("C")))
        calc.perform_rule(rules.FullSimplify())
        goal03 = file.add_goal("C(n,m-1)+C(n,m) = C(n+1, m)")
        proof = goal03.proof_by_calculation()
        calc = proof.lhs_calc
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition("C")))
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
        calc.perform_rule(rules.OnSubterm(rules.ExpandDefinition("C")))
        goal04 = file.add_goal("C(m+n+1,m) = SUM(i, 0, m, C(n+i, i))", conds=["m>=0", "n>=0"], fixes=fixes)
        proof = goal04.proof_by_induction("m")
        base_proof = proof.base_case.proof_by_calculation()
        calc = base_proof.lhs_calc
        calc.perform_rule(rules.ExpandDefinition("C"))
        calc = base_proof.rhs_calc
        calc.perform_rule(rules.ExpandDefinition("C"))
        induct_proof = proof.induct_case.proof_by_calculation()
        calc = induct_proof.rhs_calc
        cond = parser.parse_expr("i=m+1", fixes=fixes)
        calc.perform_rule(rules.SplitSummation(cond=cond))
        calc.perform_rule(rules.FullSimplify())
        s1 = parser.parse_expr("j+n", fixes=calc.ctx.get_fixes())
        s2 = parser.parse_expr("n+j", fixes=calc.ctx.get_fixes())
        calc.perform_rule(rules.Equation(s1, s2))
        calc.perform_rule(rules.OnLocation(rules.ApplyInductHyp(), "1"))
        s1 = parser.parse_expr("C(m + n + 1,m + 1) + C(m + n + 1,m)", fixes=calc.ctx.get_fixes())
        s2 = parser.parse_expr("C(m + n + 1,m + 1 - 1) + C(m + n + 1, m+1)", fixes=calc.ctx.get_fixes())
        calc.perform_rule(rules.Equation(s1, s2))
        calc.perform_rule(rules.ApplyEquation(goal03.goal))
        calc.perform_rule(rules.FullSimplify())
        print(goal04)

if __name__ == "__main__":
    unittest.main()
