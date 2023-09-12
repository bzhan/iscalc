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
        print(file)
if __name__ == "__main__":
    unittest.main()
