"""Unit test for integrals using internal language."""

import unittest
import lark

from integral import compstate
from integral import action
from integral import parser


class ActionTest(unittest.TestCase):
    def testStandard(self):
        file = compstate.CompFile("base", "standard")
        ctx = file.get_context()

        actions = [
            "calculate INT x:[0,1]. (3 * x + 1) ^ (-2)",
            "substitute u for 3 * x + 1",
            "apply integral identity",
            "simplify"
        ]
        state = action.InitialState(ctx)
        for act in actions:
            a = parser.parse_action(act)
            state = state.process_action(a)
        print(state)
        self.assertTrue(state.is_finished())

        actions = [
            "calculate INT x:[0,oo]. log(x) / (x ^ 2 + 1)",
            "split region at 1",
            "inverse substitute 1 / u for x creating u",
            "simplify",
            "rewrite u ^ 2 * (1 / u ^ 2 + 1) to u ^ 2 + 1",
            "simplify"
        ]
        state = action.InitialState(ctx)
        for act in actions:
            try:
                a = parser.parse_action(act)
            except lark.exceptions.UnexpectedToken as e:
                print("Error when parsing: %s" % act)
                raise e
            state = state.process_action(a)
        print(state)
        self.assertTrue(state.is_finished())

        actions = [
            "calculate INT x:[-1,2]. x * exp(x)",
            "integrate by parts with u = x, v = exp(x)",
            "apply integral identity",
            "simplify",
        ]
        state = action.InitialState(ctx)
        for act in actions:
            try:
                a = parser.parse_action(act)
            except lark.exceptions.UnexpectedToken as e:
                print("Error when parsing: %s" % act)
                raise e
            state = state.process_action(a)
        print(state)
        self.assertTrue(state.is_finished())


if __name__ == "__main__":
    unittest.main()
