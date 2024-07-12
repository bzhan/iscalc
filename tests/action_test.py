"""Unit test for integrals using internal language."""

import unittest
import lark

from integral import compstate
from integral import action
from integral import parser


class ActionTest(unittest.TestCase):
    def check_actions(self, base_file, current_file, actions, print_state=False):
        file = compstate.CompFile(base_file, current_file)
        ctx = file.get_context()

        state = action.InitialState(ctx)
        for act in actions:
            a = parser.parse_action(act)
            state = state.process_action(a)
        if print_state:
            print(state)
        self.assertTrue(state.is_finished())

    def testTongji(self):
        actions = [
            "calculate INT x:[2,3]. 2 * x + x ^ 2",
            "apply integral identity",
            "simplify"
        ]
        self.check_actions("base", "tongji", actions)

        actions = [
            "calculate INT x:[0,1]. (3 * x + 1) ^ (-2)",
            "substitute u for 3 * x + 1",
            "apply integral identity",
            "simplify"
        ]
        self.check_actions("base", "tongji", actions)

        actions = [
            "calculate INT x:[0,1]. exp(6 * x)",
            "apply integral identity",
            "simplify"
        ]
        self.check_actions("base", "tongji", actions)

        actions = [
            "calculate INT x:[-1,2]. x * exp(x)",
            "integrate by parts with u = x, v = exp(x)",
            "apply integral identity",
            "simplify",
        ]
        self.check_actions("base", "tongji", actions)

        actions = [
            "calculate INT x:[0,pi/4]. sin(x)",
            "apply integral identity",
            "simplify"
        ]
        self.check_actions("base", "tongji", actions)

        actions = [
            "calculate INT x:[0,1]. 3*x^2 - x + 1",
            "apply integral identity",
            "simplify"
        ]
        self.check_actions("base", "tongji", actions)

        actions = [
            "calculate INT x:[1,2]. x^2 + 1/x^4",
            "apply integral identity",
            "simplify"
        ]
        self.check_actions("base", "tongji", actions)

        actions = [
            "calculate INT x:[pi/3, pi]. sin(2*x + pi/3)",
            "substitute u for 2*x + pi/3",
            "apply integral identity",
            "simplify"
        ]
        self.check_actions("base", "tongji", actions)

        actions = [
            "calculate INT x:[4, 9]. x ^ (1 / 3) * (x ^ (1 / 2) + 1)",
            "expand polynomial",
            "apply integral identity",
            "simplify"
        ]
        self.check_actions("base", "tongji", actions)

        actions = [
            "calculate INT x:[-1, 0]. (3 * x ^ 4 + 3 * x ^ 2 + 1) / (x ^ 2 + 1)",
            "partial fraction decomposition",
            "apply integral identity",
            "simplify"
        ]
        self.check_actions("base", "tongji", actions)

        actions = [
            "calculate INT x:[4, exp(1) + 3]. (x ^ 3 - 12 * x ^ 2 - 42) / (x - 3)",
            "partial fraction decomposition",
            "apply integral identity",
            "simplify",
            "substitute u for x - 3",
            "apply integral identity",
            "expand polynomial",
            "simplify"
        ]
        self.check_actions("base", "tongji", actions)

        actions = [
            "calculate INT x:[0, pi / 2]. sin(x) * cos(x) ^ 3",
            "substitute u for cos(x)",
            "apply integral identity",
            "simplify"
        ]
        self.check_actions("base", "tongji", actions)

        actions = [
            
        ]

    def testChapter1Section5(self):
        actions = [
            "calculate INT x:[0,oo]. log(x) / (x ^ 2 + 1)",
            "split region at 1",
            "inverse substitute 1 / u for x creating u",
            "simplify",
            "rewrite u ^ 2 * (1 / u ^ 2 + 1) to u ^ 2 + 1",
            "simplify"
        ]
        self.check_actions("interesting", "chapter1section5", actions)


if __name__ == "__main__":
    unittest.main()
