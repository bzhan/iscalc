import unittest

import integral.gruntz
from integral import series, parser
from integral.context import Context
from integral.expr import Op, Var, Const
from integral.gruntz import SubsSet, mrv, rewrite, dummy_var, limit_inf, mrv_lead_term
from integral.parser import parse_expr
from integral.rules import FullSimplify
from integral.series import expand_series


class GruntzTest(unittest.TestCase):
    def testDoSubs(self):
        s = SubsSet()
        e1 = parse_expr('exp(x)')
        e2 = parse_expr('exp(x+sin(x))')
        s[e1]
        s[e2]
        e = parse_expr('exp(x)  + exp(x+sin(x)) + 3')
        res = s.do_subs(e)
        print(res)

    def testRewrite1(self):
        x = 'x'
        ctx = Context()
        ctx.load_book('base')
        w = dummy_var()
        o = SubsSet()
        e = o[parse_expr("exp(x)")]
        res = rewrite(e, o, x, w, ctx)
        print(res) # 1/_d1

    def testMrv(self):

        x = 'x'
        ctx = Context()
        ctx.load_book('base')
        ctx.add_condition(Op('>', Var('x'), Const(1000000000000000)))
        test_data = [
            ("x", "_d1"),
            ('exp(x)', "_d3"),
            ('log(x)', "log(_d1)"),
            ('exp(x+exp(x^2))', "_d13"),
            ("(exp(x ^ 2) + x) / x ^ 2", "(_d3 + x) / x ^ 2"),
            ("exp(x^2)+x", "_d3 + x"),
            ("exp(x) + exp(-x) + exp(2*x)", "_d3 + _d10 + _d17"),
            ("exp(-x+exp(-x))", "_d15"),
            ("1/exp(-x+exp(-x))","1 / _d15"),
            ("1/exp(-x+exp(-x)) - exp(x)", "1 / _d15 - _d45"),
            ("exp(exp(-x/(1+exp(-x)))) * exp(-x / (1+exp(-x/(1+exp(-x))))) * exp(exp(-x+exp(-x/(1+exp(-x))))) / (exp(-x/(1+exp(-x))))^2 - exp(x)+x",\
             "exp(_d58) * _d143 * exp(_d599) / _d58 ^ 2 - _d764 + x"),
            ('(3^x - 2^x)/(x^2-x)', '(_d3 - _d10) / (x ^ 2 - x)'),
        ]
        for e, res in test_data:
            integral.gruntz.count = 0
            e = parse_expr(e)
            f, exps = mrv(e, x, ctx)
            # print(f)
            # print("--------------")
            # print(exps)
            self.assertEqual(str(exps), res)

    def testMrvLeadTerm(self):
        ctx = Context()
        ctx.load_book('base')
        ctx.add_condition(Op('>', Var('x'), Const(0)))
        test_data = [('x/log(x)', ['1/x', '-1'])]
        for a, b in test_data:
            c,d = mrv_lead_term(parse_expr(a), 'x', ctx)
            print(c,d)

    def test_limit_inf(self):
        ctx = Context()
        ctx.load_book('base')
        ctx.add_condition(Op('>', Var('x'), Const(0)))
        test_data = [
            # ('exp(x)', 'oo'),
            # ('(3^(1/x) - 2^(1/x))/((1/x)^2-(1/x))', 'log(2) - log(3)'),
            # ('(x^2-x) / (x^2+3*x -4)', '1'),
            # ('(exp(1/x - exp(-x)) - exp(1/x)) / exp(-x)', '-1'), # 8.1
            # ('(log(log(x) + log(log(x))) - log(log(x))) / log(log(x) + log(log(log(x)))) * log(x)', '1'), #8.19
            # ('exp(x)*(exp(1/x-exp(-x))-exp(1/x))', '-1'), # 8.1
            # ('exp(x) * (exp(1/x + exp(-x)+exp(-x^2))-exp(1/x-exp(-exp(x))))', '1') # 8.2
            # ("exp(exp(-x/(1+exp(-x)))) * exp(-x / (1+exp(-x/(1+exp(-x))))) * \ #issue
            # exp(exp(-x+exp(-x/(1+exp(-x))))) / (exp(-x/(1+exp(-x))))^2 - exp(x)+x", '2')
            ]
        for e, res in test_data:
            r = limit_inf(parse_expr(e), 'x', ctx)
            print(r)

    def test_limit_inf2(self):
        ctx = Context()
        ctx.load_book('base')
        test_data = [
            ("(exp(1/x - exp(-x)) - exp(1/x)) / exp(-x)", "-1"),
            ('(log(log(x) + log(log(x))) - log(log(x))) / log(log(x) + log(log(log(x)))) * log(x)', '1')
        ]
        from integral import limits
        for a, b in test_data:
            res = limits.limit_of_expr(parse_expr(a), 'x', ctx)
            print(res)



