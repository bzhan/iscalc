import unittest
from fractions import Fraction

from integral import series, parser
from integral.context import Context
from integral.expr import Op, Var, Const
from integral.parser import parse_expr
from integral.rules import Simplify
from integral.series import expand_series


class SeriesTest(unittest.TestCase):
    def testHeadTerm(self):

        data = [
            ('sin(x) * exp(x)', 'x', ['1', '1']),
            ('sin(x) / exp(x)', 'x', ['1', '1']),
            ('log(x)', 'x', ['log(x)', '0']),
            # ('tan(x) - x', 'x', ['1/3', '3']), # issue
            ('log(1/x)', 'x', ['-log(x)', '0']),
            ('log(1/x + (1/x)^(log(5)/log(3)))', 'x', ['-log(5)/log(3) * log(x)', '0']),
            ('exp(x*sin(x))', 'x', ['1', '0']),
            ('exp(sin(x+1))', 'x', ['exp(sin(1))', '0']),
            ('log(log(1/x))', 'x', ['log(-log(x))', '0']),
            ('log(log(log(1 / x)) + 1 / x)', 'x', ['-log(x)', '0']),
            ('1/log(log(log(1 / x)) + 1 / x)', 'x', ['-1/log(x)', '0']),
            ('(log(log(1 / x) + 1 / x) - log(1 / x))', 'x', ['-log(x)', '1']),
            ('1/x*(log(log(1 / x) + 1 / x) - log(1 / x))', 'x', ['-log(x)', '0']),
            ('1/x*(log(log(1 / x) + 1 / x) - log(1 / x))/log(log(log(1 / x)) + 1 / x)', 'x', ['1', '0']),
            ]
        r = Simplify()
        ctx = Context()
        ctx.load_book('base')
        ctx.add_condition(Op('>', Var('x'), Const(0)))
        ctx.add_condition(Op('<', Var('x'), Const(Fraction(1, 1000000))))
        for e, v, res in data:
            e = parse_expr(e)
            s = expand_series(e, v)
            ht = s.head_term
            self.assertEqual(r.eval(ht.head_coff, ctx), r.eval(parse_expr(res[0]),ctx))
            self.assertEqual(r.eval(ht.head_power, ctx), r.eval(parse_expr(res[1]),ctx))




