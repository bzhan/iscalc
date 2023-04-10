import unittest
from integral import series, parser
from integral.context import Context
from integral.parser import parse_expr
from integral.rules import FullSimplify
from integral.series import expand_series


class SeriesTest(unittest.TestCase):
    def testHeadTerm(self):
        data = [('sin(x) * exp(x)', 'x', ['1', '1']),
                ('sin(x) / exp(x)', 'x', ['1', '1']),
                ('log(x)', 'x', ['log(x)', '0']),
                # ('tan(x) - x', 'x', ['1/3', '3']),
                ('log(1/x)', 'x', ['-log(x)', '0']),
                ('log(1/x + (1/x)^(log(5)/log(3)))', 'x', ['-log(5)/log(3) * log(x)', '0']),
                ('exp(x*sin(x))', 'x', ['1', '0']),
                ('exp(sin(x+1))', 'x', ['exp(sin(1))', '0'])
                ]
        r = FullSimplify()
        ctx = Context()
        ctx.load_book('base')
        for e, v, res in data:
            e = parse_expr(e)
            ht = expand_series(e, v).head_term
            self.assertEqual(r.eval(ht[0], ctx), r.eval(parse_expr(res[0]),ctx))
            self.assertEqual(r.eval(ht[1], ctx), r.eval(parse_expr(res[1]),ctx))

