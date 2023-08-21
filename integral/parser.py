"""Parsing"""

from typing import Dict, Optional, Tuple
from lark import Lark, Transformer, v_args, exceptions
from decimal import Decimal
from fractions import Fraction

from integral import expr
from integral.expr import Expr


grammar = r"""
    ?atom: CNAME -> var_expr
        | "?" CNAME  -> symbol_expr
        | INT -> int_expr
        | DECIMAL -> decimal_expr
        | "D" CNAME "." expr -> deriv_expr
        | "pi" -> pi_expr
        | "G" -> g_expr
        | "inf" -> pos_inf_expr
        | "oo" -> pos_inf_expr
        | "-inf" -> neg_inf_expr
        | "-oo" -> neg_inf_expr
        | CNAME "(" expr ("," expr)* ")" -> fun_expr
        | "(" expr ")"
        | "\|" expr "\|" -> abs_expr 
        | "INT" CNAME ":[" expr "," expr "]." expr -> integral_expr
        | "INT" CNAME "." expr -> indefinite_integral_expr
        | "INT" CNAME "[" CNAME ("," CNAME)* "]" "." expr -> indefinite_integral_skolem_expr
        | "[" expr "]_" CNAME "=" expr "," expr -> eval_at_expr
        | "LIM" "{" CNAME "->" expr "}" "." expr -> limit_inf_expr
        | "LIM" "{" CNAME "->" expr "-}" "."  expr -> limit_l_expr
        | "LIM" "{" CNAME "->" expr "+}" "."  expr -> limit_r_expr
        | "[" expr ("," expr)* "]" -> vector_expr
        | "$" CNAME -> type0_expr
        | "$" CNAME "(" expr ("," expr)* ")" -> type_expr

    ?uminus: "-" uminus -> uminus_expr | atom  // priority 80

    ?pow: pow "^" uminus -> pow_expr          // priority 75
        | "-" atom "^" uminus -> uminus_pow_expr
        | uminus

    ?times: times "*" pow -> times_expr        // priority 70
        | times "/" pow -> divides_expr 
        | times "%" pow -> modulo_expr
        | pow

    ?plus: plus "+" times -> plus_expr         // priority 65
        | plus "-" times -> minus_expr | times

    ?compare: plus "=" plus -> eq_expr              // priority 50
        | plus "!=" plus -> not_eq_expr
        | plus ">" plus -> greater_expr
        | plus "<" plus -> less_expr
        | plus ">=" plus -> greater_eq_expr
        | plus "<=" plus -> less_eq_expr
        | plus

    ?expr: compare
    !interval: ("(" | "[") expr "," expr ("]" | ")") -> interval_expr

    %import common.CNAME
    %import common.WS
    %import common.INT
    %import common.DECIMAL

    %ignore WS
"""

@v_args(inline=True)
class ExprTransformer(Transformer):
    def __init__(self):
        self.fixes: Optional[Dict[str, expr.Type]] = None

    def var_expr(self, s):
        s = str(s)
        if self.fixes is not None and s in self.fixes:
            return expr.Var(s, type=self.fixes[s])
        else:
            return expr.Var(s)

    def symbol_expr(self, s):
        return expr.Symbol(str(s), [expr.VAR, expr.CONST, expr.OP, expr.FUN])

    def int_expr(self, n):
        return expr.Const(int(n))

    def decimal_expr(self, n):
        return expr.Const(Decimal(n))

    def plus_expr(self, a, b):
        return expr.Op("+", a, b)

    def minus_expr(self, a, b):
        return expr.Op("-", a, b)

    def times_expr(self, a, b):
        return expr.Op("*", a, b)

    def divides_expr(self, a, b):
        if a.ty == expr.CONST and b.ty == expr.CONST:
            return expr.Const(Fraction(a.val) / Fraction(b.val))
        else:
            return expr.Op("/", a, b)

    def modulo_expr(self, a, b):
        if a.ty == expr.CONST and b.ty == expr.CONST and isinstance(a.val, int) and isinstance(b.val, int):
            return expr.Const(a.val % b.val)
        else:
            return expr.Op("%", a, b)

    def pow_expr(self, a, b):
        return expr.Op("^", a, b)

    def eq_expr(self, a, b):
        return expr.Op("=", a, b)

    def not_eq_expr(self, a, b):
        return expr.Op("!=", a, b)

    def less_expr(self, a, b):
        return expr.Op("<", a, b)

    def greater_expr(self, a, b):
        return expr.Op(">", a, b)

    def less_eq_expr(self, a, b):
        return expr.Op("<=", a, b)

    def greater_eq_expr(self, a, b):
        return expr.Op(">=", a, b)

    def uminus_expr(self, a):
        if a.is_const() and a.val > 0:
            return expr.Const(-a.val)
        else:
            return expr.Op("-", a)

    def uminus_pow_expr(self, a, b):
        return expr.Op("-", expr.Op("^", a, b))

    def pi_expr(self):
        return expr.pi

    def g_expr(self):
        return expr.G

    def pos_inf_expr(self):
        return expr.Inf(Decimal("inf"))
    def neg_inf_expr(self):
        return expr.Inf(Decimal("-inf"))

    def fun_expr(self, func_name, *args):
        if func_name == 'SKOLEM_CONST':
            return expr.SkolemFunc(str(args[0]), tuple())
        elif func_name == 'SKOLEM_FUNC':
            return expr.SkolemFunc(str(args[0].func_name), tuple(arg for arg in args[0].args))
        elif func_name == 'SUM':
            e = expr.Summation(str(args[0]), *args[1:])
            return e.replace(expr.Var(e.index_var), expr.Var(e.index_var, type=expr.IntType))
        return expr.Fun(str(func_name), *args)

    def abs_expr(self, expr):
        return expr.Fun("abs", expr)

    def deriv_expr(self, var, body):
        return expr.Deriv(str(var), body)

    def integral_expr(self, var, lower, upper, body):
        return expr.Integral(str(var), lower, upper, body)

    def indefinite_integral_expr(self, var, body):
        return expr.IndefiniteIntegral(str(var), body, tuple())

    def indefinite_integral_skolem_expr(self, *args):
        var = args[0]
        skolem_args = tuple(str(arg) for arg in args[1:-1])
        body = args[-1]
        return expr.IndefiniteIntegral(str(var), body, skolem_args)

    def eval_at_expr(self, body, var, lower, upper):
        return expr.EvalAt(var, lower, upper, body)

    def limit_inf_expr(self, var, lim, body):
        return expr.Limit(str(var), lim, body)

    def limit_l_expr(self, var, lim, body):
        return expr.Limit(str(var), lim, body, "-")

    def limit_r_expr(self, var, lim, body):
        return expr.Limit(str(var), lim, body, "+")

    def vector_expr(self, *args):
        data = []
        for arg in args:
            if isinstance(arg, expr.Matrix):
                data.append(arg.data)
            else:
                data.append(arg)
        return expr.Matrix(tuple(data))

    def type0_expr(self, name) -> expr.Type:
        return expr.Type(str(name))

    def type_expr(self, name, *args) -> expr.Type:
        return expr.Type(str(name), *args)


transformer = ExprTransformer()
expr_parser = Lark(grammar, start="expr", parser="lalr", transformer=transformer)

def parse_expr(s: str, *, fixes: Optional[Dict[str, expr.Type]] = None) -> Expr:
    """Parse an integral expression."""
    try:
        transformer.fixes = fixes
        res = expr_parser.parse(s)
        transformer.fixes = None
        return res
    except (exceptions.UnexpectedCharacters, exceptions.UnexpectedToken) as e:
        print("When parsing:", s)
        raise e
