
import math
import sympy
from fractions import Fraction

from integral.expr import Expr, Var, Const
from integral.poly import normalize
from integral.context import Context

def is_rational(e: Expr) -> bool:
    """Detect rational functions in x."""
    if e.is_var() or e.is_const():
        return True
    elif e.is_op() and e.op in ('+', '-', '*', '/'):
        return all(is_rational(arg) for arg in e.args)
    elif e.is_op() and e.op == '^':
        return is_rational(e.args[0]) and e.args[1].is_const() and isinstance(e.args[1].val, int)
    else:
        return False

def convert_to_sympy(e: Expr):
    """Convert expression to sympy expression.
    
    Currently handle rational expressions only.
    
    """
    def rec(e: Expr):
        if e.is_var():
            return sympy.symbols(e.name)
        elif e.is_const():
            return e.val
        elif e.is_plus():
            return rec(e.args[0]) + rec(e.args[1])
        elif e.is_uminus():
            return -rec(e.args[0])
        elif e.is_minus():
            return rec(e.args[0]) - rec(e.args[1])
        elif e.is_times():
            return rec(e.args[0]) * rec(e.args[1])
        elif e.is_divides():
            return rec(e.args[0]) / rec(e.args[1])
        elif e.is_power():
            return rec(e.args[0]) ** rec(e.args[1])
        else:
            print('convert_to_sympy', e)
            raise NotImplementedError
    return rec(e)

def convert_from_sympy(e, ctx: Context) -> Expr:
    def rec(e):
        if isinstance(e, sympy.core.symbol.Symbol):
            return Var(e.name)
        elif isinstance(e, sympy.core.numbers.Integer):
            return Const(int(e))
        elif isinstance(e, sympy.core.numbers.Rational):
            return Const(Fraction(e.numerator, e.denominator))
        elif isinstance(e, sympy.core.add.Add):
            args = [rec(arg) for arg in e.args]
            return sum(args)
        elif isinstance(e, sympy.core.mul.Mul):
            args = [rec(arg) for arg in e.args]
            return math.prod(args)
        elif isinstance(e, sympy.core.power.Pow):
            return rec(e.args[0]) ** rec(e.args[1])
        else:
            print('convert_from_sympy', e)
            raise NotImplementedError
    return normalize(rec(e), ctx)

def partial_fraction(e: Expr, ctx: Context) -> Expr:
    return convert_from_sympy(sympy.apart(convert_to_sympy(e)), ctx)
