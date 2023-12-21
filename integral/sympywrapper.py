import math
import sympy
from fractions import Fraction

from integral import expr
from integral.expr import Expr, Var, Const, Type

def is_rational(e: Expr) -> bool:
    """Detect rational functions in x."""
    if expr.is_var(e) or expr.is_const(e):
        return True
    elif expr.is_op(e) and e.op in ('+', '-', '*', '/'):
        return all(is_rational(arg) for arg in e.args)
    elif expr.is_op(e) and e.op == '^':
        return is_rational(e.args[0]) and expr.is_const(e.args[1]) and isinstance(e.args[1].val, int)
    else:
        return False


def convert_to_sympy(e: Expr):
    """Convert expression to sympy expression.
    
    Currently handle rational expressions only.
    
    """

    def rec(e: Expr):
        if expr.is_var(e):
            return sympy.symbols(e.name)
        elif expr.is_const(e):
            return e.val
        elif e.is_plus():
            return rec(e.args[0]) + rec(e.args[1])
        elif expr.is_uminus(e):
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

def convert_from_sympy(e) -> Expr:
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
    return rec(e)

def partial_fraction(e: Expr) -> Expr:
    return convert_from_sympy(sympy.apart(convert_to_sympy(e)))

def type_le(t1:Type, t2:Type):
    if t1 == expr.IntType and t2 in (expr.IntType, expr.RealType):
        return True
    elif t1 in (expr.RealType, expr.BoolType) and t2 == t1:
        return True
    elif expr.is_matrix_type(t1) and expr.is_matrix_type(t2):
        if not type_le(t1.eleType, t2.eleType):
            return False
        if not convert_to_sympy(t1.row) == convert_to_sympy(t2.row):
            return False
        if not convert_to_sympy(t1.col) == convert_to_sympy(t2.col):
            return False
        return True
    elif expr.is_fun_type(t1) and expr.is_fun_type(t2):
        n, m = len(t1.args), len(t2.args)
        if n != m:
            return False
        for i in range(n):
            if not type_le(t1.args[i], t2.args[i]):
                return False
        return True
    return False
