"""Polynomials."""

from fractions import Fraction
from typing import Union, Dict, Tuple
import functools
import operator
import sympy
import math

from integral import expr, matrix, context
from integral.context import Context, apply_subterm



def collect_pairs(ps, ctx:Context):
    """
    Reduce a list of pairs by collecting into groups according to
    first components, and adding the second component for each group.

    It is assumed that the first components are hashable. The second
    components are either Expr, ConstantPolynomial, or numbers. Pairs
    whose second component equals zero are removed.

    e.g.    

    - [("x", 1), ("y", 2), ("x", 3)] => [("x", 4), ("y", 2)]
    - [("x", 1), ("x", -1), ("y", 1)] => [("y", 1)]

    """
    res = {}
    for v, c in ps:
        if v in res:
            res[v] += c
        else:
            res[v] = c
    
    def zero_for(v):
        if isinstance(v, expr.Expr):
            return expr.Const(0)
        elif isinstance(v, Polynomial):
            return Polynomial(tuple())
        elif isinstance(v, (int, Fraction)):
            return 0
        else:
            raise NotImplementedError

    res_list = []
    for k, v in res.items():
        if v != zero_for(v):
            res_list.append((k, v))
        else:
            # ([(v, 1)], 0) -> zero_matrix
            e = from_poly(Polynomial([Monomial(1, k)]))
            if expr.is_matrix_type(e.type):
                res_list.append((((expr.Fun(*ctx.get_func_type('zero_matrix', expr.num_row(e.type), expr.num_col(e.type))), 1),), 1))
    try:
        res = tuple(sorted(res_list))
    except:
        print(res_list)
        raise NotImplementedError
    return res


def collect_pairs_power(ps: Dict[expr.Expr, "Polynomial"], ctx: Context):
    res = {}
    res_list = []
    def is_non_negative(c: Polynomial):
        if c.is_fraction() and c.get_fraction() >= 0:
            return True
        e = from_poly(c)
        if expr.is_var(e) and ctx.is_not_negative(e):
            return True
        return False

    mat_list = []
    for v, c in ps:
        if expr.is_matrix_type(v.type):
            if mat_list != [] and mat_list[-1][0] == v:
                tmp = mat_list[-1]
                mat_list.pop()
                mat_list.append((tmp[0], (tmp[1] + c).reduce(ctx)))
            else:
                mat_list.append((v, c.reduce(ctx)))
        else:
            if v in res:
                if is_non_negative(c) and is_non_negative(res[v]):
                    res[v] += c
                    res[v].reduce(ctx)
                elif ctx.is_nonzero(v):
                    res[v] += c
                    res[v].reduce(ctx)
                else:
                    res_list.append((v, c))
            else:  # v not in res
                res[v] = c

    for v, c in res.items():
        if c != Polynomial(tuple()):
            res_list.append((v, c))
    return tuple(sorted(res_list) + mat_list)

def reduce_power(n: expr.Expr, e: "Polynomial") -> Tuple[Tuple[expr.Expr, "Polynomial"]]:
    """Reduce n ^ e to normal form.
    
    Returns a list of (n_i, e_i), so that n ^ e equals (n_1 ^ e^1) * ... (n_k ^ e_k).

    If n has type Expr, n ^ e is left unchanged. If n is an integer,
    it is factored to simplify the representation.

    """
    if expr.is_const(n) and isinstance(n.val, int) and e.is_fraction():
        if n.val >= 0:
            # Compute factors of n. Let n = (n_1 ^ e_1) * ... * (n_k ^ e_k), then
            # n ^ e = (n_1 ^ (e * e_1)) * ... * (n_k ^ (e * e_k)).
            return tuple((expr.Const(ni), e * ei) for ni, ei in sympy.factorint(n.val).items())
        else:
            # If n is negative, the denominator of e must be odd.
            # If the numerator of e is also odd, add an extra -1 factor.
            assert Fraction(e.get_fraction()).denominator % 2 == 1, \
                'reduce_power: exponent has even denominator'
            if Fraction(e.get_fraction()).numerator % 2 == 0:
                return tuple((expr.Const(ni), e * ei) for ni, ei in sympy.factorint(-n.val).items())
            else:
                return ((expr.Const(-1), constant(1)),) + tuple((expr.Const(ni), e * ei) for ni, ei in sympy.factorint(-n.val).items())
    else:
        return ((n, e),)

def extract_frac(ps: Tuple[Tuple[expr.Expr, "Polynomial"]]) -> Tuple[Tuple[Tuple[expr.Expr, "Polynomial"]], Fraction]:
    """Reduce (n_1 ^ e_1) * ... * (n_k ^ e_k) by extracting fractions.
    
    Collects the integer part of e_i into a separate coefficient. E.g.
    2 ^ (3/2) => 2 * 2^(1/2),
    2 ^ (-1/2) => 1/2 * 2^(1/2)
    
    """
    res = []
    coeff = 1

    for n, e in ps:
        if expr.is_const(n) and e.is_fraction():
            bval = n.val
            val = e.get_fraction()
            if val >= 1:
                coeff *= (bval ** math.floor(val))
            if val < 0:
                coeff *= Fraction(1, bval ** (-math.floor(val)))
            if val - math.floor(val) != 0:
                res.append((n, constant(val - math.floor(val))))
        else:
            res.append((n, e))

    return tuple(res), coeff


class Monomial:
    """Represents a monomial."""
    def __init__(self, coeff: Union[int, Fraction],
                 factors: Tuple[Tuple[expr.Expr, Union[int, Fraction, "Polynomial"]]]):
        """Construct a monomial from coefficient and tuple of factors,
        where each factor is associated its power. For example,

        (2, ()) -> 2
        (2, ((x, 1))) -> 2 * x
        (2, ((x, 2), (y, 1))) -> 2 * x^2 * y

        coeff: Union[int, Fraction] - coefficient of the monomial.

        """
        assert isinstance(coeff, (int, Fraction)), "Unexpected coeff: %s" % str(coeff)

        self.coeff = coeff

        # First, coerce type of exponent to Polynomial
        self.factors = []
        for base, power in factors:
            assert isinstance(base, expr.Expr)
            if isinstance(power, (int, Fraction)):
                power = constant(power)
            assert isinstance(power, Polynomial), "Unexpected power: %s" % str(power)
            self.factors.append((base, power))
        self.factors = tuple(self.factors)

    def reduce(self, ctx: Context) -> "Monomial":
        # Reduce power in factors
        reduced_factors = []
        for n, e in self.factors:
            e.reduce(ctx)
            reduced_factors.extend(reduce_power(n, e))

        # Here using collect power version
        self.factors = tuple((i, j) for i, j in collect_pairs_power(reduced_factors, ctx))

        # Extract fractions
        self.factors, coeff2 = extract_frac(self.factors)
        self.coeff = self.coeff * coeff2
        return self

    def __hash__(self):
        return hash(("MONO", self.coeff, self.factors))

    def __eq__(self, other):
        return isinstance(other, Monomial) and self.coeff == other.coeff and \
            self.factors == other.factors

    def __str__(self):
        res = ""
        if self.coeff != 1:
            res += str(self.coeff)
        for var, p in self.factors:
            s = str(var)
            if len(s) != 1:
                s = "(" + s + ")"
            if str(p) != "1":
                if isinstance(p, Fraction):
                    assert p.denominator != 0
                    if p.denominator == 1:
                        s = s + "^" + str(p.numerator)
                    else:
                        s = s + " ^ " + str(p)
                else:
                    s = s + "^" + str(p)
            if res:
                res += " * " + s
            else:
                res = s

        if res == "":
            res = "1"
        return res

    def __repr__(self):
        return "Monomial(%s)" % str(self)

    def __le__(self, other):
        if not isinstance(other, Monomial):
            raise TypeError
        return (self.factors, self.coeff) <= (other.factors, other.coeff)

    def __lt__(self, other):
        return self <= other and self != other

    def __mul__(self, other):
        if isinstance(other, (int, Fraction)):
            return Monomial(self.coeff * other, self.factors)
        elif isinstance(other, Monomial):
            return Monomial(self.coeff * other.coeff, self.factors + other.factors)
        else:
            raise NotImplementedError

    def __neg__(self):
        return Monomial(-self.coeff, self.factors)

    def __truediv__(self, other):
        if isinstance(other, Monomial):
            inv_factors = tuple((n, -e) for n, e in other.factors)
            return Monomial(Fraction(self.coeff) / other.coeff, self.factors + inv_factors)
        else:
            raise NotImplementedError

    def __pow__(self, exp):
        if isinstance(exp, int):
            return Monomial(Fraction(self.coeff) ** exp, [(n, e * exp) for n, e in self.factors])
        elif isinstance(exp, Fraction) and exp.denominator % 2 == 0:
            sqrt_factors = []
            for n, e in self.factors:
                if isinstance(n, expr.Expr) and e.is_fraction() and e.get_fraction() % 2 == 0:
                    sqrt_factors.append((expr.Fun('abs', n), e * exp))
                else:
                    sqrt_factors.append((n, e * exp))
            if self.coeff == 1:
                return Monomial(1, sqrt_factors)
            elif self.coeff < 0 and len(sqrt_factors) > 0:
                # Avoid taking square root of negative coefficient, move the negation
                # to the first sqrt_factor
                sqrt_factors = [(-sqrt_factors[0][0], sqrt_factors[0][1])] + sqrt_factors[1:]
                return Monomial(1, [(expr.Const(-self.coeff), exp)] + sqrt_factors)
            else:
                return Monomial(1, [(expr.Const(self.coeff), exp)] + sqrt_factors)
        elif isinstance(exp, Fraction) and exp.denominator % 2 == 1:
            factors = []
            for n, e in self.factors:
                factors.append((n, e * exp))
            if self.coeff == 1:
                return Monomial(1, factors)
            else:
                return Monomial(1, [(expr.Const(self.coeff), exp)] + factors)
        else:
            raise ValueError

    def is_constant(self) -> bool:
        return len(self.factors) == 0

    def has_matrix(self):
        if len(self.factors) > 0:
            for factor in self.factors:
                if expr.is_matrix_type(factor[0].type):
                    return True
        return False

    def get_constant(self) -> Union[int, Fraction]:
        if len(self.factors) == 0:
            return self.coeff
        else:
            raise AssertionError

    def is_fraction(self) -> bool:
        return len(self.factors) == 0

    def get_fraction(self) -> Union[int, Fraction]:
        return self.coeff


class Polynomial:
    """Represents a polynomial."""
    def __init__(self, monomials: Tuple[Monomial]):
        self.monomials = tuple(monomials)
        assert all(isinstance(mono, Monomial) for mono in self.monomials)

    def reduce(self, ctx: Context) -> "Polynomial":
        for mono in self.monomials:
            mono.reduce(ctx)
        assert all(isinstance(mono.coeff, (int, Fraction)) for mono in self.monomials)
        ts = collect_pairs([(mono.factors, mono.coeff) for mono in self.monomials], ctx)
        self.monomials = tuple(Monomial(coeff, factor) for factor, coeff in ts if coeff != 0)
        return self

    def __eq__(self, other):
        if isinstance(other, (int, Fraction)):
            return self.is_fraction() and self.get_fraction() == other

        return isinstance(other, Polynomial) and self.monomials == other.monomials

    def __le__(self, other):
        if not isinstance(other, Polynomial):
            raise TypeError
        return self.monomials <= other.monomials

    def __lt__(self, other):
        return self <= other and self != other

    def __hash__(self):
        return hash(("POLY", self.monomials))

    def __str__(self):
        if len(self.monomials) == 0:
            return "0"
        else:
            return " + ".join(str(mono) for mono in self.monomials)

    def __repr__(self):
        return "Polynomial(%s)" % str(self)

    def __len__(self):
        return len(self.monomials)

    def __add__(self, other):
        if not isinstance(other, Polynomial):
            raise TypeError
        return Polynomial(self.monomials + other.monomials)

    def __neg__(self):
        return Polynomial([-m for m in self.monomials])

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        if isinstance(other, (int, Fraction)):
            return Polynomial([m * other for m in self.monomials])
        elif isinstance(other, Polynomial):
            # Applies distributivity - could expand the number of terms exponentially
            return Polynomial([m1 * m2 for m1 in self.monomials for m2 in other.monomials])
        else:
            raise NotImplementedError

    def __truediv__(self, other):
        # Assume the denominator is a monomial
        if isinstance(other, Polynomial):
            if len(other.monomials) == 0:
                raise ZeroDivisionError
            elif len(other.monomials) == 1:
                return Polynomial([m / other.monomials[0] for m in self.monomials])
            else:
                raise ValueError
        else:
            raise NotImplementedError

    def __pow__(self, exp: "Polynomial") -> "Polynomial":
        # Assume self is a monomial and exp is a fraction
        if len(self.monomials) == 1 and isinstance(exp, (int, Fraction)):
            if self.monomials[0].has_matrix():
                pos = None
                for i in range(len(self.monomials[0].factors)):
                    if expr.is_matrix_type(self.monomials[0].factors[i][0].type):
                        pos = i
                        break
                if pos != None:
                    if type(exp) == int:
                        part1 = Monomial(self.monomials[0].coeff, self.monomials[0].factors[0:pos]) ** exp
                        part2 = Monomial(1, [(from_mono(Monomial(1, self.monomials[0].factors[pos:])), exp)])
                        return Polynomial([part1*part2])
                    else:
                        raise NotImplementedError
            return Polynomial([self.monomials[0] ** exp])
        else:
            raise ValueError('%s, %s' % (self, exp))

    def is_monomial(self) -> bool:
        return len(self.monomials) == 1

    def get_monomial(self) -> Monomial:
        if self.is_monomial():
            return self.monomials[0]
        else:
            raise AssertionError("get_monomial")

    def is_fraction(self) -> bool:
        if len(self.monomials) == 0:
            return True
        return self.is_monomial() and self.get_monomial().is_fraction()

    def get_fraction(self) -> Union[int, Fraction]:
        if len(self.monomials) == 0:
            return 0
        else:
            return self.get_monomial().get_fraction()
        
    def get_constant(self) -> Union[int, Fraction]:
        """If self is a constant, return the constant. Otherwise raise an exception."""
        if len(self.monomials) == 0:
            return 0
        elif len(self.monomials) == 1 and self.monomials[0].is_constant():
            return self.monomials[0].get_constant()
        else:
            raise AssertionError

    def is_one(self) -> bool:
        return len(self.monomials) == 1 and self.monomials[0].is_one()


def constant(c: Union[int, Fraction]) -> Polynomial:
    """Polynomial for c (numerical constant)."""
    return Polynomial([Monomial(c, tuple())])

def singleton(s: expr.Expr) -> Polynomial:
    """Polynomial for 1*s^1."""
    if expr.is_const(s):
        return constant(s.val)
    else:
        return Polynomial([Monomial(1, [(s, 1)])])


"""
Conversion from expressions to polynomials.
"""

def to_poly_r(e: expr.Expr, ctx: Context) -> Polynomial:
    """Convert expression to polynomial."""
    if expr.is_var(e):
        return singleton(e)

    elif e.is_plus():
        return to_poly(e.args[0], ctx) + to_poly(e.args[1], ctx)

    elif expr.is_uminus(e):
        return -to_poly(e.args[0], ctx)

    elif e.is_minus():
        return to_poly(e.args[0], ctx) - to_poly(e.args[1], ctx)

    elif e.is_times():
        a, b = to_poly(e.args[0], ctx), to_poly(e.args[1], ctx)
        if a.is_monomial() and b.is_monomial():
            return a * b
        elif (a.is_fraction() or b.is_fraction()) and \
                not expr.is_matrix_type(e.args[1].type) and \
                not expr.is_matrix_type(e.args[0].type):
            return a * b
        elif a.is_monomial():
            return a * singleton(from_poly(b))
        elif b.is_monomial():
            # do not swap a and b if they are both matrices
            if expr.is_matrix_type(e.args[0].type) and expr.is_matrix_type(e.args[1].type):
                return singleton(from_poly(a))*b
            return b * singleton(from_poly(a))
        else:
            return singleton(from_poly(a)) * singleton(from_poly(b))

    elif e.is_divides():
        a, b = to_poly(e.args[0], ctx), to_poly(e.args[1], ctx)
        if a.is_fraction() and a.get_fraction() == 0:
            return constant(0)
        elif b.is_fraction() and b.get_fraction() == 1:
            return a
        elif a.is_monomial() and b.is_monomial():
            return a / b
        elif a.is_monomial():
            return a / singleton(from_poly(b))
        elif b.is_monomial():
            return singleton(from_poly(a)) / b
        else:
            return singleton(from_poly(a)) / singleton(from_poly(b))

    elif e.is_power():
        a, b = to_poly(e.args[0], ctx), to_poly(e.args[1], ctx)
        if a.is_fraction() and a.get_fraction() == 0:
            return singleton(expr.Const(0))
        elif a.is_fraction() and a.get_fraction() == 1:
            return singleton(expr.Const(1))
        elif a.is_monomial() and b.is_fraction():
            return a ** b.get_fraction()
        elif b.is_fraction():
            return Polynomial([Monomial(1, [(from_poly(a), b.get_fraction())])])
        else:
            return Polynomial([Monomial(1, [(from_poly(a), b)])])

    elif expr.is_fun(e) and e.func_name == "exp":
        a = e.args[0]
        # exp(matrix)
        if expr.is_matrix_type(a.type):
            return singleton(expr.Fun(*ctx.get_func_type('exp', from_poly(to_poly(a, ctx)))))
        elif expr.is_fun(a) and a.func_name == "log":
            return to_poly(a.args[0], ctx)
        else:
            return Polynomial([Monomial(1, [(expr.E, to_poly(a, ctx))])])

    elif expr.is_fun(e) and e.func_name in ("sin", "cos", "tan", "cot", "csc", "sec"):
        a = e.args[0]
        if expr.is_fun(a) and a.func_name == "a" + e.func_name:
            # sin(asin(x)) = x
            return to_poly(a.args[0], ctx)
        else:
            tmp = normalize(a, ctx)
            if e.func_name == "cos" and expr.is_uminus(tmp):
                return singleton(expr.Fun(e.func_name, tmp.args[0]), )
            else:
                return singleton(expr.Fun(e.func_name, tmp))

    elif expr.is_fun(e) and e.func_name in ("asin", "acos", "atan", "acot", "acsc", "asec"):
        a, = e.args
        if e.func_name in ("atan", "acot", "acos") and expr.is_fun(a) and a.func_name == e.func_name[1:]:
            # TODO: determine domain range of cos(x)
            # atan(tan(x)) = x
            return to_poly(a.args[0], ctx)
        else:
            return singleton(expr.Fun(e.func_name, normalize(a, ctx)))

    elif expr.is_fun(e) and e.func_name == "sqrt":
        return to_poly(expr.Op("^", e.args[0], expr.Const(Fraction(1, 2))), ctx)

    elif expr.is_fun(e):
        args_norm = [normalize(arg, ctx) for arg in e.args]
        return singleton(expr.Fun((e.func_name, e.func_type), *args_norm))

    elif expr.is_evalat(e):
        if e.upper == expr.POS_INF:
            upper = expr.Limit(e.var, expr.POS_INF, e.body, var_type=e.var_type)
        elif e.upper == expr.NEG_INF:
            x = expr.Var(e.var)
            upper = expr.Limit(e.var, expr.POS_INF, e.body.subst(e.var, -x), var_type=e.var_type)
        else:
            try:
                upper = normalize(e.body.subst(e.var, e.upper), ctx)
            except:
                x = expr.Var(e.var)
                a = e.upper
                upper = expr.Limit(e.var, expr.POS_INF, e.body.subst(e.var, a - 1 / x), var_type=e.var_type)

        if e.lower == expr.POS_INF:
            lower = expr.Limit(e.var, expr.POS_INF, e.body, var_type=e.var_type)
        elif e.lower == expr.NEG_INF:
            x = expr.Var(e.var)
            lower = expr.Limit(e.var, expr.POS_INF, e.body.subst(e.var, -x), var_type=e.var_type)
        else:
            try:
                lower = normalize(e.body.subst(e.var, e.lower), ctx)
            except:
                x = expr.Var(e.var)
                a = e.lower
                lower = expr.Limit(e.var, expr.POS_INF, e.body.subst(e.var, a + 1 / x), var_type=e.var_type)
        return to_poly(normalize(upper, ctx) - normalize(lower, ctx), ctx)

    elif expr.is_integral(e):
        ctx2 = context.body_conds(e, ctx)
        body = normalize(e.body, ctx2)
        l, h = normalize(e.lower, ctx), normalize(e.upper, ctx)

        if l.is_evaluable() and h.is_evaluable() :
            ll, hh = expr.eval_expr(l), expr.eval_expr(h)
            if ll > hh:
                return singleton(-expr.Integral(e.var, h, l, body))
        return singleton(expr.Integral(e.var, normalize(e.lower, ctx), normalize(e.upper, ctx), body))
    elif expr.is_limit(e):
        ctx2 = context.body_conds(e,ctx)
        return singleton(expr.Limit(e.var, normalize(e.lim, ctx), normalize(e.body, ctx2), var_type=e.var_type))
    elif expr.is_inf(e):
        if e == expr.POS_INF:
            return singleton(e)
        else:
            return -singleton(expr.POS_INF)
    elif expr.is_indefinite_integral(e):
        return singleton(expr.IndefiniteIntegral(e.var, normalize(e.body, ctx), e.skolem_args))

    elif expr.is_summation(e):
        l, u = normalize(e.lower, ctx), normalize(e.upper, ctx)
        if l == u:
            return to_poly(e.body.subst(e.index_var, l), ctx)
        ctx2 = context.body_conds(e, ctx)
        return singleton(expr.Summation(e.index_var, normalize(e.lower, ctx),
                                        normalize(e.upper, ctx), normalize(e.body, ctx2)))
    elif expr.is_product(e):
        l, u = normalize(e.lower, ctx), normalize(e.upper, ctx)
        if l == u:
            return to_poly(e.body.subst(e.index_var, l), ctx)
        ctx2 = context.body_conds(e, ctx)
        return singleton(expr.Product(e.index_var, l, u, normalize(e.body, ctx2)))
    elif expr.is_matrix(e):
        res_data = [[normalize(item, ctx) for item in rv] for rv in e.data]
        return singleton(expr.Matrix(res_data, e.type))
    elif expr.is_deriv(e):
        return singleton(expr.Deriv(e.var, normalize(e.body, ctx)))
    else:
        return singleton(e)

def to_poly(e: expr.Expr, ctx: Context) -> Polynomial:
    return to_poly_r(e, ctx).reduce(ctx)

def function_eval(e: expr.Expr, ctx: Context) -> expr.Expr:
    if expr.is_fun(e) and e.func_name == "binom":
        if expr.is_const(e.args[0]) and expr.is_const(e.args[1]):
            return expr.Const(math.comb(e.args[0].val, e.args[1].val))

    if expr.is_fun(e) and e.func_name == 'factorial':
        if expr.is_const(e.args[0]) and abs(round(e.args[0].val) - e.args[0].val) < 1e-15 and round(e.args[0].val) >= 0:
            return expr.Const(math.factorial(round(e.args[0].val)))

    if expr.is_fun(e) and e.func_name == 'floor':
        if expr.is_inf(e.args[0]):
            return e.args[0]
    if expr.is_fun(e) and e.func_name == 'ccon':
        assert len(e.args) == 2, "wrong number of ccon arguments"
        a, b = (function_eval(arg, ctx) for arg in e.args)
        if expr.is_matrix_type(a.type) and expr.is_matrix_type(b.type):
            assert expr.num_row(a.type) == expr.num_row(b.type), \
                "two matrices can not be concatenated by column as they have a different row number"
            res_type = expr.MatrixType(expr.type_mapping[(a.type.args[0], b.type.args[0])],
                                       expr.num_row(a.type),
                                       normalize(expr.num_col(a.type) + expr.num_col(b.type), ctx))
            if not expr.is_matrix(a) and not expr.is_matrix(b):
                res_data = [[a, b]]
                res = expr.Matrix(res_data, res_type)
                return res
            elif expr.is_matrix(a) and expr.is_matrix(b):
                res_data = a.data
                for i, row in enumerate(b.data):
                    for item in row:
                        res_data[i].append(item)
                res = expr.Matrix(res_data, res_type)
                return res


    if expr.is_fun(e) and e.func_name == 'rcon':
        assert len(e.args) == 2, "wrong number of rcon arguments"
        a, b = (function_eval(arg, ctx) for arg in e.args)
        if expr.is_matrix_type(a.type) and expr.is_matrix_type(b.type):
            assert expr.num_col(a.type) == expr.num_col(b.type), \
                f"two matrices can not be concatenated by row as they have a different column number:\n" \
                f"%s[%s], %s[%s]" %\
                (str(a),str(a.type),str(b),str(b.type))
            res_type = expr.MatrixType(expr.type_mapping[(a.type.args[0], b.type.args[0])],
                                       normalize(expr.num_row(a.type) + expr.num_row(b.type), ctx),
                                       expr.num_col(a.type))
            if not expr.is_matrix(a) and not expr.is_matrix(b):
                res_data = [[a], [b]]
                res = expr.Matrix(res_data, res_type)
                return res
            elif expr.is_matrix(a) and expr.is_matrix(b):
                res_data = list(a.data)+ list(b.data)
                res = expr.Matrix(res_data, res_type)
                return res

    if expr.is_fun(e) and e.func_name == 'sin':
        a = e.args[0]
        if expr.is_uminus(a):
            return -expr.Fun('sin', a.args[0])
    if expr.is_fun(e) and e.func_name == 'hat':
        a = e.args[0]
        t = a.type
        if expr.is_fun(a) and a.func_name == 'zero_matrix' and expr.eval_expr(t.args[1]) == 3 \
            and expr.eval_expr(t.args[2]) == 1:
            return expr.Fun(*ctx.get_func_type('zero_matrix', expr.Const(3), expr.Const(3)))
    return e

def function_table(e: expr.Expr, ctx: Context) -> expr.Expr:
    if not expr.is_fun(e) or len(e.args) != 1:
        return e

    func_table = ctx.get_function_tables()
    if not e.func_name in func_table:
        return e
    if not e.args[0].is_constant():
        return e
    if e.args[0] in func_table[e.func_name]:
        return func_table[e.func_name][e.args[0]]
    else:
        return e

def simplify_identity(e: expr.Expr, ctx: Context) -> expr.Expr:
    for identity in ctx.get_simp_identities():
        inst = expr.match(e, identity.lhs)
        if inst is not None:
            # Check conditions
            satisfied = True
            for cond in identity.conds.data:
                cond = expr.expr_to_pattern(cond)
                cond = cond.inst_pat(inst)
                if not ctx.check_condition(cond):
                    satisfied = False
            if satisfied:
                return identity.rhs.inst_pat(inst)
    return e

def simp_matrix(e: expr.Expr, ctx: Context) -> expr.Expr:
    """Simplification of matrix expressions.
    
    We currently perform the following simplifications:
    * A ^ 0 = 0
    * A ^ 1 = A

    """
    if expr.is_op(e):
        if e.is_power():
            a, b = e.args
            if expr.is_matrix_type(a.type):
                nb = normalize(b, ctx)
                if nb == expr.Const(0):
                    return expr.Fun(*ctx.get_func_type("unit_matrix", expr.num_row(a.type)))
                elif nb == expr.Const(1):
                    return a
                elif expr.is_fun(a) and a.func_name == 'unit_matrix' and \
                    b.type == expr.IntType and ctx.check_condition(expr.Op('>=', b, expr.Const(0))):
                    return a
        elif e.is_plus() and expr.is_fun(e.args[1]) and e.args[1].func_name == 'zero_matrix':
            return e.args[0]
        elif e.is_times():
            # eliminate unit matrix
            a, b = e.args
            e = simp_matrix(a, ctx) * simp_matrix(b, ctx)
            factors = []
            def get_all_factor(e):
                nonlocal factors
                if e.is_times():
                    a,b = e.args
                    get_all_factor(a)
                    get_all_factor(b)
                else:
                    factors.append(e)
            get_all_factor(e)
            # simp inv(p) * p = unit matrix
            first = True
            tmp = []
            for i in range(len(factors)):
                if first:
                    first = False
                    tmp.append(factors[i])
                else:
                    a = factors[i]
                    b = factors[i-1]
                    if expr.is_fun(a) and a.func_name == 'inv' and a.args[0] == b:
                        tmp.pop()
                        tmp.append(expr.Fun(*ctx.get_func_type('unit_matrix', expr.num_row(b.type))))
                    elif expr.is_fun(b) and b.func_name == 'inv' and b.args[0] == a:
                        tmp.pop()
                        tmp.append(expr.Fun(*ctx.get_func_type('unit_matrix', expr.num_row(a.type))))
                    else:
                        tmp.append(a)

            factors = tmp
            has_zero_matrix = False
            all_mat_factors = []
            nonunit_mat_factors = []
            scalar_factors = []
            for factor in factors:
                if expr.is_matrix_type(factor.type):
                    all_mat_factors.append(factor)
                    if expr.is_fun(factor) and factor.func_name == 'unit_matrix':
                        continue
                    if expr.is_fun(factor) and factor.func_name == 'zero_matrix':
                        has_zero_matrix = True
                    nonunit_mat_factors.append(factor)
                else:
                    scalar_factors.append(factor)

            if has_zero_matrix:
                row, col = expr.num_row(all_mat_factors[0].type), expr.num_col(all_mat_factors[-1].type)
                return expr.Fun(*ctx.get_func_type("zero_matrix", row, col))
            else:
                all_factors = scalar_factors + nonunit_mat_factors
                if len(nonunit_mat_factors) == 0 and len(all_mat_factors) != 0:
                    row, col = expr.num_row(all_mat_factors[0].type), expr.num_col(all_mat_factors[-1].type)
                    all_factors.append(expr.Fun(*ctx.get_func_type("unit_matrix", row)))
                res = all_factors[0]
                for factor in all_factors[1:]:
                    res = expr.Op('*', res, factor)
                return res

    if expr.is_matrix(e):
        a = expr.Symbol('a', [expr.VAR, expr.CONST, expr.OP, expr.FUN], type=expr.IntType)
        b = expr.Symbol('b', [expr.VAR, expr.CONST, expr.OP, expr.FUN], type=expr.IntType)
        pat_data = [[expr.Fun(*ctx.get_func_type('unit_matrix', a)), expr.Fun(*ctx.get_func_type('zero_matrix', a, b))],
                    [expr.Fun(*ctx.get_func_type('zero_matrix', b, a)), expr.Fun(*ctx.get_func_type('unit_matrix', b))]]
        pat = expr.Matrix(pat_data)
        inst = expr.match(e, pat)
        if inst != None:
            dim = normalize(expr.Op('+', a, b).inst_pat(inst), ctx)
            return expr.Fun(*ctx.get_func_type('unit_matrix', dim))

    return e

def simplify_scalar_multiply(e: expr.Expr, ctx:Context) -> expr.Expr:
    if e.is_times():
        a, b = e.args
        if not expr.is_matrix_type(a.type) and expr.is_matrix(b):
            res_type = expr.MatrixType(expr.type_mapping[(b.type.eleType, a.type)],
                                       expr.num_row(b.type),
                                       expr.num_col(b.type))
            return expr.Matrix([[from_poly(to_poly(a*item, ctx)) for item in r] for r in b.data], res_type)
        elif not expr.is_matrix_type(b.type) and expr.is_matrix(a):
            res_type = expr.MatrixType(expr.type_mapping[(a.type.eleType, b.type)],
                                       expr.num_row(a.type),
                                       expr.num_col(a.type))
            return expr.Matrix([[from_poly(to_poly(b * item, ctx)) for item in r] for r in a.data], res_type)
    elif expr.is_uminus(e):
        a = e.args[0]
        if expr.is_matrix(a):
            # concrete matrix
            return expr.Matrix([[from_poly(to_poly(-item, ctx)) for item in r] for r in a.data], a.type)
        elif expr.is_matrix_type(a.type):
            # matrix typed expression
            if expr.is_fun(a) and a.func_name == 'zero_matrix':
                # -zero_matrix(a,b) ==> zero_matrix(a,b)
                return a
    return e

def simplify_matrix_multiply(e: expr.Expr, ctx: Context):
    if e.is_times():
        a, b = e.args
        if expr.is_matrix(a) and expr.is_matrix(b):
            return matrix.multiply(a, b, ctx)
    return e

def simplify_matrix_add(e: expr.Expr, ctx: Context):
    if e.is_plus():
        a, b = e.args
        if expr.is_matrix(a) and expr.is_matrix(b):
            if not expr.is_matrix_type(a.type):
                raise AssertionError
            if not expr.is_matrix_type(b.type):
                raise AssertionError
            assert expr.num_col(a.type) == expr.num_col(b.type) and \
                expr.num_row(a.type) == expr.num_row(b.type)
            return matrix.add(a, b, ctx)
        elif expr.is_matrix_type(a.type) and expr.is_matrix_type(b.type):
            if expr.is_fun(a) and a.func_name == 'zero_matrix':
                assert expr.num_col(a.type) == expr.num_col(b.type)
                assert expr.num_row(a.type) == expr.num_row(b.type)
                return b
            if expr.is_fun(b) and b.func_name == 'zero_matrix':
                assert expr.num_col(a.type) == expr.num_col(b.type)
                assert expr.num_row(a.type) == expr.num_row(b.type)
                return a

    elif e.is_minus():
        a, b = e.args
        if expr.is_matrix(a) and expr.is_matrix(b):
            assert expr.num_col(a.type) == expr.num_col(b.type) and \
                   expr.num_row(a.type) == expr.num_row(b.type)
            return matrix.minus(a, b, ctx)
    return e

def simplify_eq(e: expr.Expr, ctx: Context) -> expr.Expr:
    if not expr.is_var(e):
        return e

    for eq in ctx.get_conds().data:
        if eq.is_equals() and e == eq.lhs and eq.rhs.is_constant():
            return eq.rhs
    return e

def simplify_limit(e: expr.Expr, ctx: Context) -> expr.Expr:
    from integral import limits
    if not expr.is_limit(e):
        return e
    if e.var not in e.body.get_vars():
        return e.body

    if e.lim == expr.POS_INF:
        return limits.reduce_inf_limit(e.body, e.var, ctx)
    elif e.lim == expr.NEG_INF:
        raise limits.reduce_neg_inf_limit(e.body, e.var, ctx)
    else:
        return limits.reduce_finite_limit(e, ctx)

def simplify_integral(e: expr.Expr, ctx: Context) -> expr.Expr:
    if not expr.is_integral(e):
        return e

    if expr.is_deriv(e.body) and e.body.var == e.var:
        return expr.EvalAt(e.var, e.lower, e.upper, e.body.body)
    elif e.lower == e.upper:
        return expr.Const(0)
    else:
        return e

def simplify_power(e: expr.Expr, ctx: Context) -> expr.Expr:
    if not e.is_power():
        return e
    if e.args[1].is_plus() and expr.is_const(e.args[0]) and expr.is_const(e.args[1].args[1]):
        # c1 ^ (a + c2) => c1 ^ c2 * c1 ^ a
        return (e.args[0] ^ e.args[1].args[1]) * (e.args[0] ^ e.args[1].args[0])
    elif e.args[1].is_minus() and expr.is_const(e.args[0]) and expr.is_const(e.args[1].args[1]):
        # c1 ^ (a - c2) => c1 ^ -c2 * c1 ^ a
        return (e.args[0] ^ e.args[1].args[0]) * (e.args[0] ^ (-(e.args[1].args[1])))
    elif expr.is_uminus(e.args[0]):
        if expr.is_const(e.args[1]):
            # (-a) ^ n = (-1) ^ n * a ^ n
            return (expr.Const(-1) ^ e.args[1]) * (e.args[0].args[0] ^ e.args[1])
        elif normalize(e.args[1] / expr.Const(2), ctx).type == expr.IntType:
            return e.args[0].args[0] ^ e.args[1]
        else:
            return e
    elif e.args[0].is_minus() and expr.is_uminus(e.args[0].args[0]) and expr.is_const(e.args[1]):
        # (-a - b) ^ n = (-1) ^ n * (a + b) ^ n
        nega, negb = e.args[0].args
        return (expr.Const(-1) ^ e.args[1]) * ((nega.args[0] + negb) ^ e.args[1])
    else:
        return e

def simplify_trig(e: expr.Expr, ctx: Context) -> expr.Expr:
    if not (expr.is_fun(e) and e.func_name in ('sin', 'cos', 'tan', 'cot', 'csc', 'sec')):
        return e

    a = e.args[0]
    c = expr.Symbol('c', [expr.CONST], type=expr.RealType)
    d = expr.Symbol('d', [expr.CONST], type=expr.RealType)

    # Find constant coefficient of a
    coeff = None
    if expr.match(a, c * expr.pi):
        coeff = a.args[0].val
    elif expr.match(a, c * expr.pi / d):
        coeff = Fraction(a.args[0].args[0].val, a.args[1].val)
    elif expr.match(a, expr.pi / d):
        coeff = Fraction(1, a.args[1].val)
    elif expr.match(a, -(c * expr.pi)):
        coeff = -a.args[0].args[0].val
    elif expr.match(a, -(c * expr.pi / d)):
        coeff = Fraction(-a.args[0].args[0].args[0].val, a.args[0].args[1].val)
    elif expr.match(a, -(expr.pi / d)):
        coeff = Fraction(-1, a.args[0].args[1].val)
    elif a == -expr.pi:
        coeff = -1

    if coeff is None:
        return e

    # Normalize coefficient to the interval (-1, 1]
    n = int(coeff)
    if n % 2 == 0:
        coeff = coeff - n
    elif n > 0:
        coeff = coeff - (n + 1)
    else:
        coeff = coeff - (n - 1)

    def build(val):
        if isinstance(val, int):
            return expr.Fun(e.func_name, expr.Const(val) * expr.pi)
        elif isinstance(val, Fraction):
            return expr.Fun(e.func_name, expr.Const(val.numerator) * expr.pi / expr.Const(val.denominator))
        else:
            raise TypeError

    # Further normalize to [0, pi]
    if coeff < 0:
        if e.func_name in ('sin', 'tan', 'cot', 'csc'):
            return -build(-coeff)
        else:  # cos, sec: does not change sign
            return build(-coeff)
    else:
        return build(coeff)

def simplify_log(e: expr.Expr, ctx: Context) -> expr.Expr:
    if not (expr.is_fun(e) and e.func_name == 'log'):
        return e
    
    a = e.args[0]
    if not a.is_constant():
        return e

    if expr.is_const(a) and isinstance(a.val, int):
        int_factors = sympy.factorint(a.val)
        log_ints = []
        for b, e in int_factors.items():
            if e != 1:
                log_ints.append(e * expr.log(expr.Const(b)))
            else:
                log_ints.append(expr.log(expr.Const(b)))
            return sum(log_ints[1:], log_ints[0])
    elif expr.is_const(a) and isinstance(a.val, Fraction):
        return expr.log(expr.Const(a.val.numerator)) - expr.log(expr.Const(a.val.denominator))
    elif a.is_times():
        return expr.log(a.args[0]) + expr.log(a.args[1])
    elif a.is_divides():
        return expr.log(a.args[0]) - expr.log(a.args[1])
    elif expr.is_fun(a) and a.func_name == 'sqrt':
        return expr.log(a.args[0]) / 2
    else:
        return e

def simplify_sqrt(e: expr.Expr, ctx: Context) -> expr.Expr:
    if not (expr.is_fun(e) and e.func_name == 'sqrt'):
        return e

    if e.args[0] == expr.Const(0):
        return expr.Const(0)
    if e.args[0] == expr.Const(1):
        return expr.Const(1)
    if e.args[0] == expr.Const(4):
        return expr.Const(2)
    if e.args[0] == expr.Const(Fraction(1, 4)):
        return expr.Const(Fraction(1, 2))
    if e.args[0] == expr.Const(Fraction(1, 2)):
        return 1 / expr.sqrt(expr.Const(2))

    return e

def simplify_sum(e: expr.Expr, ctx:Context) -> expr.Expr:
    if expr.is_summation(e):
        if e.lower == e.upper and e.lower not in (expr.POS_INF, expr.NEG_INF):
            return e.body
        if e.body == expr.Const(0):
            return e.body
    elif e.is_plus():
        a = expr.Symbol('a',[expr.SUMMATION])
        b = expr.Symbol('b',[expr.SUMMATION])
        pat_list = [a+b, -(a)+b, a - b, -(a) - b]
        for pat in pat_list:
            inst = expr.match(e, pat)
            if inst != None:
                tmpa:expr.Summation = a.inst_pat(inst)
                tmpb:expr.Summation = b.inst_pat(inst)
                al, bl, au, bu, av, bv = tmpa.lower,tmpb.lower,tmpa.upper,tmpb.upper, tmpa.index_var, tmpb.index_var
                ab, bb = tmpa.body, tmpb.body
                if al == bl and au == bu and ab == bb:
                    new_inst = {'a':ab, 'b':bb}
                    new_body = pat.inst_pat(new_inst)
                    return expr.Summation(av, al, au, new_body)
    return e

def simplify_inf(e: expr.Expr, ctx: Context) -> expr.Expr:
    if e.is_plus():
        if e.args[0] == expr.POS_INF and e.args[1].is_constant():
            return e.args[0]
    elif e.is_minus():
        if e.args[0] == expr.POS_INF and e.args[1].is_constant():
            return e.args[0]
    elif e.is_divides():
        if e.args[0] == expr.POS_INF and e.args[1].is_constant():
            if expr.eval_expr(e) != 0:
                return e.args[0]
    return e

def normal_const(e:expr.Expr, ctx:Context):
    if e.is_constant():
        return normalize(e, ctx)
    elif expr.is_var(e) or expr.is_inf(e) or expr.is_skolem_func(e):
        return e
    elif expr.is_op(e):
        return expr.Op(e.op, *[normal_const(arg, ctx) for arg in e.args])
    elif expr.is_fun(e):
        return expr.Fun((e.func_name, e.func_type), *[normal_const(arg, ctx) for arg in e.args])
    elif expr.is_summation(e):
        return expr.Summation(e.index_var, normal_const(e.lower,ctx), \
                              normal_const(e.upper,ctx), normal_const(e.body,ctx))
    elif expr.is_limit(e):
        return expr.Limit(e.var, normal_const(e.lim, ctx), normal_const(e.body, ctx), var_type=e.var_type)
    elif expr.is_integral(e):
        e:expr.Integral
        return expr.Integral(e.var, normal_const(e.lower,ctx), normal_const(e.upper,ctx),\
                             normal_const(e.body,ctx))
    raise NotImplementedError(str(e))

def normalize(e: expr.Expr, ctx: Context) -> expr.Expr:
    if e.is_equals():
        return expr.Eq(normalize(e.lhs, ctx), normalize(e.rhs, ctx))

    if expr.is_const(e):
        return e
    for i in range(5):
        old_e = e
        e = from_poly(to_poly(e, ctx))
        e = apply_subterm(e, simp_matrix, ctx)
        e = apply_subterm(e, simplify_scalar_multiply, ctx)
        e = apply_subterm(e, simplify_matrix_multiply, ctx)
        e = apply_subterm(e, simplify_matrix_add, ctx)
        e = apply_subterm(e, function_table, ctx)
        e = apply_subterm(e, function_eval, ctx)
        e = apply_subterm(e, simplify_identity, ctx)
        e = apply_subterm(e, simplify_eq, ctx)
        e = apply_subterm(e, simplify_limit, ctx)
        e = apply_subterm(e, simplify_integral, ctx)
        e = apply_subterm(e, simplify_power, ctx)
        e = apply_subterm(e, simplify_trig, ctx)
        e = apply_subterm(e, simplify_log, ctx)
        e = apply_subterm(e, simplify_sqrt, ctx)
        e = apply_subterm(e, simplify_inf, ctx)
        e = apply_subterm(e, simplify_sum, ctx)
        if e == old_e:
            break

    return e

"""
Conversion from polynomials to terms.
"""

def rsize(e: expr.Expr) -> int:
    """Find size of term without constants."""
    if expr.is_const(e):
        return 0
    elif expr.is_uminus(e):
        return rsize(e.args[0])
    elif e.is_times():
        return rsize(e.args[0]) + e.args[1].size() + 1
    else:
        return e.size()

def display_large(e: expr.Expr) -> bool:
    """Determine whether the expression requires large display."""
    def pred(e: expr.Expr) -> bool:
        return expr.is_integral(e) or e.is_divides() or (expr.is_fun(e) and e.func_name == "binom")
    return len(e.find_subexpr_pred(pred)) > 0

def from_mono(m: Monomial) -> expr.Expr:
    """Convert a monomial to an expression."""
    sign = 1
    num_factors = []
    denom_factors = []
    if isinstance(m.coeff, int) or (isinstance(m.coeff, Fraction) and m.coeff.denominator == 1):
        if m.coeff == 1:
            pass
        elif m.coeff == -1:
            sign = -1
        elif m.coeff >= 0:
            num_factors.append(expr.Const(m.coeff))
        else:
            sign = -1
            num_factors.append(expr.Const(-m.coeff))
    elif isinstance(m.coeff, Fraction):
        denom_factors.append(expr.Const(m.coeff.denominator))
        if m.coeff.numerator == 1:
            pass
        elif m.coeff.numerator == -1:
            sign = -1
        elif m.coeff.numerator >= 0:
            num_factors.append(expr.Const(m.coeff.numerator))
        else:
            sign = -1
            num_factors.append(expr.Const(-m.coeff.numerator))
    else:
        raise TypeError

    for base, power in m.factors:
        if isinstance(power, Polynomial) and power.is_fraction():
            power = power.get_fraction()
        if isinstance(base, expr.Expr) and base == expr.E:
            if isinstance(power, Polynomial):
                num_factors.append(expr.exp(from_poly(power)))
            else:
                num_factors.append(expr.exp(expr.Const(power)))
        else:
            if power == 1:
                num_factors.append(base)
            elif power == Fraction(1 / 2):
                num_factors.append(expr.sqrt(base))
            elif power == -1:
                denom_factors.append(base)
            elif power == Fraction(-1 / 2):
                denom_factors.append(expr.sqrt(base))
            elif isinstance(power, (int, Fraction)) and power > 0:
                num_factors.append(base ** expr.Const(power))
            elif isinstance(power, (int, Fraction)) and power < 0:
                denom_factors.append(base ** expr.Const(-power))
            elif isinstance(power, Polynomial):
                num_factors.append(base ** from_poly(power))
            elif expr.is_matrix_type(base.type) and power == 0:
                # TODO: check whether base is a square matrix or not
                r = expr.num_row(base.type)
                num_factors.append(expr.Fun(('unit_matrix', expr.FunType(expr.IntType, expr.TensorType(expr.IntType, r, r))), r))
            else:
                raise TypeError("from_mono: unexpected type %s for power" % type(power))

    large_num_factors = [factor for factor in num_factors if display_large(factor)]
    num_factors = [factor for factor in num_factors if not display_large(factor)]

    def prod(factors):
        if len(factors) == 0:
            return expr.Const(1)
        else:
            return functools.reduce(operator.mul, factors[1:], factors[0])

    res = prod(num_factors)
    if len(denom_factors) != 0:
        res = res / prod(denom_factors)
    if len(large_num_factors) != 0:
        if res == expr.Const(1):
            res = prod(large_num_factors)
        else:
            res = res * prod(large_num_factors)
    if sign == -1:
        res = -res
    return res

def from_poly(p: Polynomial) -> expr.Expr:
    """Convert a polynomial to an expression."""
    if len(p.monomials) == 0:
        return expr.Const(0)
    else:
        monos = [from_mono(m) for m in p.monomials]
        monos = sorted(monos, key=lambda p: rsize(p), reverse=True)
        res = monos[0]
        for mono in monos[1:]:
            if expr.is_uminus(mono):
                res = res - mono.args[0]
            elif mono.is_times() and expr.is_uminus(mono.args[0]):
                res = res - mono.args[0].args[0] * mono.args[1]
            elif mono.is_times() and expr.is_const(mono.args[0]) and mono.args[0].val < 0:
                res = res - expr.Const(-mono.args[0].val) * mono.args[1]
            elif expr.is_const(mono) and mono.val < 0:
                res = res - expr.Const(-mono.val)
            else:
                res = res + mono
        return res
def type_normalize(t: expr.Type, ctx:Context):
    assert isinstance(t, expr.Type)
    if t in (expr.RealType, expr.BoolType, expr.Unknown, expr.IntType):
        return t
    elif t.name == 'tensor':
        return expr.TensorType(t.eleType, normalize(t.row, ctx), normalize(t.col, ctx))
    elif t.name == 'fun':
        return expr.FunType(*[type_normalize(arg, ctx) for arg in t.args])
    else:
        raise NotImplementedError

def simp_type(e: expr.Expr, ctx: Context):
    if expr.is_var(e):
        return expr.Var(e.name, type=type_normalize(e.type, ctx))
    elif expr.is_const(e) or expr.is_skolem_func(e) or expr.is_inf(e):
        return e
    elif expr.is_symbol(e):
        return expr.Symbol(e.name, pat=e.pat, type=type_normalize(e.type, ctx))
    elif expr.is_op(e):
        return expr.Op(e.op, *[simp_type(arg, ctx) for arg in e.args])
    elif expr.is_fun(e):
        return expr.Fun((e.func_name, type_normalize(e.func_type,ctx)), \
                        *[simp_type(arg, ctx) for arg in e.args])
    elif expr.is_deriv(e):
        return expr.Deriv(e.var, simp_type(e.body, ctx))
    elif expr.is_limit(e):
        return expr.Limit(e.var, simp_type(e.lim, ctx), simp_type(e.body, ctx), var_type=e.var_type)
    elif expr.is_integral(e):
        return expr.Integral(e.var, simp_type(e.lower, ctx), \
                        simp_type(e.upper, ctx), simp_type(e.body, ctx))
    elif expr.is_indefinite_integral(e):
        return expr.IndefiniteIntegral(e.var, simp_type(e.body, ctx), e.skolem_args)
    elif expr.is_evalat(e):
        return expr.EvalAt(e.var, simp_type(e.lower, ctx), \
                        simp_type(e.upper, ctx), simp_type(e.body, ctx))
    elif expr.is_summation(e):
        return expr.Summation(e.index_var, simp_type(e.lower, ctx), \
                        simp_type(e.upper, ctx), simp_type(e.body, ctx))
    elif expr.is_product(e):
        return expr.Product(e.index_var, simp_type(e.lower, ctx), \
                        simp_type(e.upper, ctx), simp_type(e.body, ctx))
    elif expr.is_matrix(e):
        return expr.Matrix([[simp_type(item, ctx) for item in rv] for rv in e.data])
    else:
        raise NotImplementedError
