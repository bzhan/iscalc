"""Polynomials."""

from fractions import Fraction
from typing import Union, Dict, Tuple
import functools
import operator
import sympy
import math

from integral import expr
from integral.context import Context, apply_subterm


def collect_pairs(ps):
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
    
    return tuple(sorted(res_list))

def collect_pairs_power(ps: Dict[expr.Expr, "Polynomial"], ctx: Context):
    res = {}
    res_list = []
    def is_non_negative(c: Polynomial):
        if c.is_fraction() and c.get_fraction() >= 0:
            return True
        e = from_poly(c)
        if e.is_var() and ctx.is_not_negative(e):
            return True
        return False

    for v, c in ps:
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
    
    return tuple(sorted(res_list))

def reduce_power(n: expr.Expr, e: "Polynomial") -> Tuple[Tuple[expr.Expr, "Polynomial"]]:
    """Reduce n ^ e to normal form.
    
    Returns a list of (n_i, e_i), so that n ^ e equals (n_1 ^ e^1) * ... (n_k ^ e_k).

    If n has type Expr, n ^ e is left unchanged. If n is an integer,
    it is factored to simplify the representation.

    """
    if n.is_const() and isinstance(n.val, int) and e.is_fraction():
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
        if n.is_const() and e.is_fraction():
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
        ts = collect_pairs((mono.factors, mono.coeff) for mono in self.monomials)
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
    if s.is_const():
        return constant(s.val)
    else:
        return Polynomial([Monomial(1, [(s, 1)])])


"""
Conversion from expressions to polynomials.
"""

def to_poly_r(e: expr.Expr, ctx: Context) -> Polynomial:
    """Convert expression to polynomial."""
    if e.is_var():
        return singleton(e)

    elif e.is_plus():
        return to_poly(e.args[0], ctx) + to_poly(e.args[1], ctx)

    elif e.is_uminus():
        return -to_poly(e.args[0], ctx)

    elif e.is_minus():
        return to_poly(e.args[0], ctx) - to_poly(e.args[1], ctx)

    elif e.is_times():
        a, b = to_poly(e.args[0], ctx), to_poly(e.args[1], ctx)
        if a.is_monomial() and b.is_monomial():
            return a * b
        elif a.is_fraction() or b.is_fraction():
            return a * b
        elif a.is_monomial():
            return a * singleton(from_poly(b))
        elif b.is_monomial():
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

    elif e.is_fun() and e.func_name == "exp":
        a = e.args[0]
        if a.is_fun() and a.func_name == "log":
            return to_poly(a.args[0], ctx)
        else:
            return Polynomial([Monomial(1, [(expr.E, to_poly(a, ctx))])])

    elif e.is_fun() and e.func_name in ("sin", "cos", "tan", "cot", "csc", "sec"):
        a = e.args[0]
        if a.is_fun() and a.func_name == "a" + e.func_name:
            # sin(asin(x)) = x
            return to_poly(a.args[0], ctx)
        else:
            tmp = normalize(a, ctx)
            if e.func_name == "cos" and tmp.is_uminus():
                return singleton(expr.Fun(e.func_name, tmp.args[0]), )
            else:
                return singleton(expr.Fun(e.func_name, tmp))

    elif e.is_fun() and e.func_name in ("asin", "acos", "atan", "acot", "acsc", "asec"):
        a, = e.args
        if e.func_name in ("atan", "acot", "acos") and a.is_fun() and a.func_name == e.func_name[1:]:
            # TODO: determine domain range of cos(x)
            # atan(tan(x)) = x
            return to_poly(a.args[0], ctx)
        else:
            return singleton(expr.Fun(e.func_name, normalize(a, ctx)))

    elif e.is_fun() and e.func_name == "sqrt":
        return to_poly(expr.Op("^", e.args[0], expr.Const(Fraction(1, 2))), ctx)

    elif e.is_fun():
        args_norm = [normalize(arg, ctx) for arg in e.args]
        return singleton(expr.Fun(e.func_name, *args_norm))

    elif e.is_evalat():
        if e.upper == expr.POS_INF:
            upper = expr.Limit(e.var, expr.POS_INF, e.body)
        elif e.upper == expr.NEG_INF:
            x = expr.Var(e.var)
            upper = expr.Limit(e.var, expr.POS_INF, e.body.subst(e.var, -x))
        else:
            try:
                upper = normalize(e.body.subst(e.var, e.upper), ctx)
            except:
                x = expr.Var(e.var)
                a = e.upper
                upper = expr.Limit(e.var, expr.POS_INF, e.body.subst(e.var, a - 1 / x))

        if e.lower == expr.POS_INF:
            lower = expr.Limit(e.var, expr.POS_INF, e.body)
        elif e.lower == expr.NEG_INF:
            x = expr.Var(e.var)
            lower = expr.Limit(e.var, expr.POS_INF, e.body.subst(e.var, -x))
        else:
            try:
                lower = normalize(e.body.subst(e.var, e.lower), ctx)
            except:
                x = expr.Var(e.var)
                a = e.lower
                lower = expr.Limit(e.var, expr.POS_INF, e.body.subst(e.var, a + 1 / x))
        return to_poly(normalize(upper, ctx) - normalize(lower, ctx), ctx)

    elif e.is_integral():
        ctx2 = Context(ctx)
        ctx2.add_condition(expr.Op(">", expr.Var(e.var), e.lower))
        ctx2.add_condition(expr.Op("<", expr.Var(e.var), e.upper))
        body = normalize(e.body, ctx2)
        l, h = normalize(e.lower, ctx), normalize(e.upper, ctx)

        if l.is_evaluable() and h.is_evaluable() :
            ll, hh = expr.eval_expr(l), expr.eval_expr(h)
            if ll > hh:
                return singleton(-expr.Integral(e.var, h, l, body))
        return singleton(expr.Integral(e.var, normalize(e.lower, ctx), normalize(e.upper, ctx), body))

    elif e.is_limit():
        ctx2 = Context(ctx)
        if e.lim == expr.POS_INF:
            ctx2.add_condition(expr.Op(">", expr.Var(e.var), expr.Const(0)))
        return singleton(expr.Limit(e.var, normalize(e.lim, ctx), normalize(e.body, ctx2)))

    elif e.is_inf():
        if e == expr.POS_INF:
            return singleton(e)
        else:
            return -singleton(expr.POS_INF)

    elif e.is_indefinite_integral():
        return singleton(expr.IndefiniteIntegral(e.var, normalize(e.body, ctx), e.skolem_args))

    elif e.is_summation():
        l, u = normalize(e.lower, ctx), normalize(e.upper, ctx)
        if l == u:
            return to_poly(e.body.subst(e.index_var, l), ctx)
        ctx2 = Context(ctx)
        ctx2.add_condition(expr.Op(">=", expr.Var(e.index_var), l))
        return singleton(expr.Summation(e.index_var, normalize(e.lower, ctx),
                                        normalize(e.upper, ctx), normalize(e.body, ctx2)))
    else:
        return singleton(e)

def to_poly(e: expr.Expr, ctx: Context) -> expr.Expr:
    return to_poly_r(e, ctx).reduce(ctx)

def function_eval(e: expr.Expr, ctx: Context) -> expr.Expr:
    if e.is_fun() and e.func_name == "binom":
        if e.args[0].is_const() and e.args[1].is_const():
            return expr.Const(math.comb(e.args[0].val, e.args[1].val))

    if e.is_fun() and e.func_name == 'factorial':
        if e.args[0].is_const() and abs(round(e.args[0].val) - e.args[0].val) < 1e-15 and round(e.args[0].val) >= 0:
            return expr.Const(math.factorial(round(e.args[0].val)))

    return e

def function_table(e: expr.Expr, ctx: Context) -> expr.Expr:
    if not e.is_fun() or len(e.args) != 1:
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

def simplify_eq(e: expr.Expr, ctx: Context) -> expr.Expr:
    if not e.is_var():
        return e

    for eq in ctx.get_conds().data:
        if eq.is_equals() and e == eq.lhs and eq.rhs.is_constant():
            return eq.rhs
    return e

def simplify_limit(e: expr.Expr, ctx: Context) -> expr.Expr:
    from integral import limits
    if not e.is_limit():
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
    if not e.is_integral():
        return e

    if e.body.is_deriv() and e.body.var == e.var:
        return expr.EvalAt(e.var, e.lower, e.upper, e.body.body)
    elif e.lower == e.upper:
        return expr.Const(0)
    else:
        return e

def simplify_power(e: expr.Expr, ctx: Context) -> expr.Expr:
    if not e.is_power():
        return e
    if e.args[1].is_plus() and e.args[0].is_const() and e.args[1].args[1].is_const():
        # c1 ^ (a + c2) => c1 ^ c2 * c1 ^ a
        return (e.args[0] ^ e.args[1].args[1]) * (e.args[0] ^ e.args[1].args[0])
    elif e.args[1].is_minus() and e.args[0].is_const() and e.args[1].args[1].is_const():
        # c1 ^ (a - c2) => c1 ^ -c2 * c1 ^ a
        return (e.args[0] ^ e.args[1].args[0]) * (e.args[0] ^ (-(e.args[1].args[1])))
    elif e.args[0].is_uminus() and e.args[1].is_const():
        # (-a) ^ n = (-1) ^ n * a ^ n
        return (expr.Const(-1) ^ e.args[1]) * (e.args[0].args[0] ^ e.args[1])
    elif e.args[0].is_minus() and e.args[0].args[0].is_uminus() and e.args[1].is_const():
        # (-a - b) ^ n = (-1) ^ n * (a + b) ^ n
        nega, negb = e.args[0].args
        return (expr.Const(-1) ^ e.args[1]) * ((nega.args[0] + negb) ^ e.args[1])
    else:
        return e

def simplify_trig(e: expr.Expr, ctx: Context) -> expr.Expr:
    if not (e.is_fun() and e.func_name in ('sin', 'cos', 'tan', 'cot', 'csc', 'sec')):
        return e

    a = e.args[0]
    c = expr.Symbol('c', [expr.CONST])
    d = expr.Symbol('d', [expr.CONST])

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
    if not (e.is_fun() and e.func_name == 'log'):
        return e
    
    a = e.args[0]
    if not a.is_constant():
        return e

    if a.is_const() and isinstance(a.val, int):
        int_factors = sympy.factorint(a.val)
        log_ints = []
        for b, e in int_factors.items():
            if e != 1:
                log_ints.append(e * expr.log(expr.Const(b)))
            else:
                log_ints.append(expr.log(expr.Const(b)))
            return sum(log_ints[1:], log_ints[0])
    elif a.is_const() and isinstance(a.val, Fraction):
        return expr.log(expr.Const(a.val.numerator)) - expr.log(expr.Const(a.val.denominator))
    elif a.is_times():
        return expr.log(a.args[0]) + expr.log(a.args[1])
    elif a.is_divides():
        return expr.log(a.args[0]) - expr.log(a.args[1])
    elif a.is_fun() and a.func_name == 'sqrt':
        return expr.log(a.args[0]) / 2
    else:
        return e

def simplify_sqrt(e: expr.Expr, ctx: Context) -> expr.Expr:
    if not (e.is_fun() and e.func_name == 'sqrt'):
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

def normalize(e: expr.Expr, ctx: Context) -> expr.Expr:
    if e.is_equals():
        return expr.Eq(normalize(e.lhs, ctx), normalize(e.rhs, ctx))

    if e.is_const():
        return e

    for i in range(5):
        old_e = e
        e = from_poly(to_poly(e, ctx))
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
        if e == old_e:
            break

    return e

"""
Conversion from polynomials to terms.
"""

def rsize(e: expr.Expr) -> int:
    """Find size of term without constants."""
    if e.is_const():
        return 0
    elif e.is_uminus():
        return rsize(e.args[0])
    elif e.is_times():
        return rsize(e.args[0]) + e.args[1].size() + 1
    else:
        return e.size()

def display_large(e: expr.Expr) -> bool:
    """Determine whether the expression requires large display."""
    def pred(e: expr.Expr) -> bool:
        return e.is_integral() or e.is_divides() or (e.is_fun() and e.func_name == "binom")
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
            if mono.is_uminus():
                res = res - mono.args[0]
            elif mono.is_times() and mono.args[0].is_uminus():
                res = res - mono.args[0].args[0] * mono.args[1]
            elif mono.is_times() and mono.args[0].is_const() and mono.args[0].val < 0:
                res = res - expr.Const(-mono.args[0].val) * mono.args[1]
            elif mono.is_const() and mono.val < 0:
                res = res - expr.Const(-mono.val)
            else:
                res = res + mono
        return res
