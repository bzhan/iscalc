"""Rules for integration."""

from decimal import Decimal
from fractions import Fraction
from typing import Optional, Dict, Tuple, Union, List, Set
import functools
import operator

from integral import expr, matrix, context
from integral.expr import Var, Const, Fun, EvalAt, Op, Integral, Symbol, Expr, \
    OP, CONST, VAR, sin, cos, FUN, decompose_expr_factor, \
    Deriv, Inf, Limit, NEG_INF, POS_INF, IndefiniteIntegral, Summation, SUMMATION, Matrix, INTEGRAL, MATRIX, INF
from integral import parser
from integral.solve import solve_equation, solve_for_term
from integral import latex
from integral import limits
from integral import norm
from integral.context import Context, apply_subterm, body_conds
from integral import poly
from integral.poly import from_poly, to_poly, normalize
from integral.conditions import Conditions
from integral import sympywrapper

def deriv(var: str, e: Expr, ctx: Context) -> Expr:
    """Compute the derivative of e with respect to variable
    name var.

    """

    def normal(x):
        return normalize(x, ctx)

    def rec(e):
        if var not in e.get_vars():
            return Const(0)
        elif expr.is_var(e):
            if e.name == var:
                # dx. x = 1
                return Const(1)
            else:
                # dx. y = 0
                return Const(0)
        elif expr.is_const(e):
            # dx. c = 0
            return Const(0)
        elif expr.is_op(e):
            if e.op == "+":
                x, y = e.args
                return normal(rec(x) + rec(y))
            elif e.op == "-" and len(e.args) == 2:
                x, y = e.args
                return normal(rec(x) - rec(y))
            elif e.op == "-" and len(e.args) == 1:
                x, = e.args
                return normal(-(rec(x)))
            elif e.op == "*":
                x, y = e.args
                if not x.contains_var(var):
                    return normal(x * rec(y))
                elif not y.contains_var(var):
                    return normal(rec(x) * y)
                else:
                    return normal(x * rec(y) + rec(x) * y)
            elif e.op == "/":
                x, y = e.args
                if not y.contains_var(var):
                    # x / c case:
                    return normal(rec(x) / y)
                elif not x.contains_var(var) and y.ty == OP and y.op == "^":
                    # c / (y0 ^ y1): rewrite to c * y0 ^ (-y1)
                    return rec(x * (y.args[0] ^ (-y.args[1])))
                else:
                    # general case
                    return normal((rec(x) * y - x * rec(y)) / (y ^ Const(2)))
            elif e.op == "^":
                x, y = e.args
                if y.ty == CONST:
                    return normal(y * (x ^ Const(y.val - 1)) * rec(x))
                elif var not in y.get_vars():
                    return normal(y * (x ^ (y - 1)) * rec(x))
                else:
                    return normal(rec(expr.exp(y * expr.log(x))))
            else:
                raise NotImplementedError
        elif expr.is_fun(e):
            if e.func_name == "sin":
                x, = e.args
                return normal(cos(x) * rec(x))
            elif e.func_name == "cos":
                x, = e.args
                return normal(-(sin(x) * rec(x)))
            elif e.func_name == "tan":
                x, = e.args
                return normal((expr.sec(x) ^ Const(2)) * rec(x))
            elif e.func_name == "sec":
                x, = e.args
                return normal(expr.sec(x) * expr.tan(x) * rec(x))
            elif e.func_name == "csc":
                x, = e.args
                return normal(-expr.csc(x) * expr.cot(x) * rec(x))
            elif e.func_name == "cot":
                x, = e.args
                return normal(-(expr.csc(x) ^ Const(2)))
            elif e.func_name == "cot":
                x, = e.args
                return normal(-(sin(x) ^ Const(-2)) * rec(x))
            elif e.func_name == "log":
                x, = e.args
                return normal(rec(x) / x)
            elif e.func_name == "exp":
                x, = e.args
                return normal(expr.exp(x) * rec(x))
            elif e.func_name == "pi":
                return Const(0)
            elif e.func_name == "sqrt":
                if e.args[0].ty == CONST:
                    return Const(0)
                else:
                    return normal(rec(e.args[0] ^ Const(Fraction(1 / 2))))
            elif e.func_name == "atan":
                x, = e.args
                return normal(rec(x) / (Const(1) + (x ^ Const(2))))
            elif e.func_name == "asin":
                x, = e.args
                return normal(rec(x) / expr.sqrt(Const(1) - (x ^ Const(2))))
            elif e.func_name == "acos":
                x, = e.args
                return normal(-(rec(x) / expr.sqrt(Const(1) - (x ^ Const(2)))))
            elif e.func_name == "acot":
                x, = e.args
                return normal(-rec(x)) / (Const(1) + x ^ Const(2))
            elif e.func_name == "binom":
                # Arguments should be integers
                assert not e.contains_var(var), "deriv: binom applied to real variables"
                return Const(0)
            else:
                return Deriv(var, e)
        elif expr.is_integral(e):
            if e.lower.is_constant():
                return normal(Integral(e.var, e.lower, e.upper, rec(e.body))
                              + e.body.subst(e.var, e.upper) * rec(e.upper))
            return normal(Integral(e.var, e.lower, e.upper, rec(e.body))
                          + e.body.subst(e.var, e.upper) * rec(e.upper)
                          - e.body.subst(e.var, e.lower) * rec(e.lower))
        elif expr.is_limit(e):
            return Limit(e.var, e.lim, rec(e.body))
        elif expr.is_summation(e):
            return Summation(e.index_var, e.lower, e.upper, rec(e.body))
        elif expr.is_inf(e):
            return Const(0)
        else:
            print(e, type(e))
            raise NotImplementedError

    return rec(e)


class ProofObligationBranch:
    def __init__(self, exprs: List[Expr], flags: List[bool] = None):
        self.exprs = exprs  # satisfy all expressions
        if flags is None or len(flags) != len(exprs):
            self.need_to_be_satisfied = [True for i in range(len(exprs))]
        else:
            self.need_to_be_satisfied = flags

    def __str__(self):
        res = ", ".join([str(e) for e in self.exprs])
        res += "\n"
        res += ", ".join([str(b) for b in self.need_to_be_satisfied])
        return res

    def export(self):
        res = {
            'exprs': [str(e) for e in self.exprs]
        }
        return res


class ProofObligation:
    """Represents a proof obligation to prove e using the conditions
    in conds.
    
    """

    def __init__(self, branches: List['ProofObligationBranch'], conds: Conditions):
        self.branches = branches  # if any branch is satisfied then the proof obligation is carried out
        self.conds = conds

    def __eq__(self, other: "ProofObligation"):
        return self.branches == other.branches

    def __le__(self, other: "ProofObligation"):
        if len(self.branches) < other.branches:
            return True
        elif len(self.branches > other.branches):
            return False
        return all(a < b for a, b in zip(self.branches, other.branches))

    def __str__(self):
        res = ""
        for i, b in enumerate(self.branches):
            res += "branch " + str(i) + ":\n"
            res += str(b) + '\n'
        # "%s" % self.branches
        return res

    def __repr__(self):
        return str(self)

    def __hash__(self):
        return hash(tuple(self.branches))

    def export(self):
        res = {
            'branches': [branch.export() for branch in self.branches],
            'conds': self.conds.export()
        }
        return res


def check_wellformed(e: Expr, ctx: Context) -> List[ProofObligation]:
    """Check whether an expression e is wellformed, and return
    a set of wellformed-ness conditions if otherwise.
    
    """
    obligations: List[ProofObligation] = list()

    def add_obligation(branches: Union[List[ProofObligationBranch], Expr], ctx: Context):
        if isinstance(branches, Expr):
            branches = [ProofObligationBranch([branches])]
        obligation = ProofObligation(branches, ctx.get_conds())
        if obligation not in obligations:
            obligations.append(obligation)

    def rec(e: Expr, ctx: Context):
        if expr.is_var(e) or expr.is_const(e):
            pass
        elif expr.is_op(e):
            for arg in e.args:
                rec(arg, ctx)
            if e.is_divides():
                if ctx.check_condition(Op("!=", e.args[1], Const(0))):
                    pass
                else:
                    add_obligation(Op("!=", e.args[1], Const(0)), ctx)
            if e.is_power():
                if ctx.check_condition(Op(">", e.args[0], Const(0))):
                    pass
                elif ctx.check_condition(Fun("isInt", e.args[1])) and ctx.check_condition(
                        Op(">=", e.args[1], Const(0))):
                    pass
                else:
                    add_obligation(Op(">", e.args[0], Const(0)), ctx)
                    add_obligation(Fun("isInt", e.args[1]), ctx)
                    add_obligation(Op(">=", e.args[1], Const(0)), ctx)
        elif expr.is_fun(e):
            for arg in e.args:
                rec(arg, ctx)
            if e.func_name == 'log':
                if ctx.check_condition(Op(">", e.args[0], Const(0))):
                    pass
                else:
                    add_obligation(Op(">", e.args[0], Const(0)), ctx)
            if e.func_name == 'sqrt':
                if ctx.check_condition(Op(">=", e.args[0], Const(0))):
                    pass
                else:
                    add_obligation(Op(">=", e.args[0], Const(0)), ctx)
            if e.func_name == 'gamma':
                f1 = ctx.check_condition(Op(">", e.args[0], Const(0)))
                f2 = ctx.check_condition(Op('<'), e.args[0], Const(0)) and \
                     ctx.check_condition(Fun("notInt", e.args[0]))
                if f1 or f2:
                    pass
                else:
                    branch1 = ProofObligationBranch([Op(">", e.args[0], Const(0))])
                    branch2 = ProofObligationBranch([Op("<", e.args[0], Const(0)), Fun("notInt", e.args[0])])
                    add_obligation([branch1, branch2], ctx)
            if e.func_name == "acos" or e.func_name == "asin":
                f1 = ctx.check_condition(Op(">=", e.args[0], Const(-1)))
                f2 = ctx.check_condition(Op("<=", e.args[0], Const(1)))
                if f1 and f2:
                    pass
                else:
                    add_obligation(Op(">=", e.args[0], Const(-1)), ctx)
                    add_obligation(Op("<=", e.args[0], Const(1)), ctx)
            if e.func_name == 'tan':
                tmp = normalize(Const(2) * e.args[0] / expr.pi, ctx)
                f1 = ctx.check_condition(Fun("isInt", tmp))
                f2 = ctx.check_condition(Fun("isEven", tmp))

                if not f1 or f2:
                    pass
                else:
                    branch1 = ProofObligationBranch([Fun("isInt", tmp)], [False])
                    branch2 = ProofObligationBranch([Fun("isEven", tmp)])
                    add_obligation([branch1, branch2], ctx)
            # TODO: add checks for other functions
        elif expr.is_integral(e):
            rec(e.body, body_conds(e, ctx))
        elif expr.is_deriv(e):
            rec(e.body, ctx)
        elif expr.is_summation(e):
            rec(e.lower, ctx)
            rec(e.upper, ctx)
            rec(e.body, body_conds(e, ctx))
        else:
            pass

    rec(e, ctx)
    return obligations


def check_asymp_converge(asymp: limits.Asymptote) -> bool:
    if isinstance(asymp, limits.PolyLog):
        for n in asymp.order:
            if isinstance(n, (int, Fraction)) and n > 1:
                return True
            elif isinstance(n, Expr) and n.val > 1:
                return True
            elif isinstance(n, (int, Fraction)) and n == 1:
                continue  # check next orders
            elif isinstance(n, Expr) and n.val == 1:
                continue
            else:
                return False
        return False
    elif isinstance(asymp, limits.Exp):
        return True
    else:
        return False


def check_converge(e: Expr, ctx: Context) -> bool:
    """Check convergence of the sum or integral."""
    if expr.is_summation(e):
        lim = limits.limit_of_expr(e.body, e.index_var, ctx)
        if lim.e == Const(0) and check_asymp_converge(lim.asymp):
            return True
    elif expr.is_var(e) or e.is_constant():
        return True
    elif e.is_times() or e.is_plus():
        if check_converge(e.args[0], ctx) and check_converge(e.args[1], ctx):
            return True
    elif e.is_power():
        if check_converge(e.args[0], ctx) and check_converge(e.args[1], ctx) and \
                ctx.check_condition(Op(">", e.args[1], Const(0))):
            return True
    elif e.is_divides():
        if ctx.check_condition(Op("!=", e.args[1], Const(0))) and check_converge(e.args[0], ctx) and \
                check_converge(e.args[1], ctx):
            return True
    elif expr.is_fun(e):
        flag = True
        for arg in e.args:
            if not check_converge(arg, ctx):
                flag = False
                break
        if (flag):
            return True
    return False


class Rule:
    """
    Represents a rule for integration. It takes an integral
    to be evaluated (as an expression), then outputs a new
    expression that it is equal to.

    """

    def eval(self, e: Expr, ctx: Context) -> Expr:
        """Evaluation of the rule on the given expression. Returns
        a new expression.

        """
        raise NotImplementedError

    def export(self):
        """Returns the JSON representation of the rule."""
        raise NotImplementedError

    def get_substs(self) -> Dict[str, Expr]:
        """Return dictionary of variable substitutions produced by the rule."""
        return dict()


class Simplify(Rule):
    """Perform algebraic simplification. This treats the
    expression as a polynomial, and normalizes the polynomial.

    """

    def __init__(self):
        self.name = "Simplify"

    def __str__(self):
        return "simplify"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        res = normalize(e, ctx)
        return res


class Linearity(Rule):
    """Applies linearity rules:

    INT (a + b) = INT a + INT b,
    INT (c * a) = c * INT a      (where c is a constant).
    INT (c / a) = c * INT 1 / a  (where c is a constant).

    """

    def __init__(self):
        self.name = "Linearity"

    def __str__(self):
        return "linearity"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        def prod(es):
            es = list(es)
            if len(es) == 0:
                return Const(1)
            else:
                return functools.reduce(operator.mul, es[1:], es[0])

        def rec(e: Expr):
            if expr.is_integral(e):
                if e.body.is_plus():
                    return rec(expr.Integral(e.var, e.lower, e.upper, e.body.args[0])) + \
                        rec(expr.Integral(e.var, e.lower, e.upper, e.body.args[1]))
                elif expr.is_uminus(e.body):
                    return -rec(expr.Integral(e.var, e.lower, e.upper, e.body.args[0]))
                elif e.body.is_minus():
                    return rec(expr.Integral(e.var, e.lower, e.upper, e.body.args[0])) - \
                        rec(expr.Integral(e.var, e.lower, e.upper, e.body.args[1]))
                elif e.body.is_times() or e.body.is_divides():
                    num_factors, denom_factors = decompose_expr_factor(e.body)
                    b = prod(f for f in num_factors if f.contains_var(e.var))
                    c = prod(f for f in num_factors if not f.contains_var(e.var))
                    denom_b = prod(f for f in denom_factors if f.contains_var(e.var))
                    denom_c = prod(f for f in denom_factors if not f.contains_var(e.var))
                    if denom_b != Const(1):
                        b = b / denom_b
                    if denom_c != Const(1):
                        c = c / denom_c
                    if c == expr.Const(1):
                        return Integral(e.var, e.lower, e.upper, b)
                    else:
                        return c * rec(Integral(e.var, e.lower, e.upper, b))
                elif e.body.is_constant() and e.body != Const(1):
                    return e.body * expr.Integral(e.var, e.lower, e.upper, Const(1))
                else:
                    return e
            elif expr.is_indefinite_integral(e):
                if e.body.is_plus():
                    return rec(expr.IndefiniteIntegral(e.var, e.body.args[0], e.skolem_args)) + \
                        rec(expr.IndefiniteIntegral(e.var, e.body.args[1], e.skolem_args))
                elif expr.is_uminus(e.body):
                    return -IndefiniteIntegral(e.var, e.body.args[0], e.skolem_args)
                elif e.body.is_minus():
                    return rec(expr.IndefiniteIntegral(e.var, e.body.args[0], e.skolem_args)) - \
                        rec(expr.IndefiniteIntegral(e.var, e.body.args[1], e.skolem_args))
                elif e.body.is_times() or e.body.is_divides():
                    num_factors, denom_factors = decompose_expr_factor(e.body)
                    b = prod(f for f in num_factors if f.contains_var(e.var))
                    c = prod(f for f in num_factors if not f.contains_var(e.var))
                    denom_b = prod(f for f in denom_factors if f.contains_var(e.var))
                    denom_c = prod(f for f in denom_factors if not f.contains_var(e.var))
                    if denom_b != Const(1):
                        b = b / denom_b
                    if denom_c != Const(1):
                        c = c / denom_c
                    if c == expr.Const(1):
                        return IndefiniteIntegral(e.var, b, e.skolem_args)
                    else:
                        return c * rec(IndefiniteIntegral(e.var, b, e.skolem_args))
                else:
                    return e
            elif expr.is_limit(e):
                if expr.is_uminus(e.body):
                    return -Limit(e.var, e.lim, e.body.args[0])
                elif e.body.is_times() or e.body.is_divides():
                    num_factors, denom_factors = decompose_expr_factor(e.body)
                    b, c = Const(1), Const(1)
                    for f in num_factors:
                        if not f.contains_var(e.var):
                            c = c * f
                        else:
                            b = b * f
                    for f in denom_factors:
                        if not f.contains_var(e.var):
                            c = c / f
                        else:
                            b = b / f
                    return c * Limit(e.var, e.lim, b)
                else:
                    return e
            elif expr.is_summation(e):
                v, l, u, body = e.index_var, e.lower, e.upper, e.body
                if e.body.is_minus():
                    return Summation(v, l, u, body.args[0]) - Summation(v, l, u, body.args[1])
                elif expr.is_uminus(e.body):
                    return -Summation(v, l, u, body.args[0])
                elif e.body.is_times() or e.body.is_divides():
                    num_factors, denom_factors = decompose_expr_factor(e.body)
                    b, c = Const(1), Const(1)
                    for f in num_factors:
                        if not f.contains_var(e.index_var):
                            c = c * f
                        else:
                            b = b * f
                    for f in denom_factors:
                        if not f.contains_var(e.index_var):
                            c = c / f
                        else:
                            b = b / f
                    c = normalize(c, ctx)
                    b = normalize(b, ctx)
                    return normalize(c * Summation(e.index_var, e.lower, e.upper, b), ctx)
                else:
                    return e
            else:
                return e

        return rec(e)


class PartialFractionDecomposition(Rule):
    """Apply partial fraction decomposition from sympy."""

    def __init__(self):
        self.name = "PartialFractionDecomposition"

    def __str__(self):
        return "partial fraction decomposition"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if sympywrapper.is_rational(e):
            return sympywrapper.partial_fraction(e, ctx)
        else:
            return e


class ApplyIdentity(Rule):
    """Apply identities (trigonometric, etc) to the current term.
    
    The term that is rewritten to is always supplied, because there may
    be multiple options.

    """

    def __init__(self, source: Union[str, Expr], target: Union[str, Expr]):
        self.name = "ApplyIdentity"
        if isinstance(source, str):
            source = parser.parse_expr(source)
        if isinstance(target, str):
            target = parser.parse_expr(target)
        self.source = source
        self.target = target

    def __str__(self):
        return "rewrite %s to %s using identity" % (self.source, self.target)

    def export(self):
        return {
            "name": self.name,
            "str": str(self),
            "source": str(self.source),
            "target": str(self.target),
            "latex_str": "rewrite \\(%s\\) to \\(%s\\) using identity" % (
                latex.convert_expr(self.source), latex.convert_expr(self.target))
        }

    @staticmethod
    def search(e: Expr, ctx: Context) -> List[Expr]:
        res = []
        for identity in ctx.get_other_identities():
            inst = expr.match(e, identity.lhs)
            if inst is not None:
                expected_rhs = identity.rhs.inst_pat(inst)
                res.append(normalize(expected_rhs, ctx))
        return res

    def eval(self, e: Expr, ctx: Context) -> Expr:
        # Find source within e
        if self.source != e:
            find_res = e.find_subexpr(self.source)
            if len(find_res) == 0:
                raise AssertionError("ApplyIdentity: source expression not found")
            loc = find_res[0]
            return OnLocation(self, loc).eval(e, ctx)

        assert self.source == e

        for identity in ctx.get_other_identities():
            inst = expr.match(e, identity.lhs)
            if inst is not None:
                expected_rhs = identity.rhs.inst_pat(inst)
                tmp_conds = [cond.inst_pat(inst) for cond in identity.conds.data]
                flag = True
                for cond in tmp_conds:
                    flag = flag and ctx.check_condition(cond)
                if not flag:
                    continue
                if normalize(expected_rhs, ctx) == normalize(self.target, ctx):
                    return self.target

        raise AssertionError("ApplyIdentity: no matching identity for %s" % e)


class DefiniteIntegralIdentity(Rule):
    """Apply definite integral identity in current theory."""

    def __init__(self):
        self.name = "DefiniteIntegralIdentity"

    def __str__(self):
        return "apply definite integral"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        # Apply linearity
        if expr.is_integral(e) or expr.is_indefinite_integral(e):
            e = Linearity().eval(e, ctx)

        if not (expr.is_integral(e) or expr.is_indefinite_integral(e)):
            sep_ints = e.separate_integral()
            for _, loc in sep_ints:
                e = OnLocation(self, loc).eval(e, ctx)
            return e

        # First, look for indefinite integrals identities
        for identity in ctx.get_indefinite_integrals():
            inst = expr.match(IndefiniteIntegral(e.var, e.body, skolem_args=tuple()), identity.lhs)
            if inst is None:
                continue

            inst[identity.lhs.var] = Var(e.var)
            assert identity.rhs.is_plus() and expr.is_skolem_func(identity.rhs.args[1])
            pat_rhs = identity.rhs.args[0]  # remove Skolem constant C
            return EvalAt(e.var, e.lower, e.upper, normalize(pat_rhs.inst_pat(inst), ctx))

        # Look for definite integral identities
        for identity in ctx.get_definite_integrals():
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
                    return normalize(identity.rhs.inst_pat(inst), ctx)

        # No matching identity found
        return e


class SeriesExpansionIdentity(Rule):
    """Apply series expansion in the current theory."""

    def __init__(self, *, old_expr: Optional[Union[str, Expr]] = None, index_var: str = 'n'):
        self.name = "SeriesExpansionIdentity"
        if isinstance(old_expr, str):
            old_expr = parser.parse_expr(old_expr)
        self.old_expr = old_expr
        self.index_var = index_var

    def __str__(self):
        return "apply series expansion"

    def export(self):
        res = {
            "name": self.name,
            "str": str(self),
            "index_var": self.index_var
        }
        if self.old_expr is not None:
            res['old_expr'] = str(self.old_expr)
        return res

    def eval(self, e: Expr, ctx: Context) -> Expr:
        # If old_expr is given, try to find it within e
        if self.old_expr is not None and self.old_expr != e:
            find_res = e.find_subexpr(self.old_expr)
            if len(find_res) == 0:
                raise AssertionError("Equation: old expression not found")
            loc = find_res[0]
            return OnLocation(self, loc).eval(e, ctx)

        # Now e is the old expression
        assert self.old_expr is None or self.old_expr == e

        for identity in ctx.get_series_expansions():
            inst = expr.match(e, identity.lhs)
            if inst is None:
                continue

            res = identity.rhs.inst_pat(inst)
            assert expr.is_summation(res)
            res = res.alpha_convert(self.index_var)
            other_vars = res.get_vars(with_bd=True).difference(e.get_vars(with_bd=True))
            for var in other_vars:
                while ctx.d != 0:
                    ctx = ctx.parent
                ctx.add_fix(var, expr.IntType)
            return res

        # No matching identity found
        return e


class SeriesEvaluationIdentity(Rule):
    """Apply series evaluation in the current theory."""

    def __init__(self):
        self.name = "SeriesEvaluationIdentity"

    def __str__(self):
        return "apply series evaluation"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not expr.is_summation(e):
            return e
        for identity in ctx.get_series_evaluations():
            inst = expr.match(e, identity.lhs)
            if inst is None:
                continue

            return identity.rhs.inst_pat(inst)
        # No matching identity found
        return e


class IndefiniteIntegralIdentity(Rule):
    """Apply indefinite integral identity in current theory."""

    def __init__(self):
        self.name = "IndefiniteIntegralIdentity"

    def __str__(self):
        return "apply indefinite integral"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        """Apply indefinite integral identity to expression."""

        def apply(e: Expr):
            for indef in ctx.get_indefinite_integrals():
                inst = expr.match(e, indef.lhs)
                if inst is None:
                    continue

                inst['x'] = Var(e.var)
                assert indef.rhs.is_plus() and expr.is_skolem_func(indef.rhs.args[1])
                return indef.rhs.args[0].inst_pat(inst)

            # No matching identity found
            return e

        # Apply linearity
        if expr.is_integral(e) or expr.is_indefinite_integral(e):
            e = Linearity().eval(e, ctx)

        if e.is_equals():
            return OnLocation(self, "1").eval(e, ctx)

        integrals = e.separate_integral()
        skolem_args = set()
        for sub_e, loc in integrals:
            new_e = apply(sub_e)
            if new_e != sub_e:
                e = e.replace_expr(loc, new_e)
                skolem_args = skolem_args.union(set(sub_e.skolem_args))

        if e.is_plus() and expr.is_skolem_func(e.args[1]):
            # If already has Skolem variable at right
            skolem_args = skolem_args.union(set(arg.name for arg in e.args[1].dependent_vars))
            e = e.args[0] + expr.SkolemFunc(e.args[1].name, tuple(Var(arg) for arg in skolem_args))
        else:
            # If no Skolem variable at right
            e = e + expr.SkolemFunc("C", tuple(Var(arg) for arg in skolem_args))

        return e


class ReplaceSubstitution(Rule):
    """Replace previously performed substitution"""

    def __init__(self):
        self.name = "ReplaceSubstitution"

    def __str__(self):
        return "replace substitution"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        for var, expr in ctx.get_substs().items():
            e = e.subst(var, expr)
        return e


class DerivativeSimplify(Rule):
    """Simplify the derivative of an expression"""

    def __init__(self):
        self.name = "DerivativeSimplify"

    def __str__(self):
        return "simplify derivative"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not isinstance(e, Deriv):
            return e
        return deriv(e.var, e.body, ctx)


class OnSubterm(Rule):
    """Apply given rule on subterms.

    The traversal order is similar to bottom-conv: first traverse each subterm
    of the term recursively, then apply the rule to the term itself.

    """

    def __init__(self, rule: Rule):
        assert isinstance(rule, Rule)
        self.rule = rule

    def __str__(self):
        return "%s on subterms" % self.rule

    def export(self):
        res = self.rule.export()
        res['str'] += ' on subterms'
        res['loc'] = 'subterms'
        if 'latex_str' in res:
            res['latex_str'] += ' on subterms'
        return res

    def get_substs(self):
        return self.rule.get_substs()

    def eval(self, e: Expr, ctx: Context) -> Expr:
        return apply_subterm(e, self.rule.eval, ctx)


class OnLocation(Rule):
    """Apply given rule on subterm specified by given location."""

    def __init__(self, rule: Rule, loc):
        assert isinstance(rule, Rule)
        self.name = "OnLocation"
        self.rule = rule
        self.loc = expr.Location(loc)

    def __str__(self):
        return "%s at %s" % (self.rule, self.loc)

    def export(self):
        res = self.rule.export()
        res['str'] += ' at ' + str(self.loc)
        res['loc'] = str(self.loc)
        if 'latex_str' in res:
            res['latex_str'] += ' at ' + str(self.loc)
        return res

    def get_substs(self):
        return self.rule.get_substs()

    def eval(self, e: Expr, ctx: Context) -> Expr:
        def rec(cur_e, loc, ctx):
            if loc.is_empty():
                return self.rule.eval(cur_e, ctx)
            elif expr.is_var(cur_e) or expr.is_const(cur_e):
                raise AssertionError("OnLocation: invalid location")
            elif expr.is_op(cur_e):
                assert loc.head < len(cur_e.args), "OnLocation: invalid location"
                if len(cur_e.args) == 1:
                    return Op(cur_e.op, rec(cur_e.args[0], loc.rest, ctx))
                elif len(cur_e.args) == 2:
                    if loc.head == 0:
                        return Op(cur_e.op, rec(cur_e.args[0], loc.rest, ctx), cur_e.args[1])
                    elif loc.head == 1:
                        return Op(cur_e.op, cur_e.args[0], rec(cur_e.args[1], loc.rest, ctx))
                    else:
                        raise AssertionError("OnLocation: invalid location")
                else:
                    raise NotImplementedError
            elif expr.is_fun(cur_e):
                assert loc.head < len(cur_e.args), "OnLocation: invalid location"
                new_args = list(cur_e.args)
                new_args[loc.head] = rec(cur_e.args[loc.head], loc.rest, ctx)
                return Fun(cur_e.func_name, *tuple(new_args))
            elif expr.is_integral(cur_e):
                ctx2 = body_conds(cur_e, ctx)
                if loc.head == 0:
                    return Integral(cur_e.var, cur_e.lower, cur_e.upper, rec(cur_e.body, loc.rest, ctx2))
                elif loc.head == 1:
                    return Integral(cur_e.var, rec(cur_e.lower, loc.rest, ctx), cur_e.upper, cur_e.body)
                elif loc.head == 2:
                    return Integral(cur_e.var, cur_e.lower, rec(cur_e.upper, loc.rest, ctx), cur_e.body)
                else:
                    raise AssertionError("OnLocation: invalid location")
            elif expr.is_evalat(cur_e):
                if loc.head == 0:
                    return EvalAt(cur_e.var, cur_e.lower, cur_e.upper, rec(cur_e.body, loc.rest, ctx))
                elif loc.head == 1:
                    return EvalAt(cur_e.var, rec(cur_e.lower, loc.rest, ctx), cur_e.upper, cur_e.body)
                elif loc.head == 2:
                    return EvalAt(cur_e.var, cur_e.lower, rec(cur_e.upper, loc.rest, ctx), cur_e.body)
                else:
                    raise AssertionError("OnLocation: invalid location")
            elif expr.is_deriv(cur_e):
                assert loc.head == 0, "OnLocation: invalid location"
                return Deriv(cur_e.var, rec(cur_e.body, loc.rest, ctx))
            elif expr.is_limit(cur_e):
                if loc.head == 0:
                    if cur_e.lim.is_evaluable():
                        v = expr.eval_expr(cur_e.lim)
                        var = parser.parse_expr(cur_e.var, fixes=ctx.get_fixes())
                        if v == float('inf'):
                            cond = Op('>', var, Const(0))
                            ctx.add_condition(cond)
                        elif v == float('-inf'):
                            cond = Op('<', var, Const(0))
                            ctx.add_condition(cond)
                    return Limit(cur_e.var, cur_e.lim, rec(cur_e.body, loc.rest, ctx), drt=cur_e.drt)
                elif loc.head == 1:
                    return Limit(cur_e.var, rec(cur_e.lim, loc.rest, ctx), cur_e.body, drt=cur_e.drt)
                else:
                    raise AssertionError("OnLocation: invalid location")
            elif expr.is_indefinite_integral(cur_e):
                assert loc.head == 0, "OnLocation: invalid location"
                return IndefiniteIntegral(cur_e.var, rec(cur_e.body, loc.rest, ctx), cur_e.skolem_args)
            elif expr.is_summation(cur_e):
                ctx2 = body_conds(cur_e, ctx)
                if loc.head == 0:
                    return Summation(cur_e.index_var, cur_e.lower, cur_e.upper, rec(cur_e.body, loc.rest, ctx2))
                elif loc.head == 1:
                    return Summation(cur_e.index_var, rec(cur_e.lower, loc.rest, ctx), cur_e.upper, cur_e.body)
                elif loc.head == 2:
                    return Summation(cur_e.index_var, cur_e.lower, rec(cur_e.upper, loc.rest, ctx), cur_e.body)
                else:
                    raise AssertionError("OnLocation: invalid location")
            elif expr.is_matrix(cur_e):
                a, b = loc.top2
                n = len(cur_e.data)
                m = len(cur_e.data[0])
                assert a >= 0 and a < n and b >= 0 and b < m
                res_data = [list(rv) for rv in cur_e.data]
                res_data[a][b] = rec(res_data[a][b], loc.rest2, ctx)
                return Matrix(res_data, cur_e.type)
            else:
                raise NotImplementedError

        return rec(e, self.loc, ctx)


class FullSimplify(Rule):
    """Perform simplification by applying the following rules repeatedly:

    - Simplify
    - Linearity
    - DerivativeSimplify

    """

    def __init__(self):
        self.name = "FullSimplify"

    def __str__(self):
        return "full simplify"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        counter = 0
        current = e
        while True:
            # s = OnSubterm(ExpandMatFunc()).eval(current, ctx)
            s = OnSubterm(Linearity()).eval(current, ctx)
            s = Simplify().eval(s, ctx)
            s = OnSubterm(DerivativeSimplify()).eval(s, ctx)
            if s == current:
                break
            current = s
            counter += 1
            if counter > 5:
                raise AssertionError("Loop in FullSimplify")
        return current

class ApplyEquation(Rule):
    """Apply the given equation for rewriting."""

    def __init__(self, eq: Union[Expr, str], source:Expr):
        self.name = "ApplyEquation"
        if isinstance(eq, str):
            eq = parser.parse_expr(eq)
        self.eq = eq
        self.source = source

    def __str__(self):
        return "apply equation: " + str(self.eq)

    def latex_str(self):
        return "apply equation \\(%s\\)" % latex.convert_expr(self.eq)

    def export(self):
        eq_fixes = list(self.eq.get_vars(with_bd=True, with_type=True))
        res = {
            "name": self.name,
            "eq": str(self.eq),
            "source": str(self.source),
            "str": str(self),
            "latex_str": self.latex_str()
        }
        if eq_fixes != list():
            if not all(len(item) == 2 for item in eq_fixes):
                raise AssertionError
            res['eq_fixes'] = eq_fixes
        return res

    def eval(self, e: Expr, ctx: Context) -> Expr:
        # Find source within e
        if self.source != e:
            find_res = e.find_subexpr(self.source)
            if len(find_res) == 0:
                raise AssertionError("ApplyIdentity: source expression not found")
            loc = find_res[0]
            return OnLocation(self, loc).eval(e, ctx)
        assert self.source == e
        # Find lemma
        found = False
        conds = None
        for identity in ctx.get_lemmas():
            if self.eq == identity.expr:
                found = True
                conds = identity.conds.data
        for item in ctx.get_eq_conds().data:
            if self.eq == item:
                found = True
                conds = []
        assert found, "ApplyEquation: lemma %s not found" % self.eq

        # First try to match the current term with left or right side.
        pat = expr.expr_to_pattern(self.eq)
        conds_pattern = [expr.expr_to_pattern(cond) for cond in conds]
        inst_lhs = expr.match(e, pat.lhs)
        inst_rhs = expr.match(e, pat.rhs)
        tmp = None
        tmp_conds = []
        if inst_lhs is not None:
            tmp = pat.rhs.inst_pat(inst_lhs)
            tmp_conds = [cond_pattern.inst_pat(inst_lhs) for cond_pattern in conds_pattern]
            if tmp.has_symbol() or any([cond.has_symbol() for cond in tmp_conds]):
                tmp_inst_rhs = expr.match(self.eq.rhs, pat.rhs)
                tmp = tmp.inst_pat(tmp_inst_rhs)
                tmp_conds = [cond_pattern.inst_pat(tmp_inst_rhs) for cond_pattern in conds_pattern]
            if tmp != None and pat.lhs.inst_pat(inst_lhs) == self.source:
                if tmp_conds == []:
                    return tmp
                flag = True
                # check whether all conditions of the lemma have been satisfied
                for cond in tmp_conds:
                    flag = flag and ctx.check_condition(cond)
                if flag:
                    return tmp
        if inst_rhs is not None:
            tmp = pat.lhs.inst_pat(inst_rhs)
            tmp_conds = [cond_pattern.inst_pat(inst_rhs) for cond_pattern in conds_pattern]
            if tmp.has_symbol() or any([cond.has_symbol() for cond in tmp_conds]):
                tmp_inst_lhs = expr.match(self.eq.lhs, pat.lhs)
                tmp = tmp.inst_pat(tmp_inst_lhs)
                tmp_conds = [cond_pattern.inst_pat(tmp_inst_lhs) for cond_pattern in conds_pattern]
            if tmp != None and pat.rhs.inst_pat(inst_rhs) == self.source:
                if tmp_conds == []:
                    return tmp
                flag = True
                # check whether all conditions of the lemma have been satisfied
                for cond in tmp_conds:
                    flag = flag and ctx.check_condition(cond)
                if flag:
                    return tmp
        # print("solve equation %s for %s"%(self.eq, e))
        # Finally, try to solve for e in the equation.
        res = solve_for_term(self.eq, e, ctx)
        if res is not None:
            flag = True
            for cond in conds:
                flag = flag and ctx.check_condition(cond)
            if flag:
                return res
        return e


class ApplyInductHyp(Rule):
    """Apply induction hypothesis."""

    def __init__(self):
        self.name = "ApplyInductHyp"

    def __str__(self):
        return "apply induction hypothesis"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        for eq in ctx.get_induct_hyps():
            if e == eq.lhs:
                return eq.rhs
            if e == eq.rhs:
                return eq.lhs

        # Not found
        return e


class Substitution(Rule):
    """Apply substitution u = g(x).

    var_name - str: name of the new variable.
    var_subst - Expr: expression in the original integral to be substituted.

    The identity to be applied is:

    INT x:[a, b]. f(g(x)) * g(x)' = INT u:[g(a), g(b)]. f(u)

    """

    def __init__(self, var_name: str, var_subst: Union[Expr, str]):
        if isinstance(var_subst, str):
            var_subst = parser.parse_expr(var_subst)
        assert isinstance(var_name, str) and isinstance(var_subst, Expr)
        self.name = "Substitution"
        self.var_name = var_name
        self.var_subst = var_subst
        self.f = None  # After application, record f here

    def __str__(self):
        return "substitute %s for %s" % (self.var_name, self.var_subst)

    def export(self):
        return {
            "name": self.name,
            "var_name": self.var_name,
            "var_subst": str(self.var_subst),
            "str": str(self),
            "latex_str": "substitute \\(%s\\) for \\(%s\\)" % \
                         (self.var_name, latex.convert_expr(self.var_subst))
        }

    def get_substs(self):
        return {self.var_name: self.var_subst}

    def eval(self, e: Expr, ctx: Context) -> Expr:
        """
        Parameters:
        e: Expr, the integral on which to perform substitution.

        Returns:
        The new integral e', and stores in self.f the parameter used to
        specify the substitution.

        """
        if not (expr.is_integral(e) or expr.is_indefinite_integral(e)):
            sep_ints = e.separate_integral()
            if len(sep_ints) == 0:
                return e
            else:
                return OnLocation(self, sep_ints[0][1]).eval(e, ctx)

        # Variable to be substituted in the integral
        var_name = parser.parse_expr(self.var_name)

        # Expression used for substitution
        var_subst = self.var_subst

        if e.var not in var_subst.get_vars():
            raise AssertionError("Substitution: variable not found")

        dfx = deriv(e.var, var_subst, ctx)
        ctx2 = body_conds(e, ctx)
        if e.body.is_times() and e.body.args[1] == dfx:
            body = e.body.args[0]
        elif e.body.is_times() and e.body.args[0] == dfx:
            body = e.body.args[1]
        else:
            body = normalize(e.body / dfx, ctx2)
        body_subst = body.replace(var_subst, var_name)
        if e.var not in body_subst.get_vars():
            # Substitution is able to clear all x in original integrand
            self.f = body_subst
        else:
            # Substitution is unable to clear x, need to solve for x
            gu = solve_equation(var_subst, var_name, e.var, ctx)
            if gu is None:
                print('Solve %s = %s for %s' % (var_subst, var_name, e.var))
                raise AssertionError("Substitution: unable to solve equation")

            gu = normalize(gu, ctx)
            c = e.body.replace(parser.parse_expr(e.var), gu)
            new_problem_body = c * deriv(str(var_name), gu, ctx)
            self.f = new_problem_body

        if expr.is_integral(e):
            if e.lower == expr.NEG_INF:
                lower = limits.reduce_neg_inf_limit(var_subst, e.var, ctx)
            else:
                x = Var(e.var)
                lower = self.var_subst
                lower = limits.reduce_inf_limit(lower.subst(e.var, (1 / x) + e.lower), e.var, ctx)
                lower = normalize(lower, ctx)
            if e.upper == expr.POS_INF:
                upper = limits.reduce_inf_limit(var_subst, e.var, ctx)
            else:
                x = Var(e.var)
                upper = self.var_subst
                upper = limits.reduce_inf_limit(upper.subst(e.var, e.upper - (1 / x)), e.var, ctx)
                upper = normalize(upper, ctx)
            if lower.is_evaluable() and upper.is_evaluable() and expr.eval_expr(lower) > expr.eval_expr(upper):
                return normalize(Integral(self.var_name, upper, lower, Op("-", self.f)), ctx)
            else:
                return normalize(Integral(self.var_name, lower, upper, self.f), ctx)
        elif expr.is_indefinite_integral(e):
            return normalize(IndefiniteIntegral(self.var_name, self.f, e.skolem_args), ctx)
        else:
            raise TypeError


class SubstitutionInverse(Rule):
    """Apply substitution x = f(u).

    var_name - str: name of the new variable u.
    var_subst - Expr: expression containing the new variable.

    """

    def __init__(self, var_name: str, var_subst: Union[Expr, str]):
        self.name = "SubstitutionInverse"
        self.var_name = var_name
        if isinstance(var_subst, str):
            var_subst = parser.parse_expr(var_subst)
        self.var_subst = var_subst

    def __str__(self):
        return "inverse substitution for %s" % self.var_subst

    def export(self):
        return {
            "name": self.name,
            "var_name": self.var_name,
            "var_subst": str(self.var_subst),
            "str": str(self),
            "latex_str": "inverse substitution for \\(%s\\)" % latex.convert_expr(self.var_subst)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not expr.is_integral(e):
            sep_ints = e.separate_integral()
            if len(sep_ints) == 0:
                return e
            else:
                return OnLocation(self, sep_ints[0][1]).eval(e, ctx)

        # dx = f'(u) * du
        subst_deriv = deriv(self.var_name, self.var_subst, ctx)

        # Replace x with f(u)
        new_e_body = e.body.replace(Var(e.var), self.var_subst)

        # g(x) = g(x(u)) * f'(u)
        new_e_body = new_e_body * subst_deriv

        # Solve the equations lower = f(u) and upper = f(u) for u.
        # Solve the equations lower = f(u) and upper = f(u) for u.
        x = Var("_" + self.var_name)
        lower = solve_equation(self.var_subst, x, self.var_name, ctx)
        upper = solve_equation(self.var_subst, x, self.var_name, ctx)
        if lower is None or upper is None:
            raise AssertionError("SubstitutionInverse: cannot solve")

        lower = limits.reduce_inf_limit(lower.subst(x.name, (1 / x) + e.lower), x.name, ctx)
        upper = limits.reduce_inf_limit(upper.subst(x.name, e.upper - (1 / x)), x.name, ctx)

        lower = normalize(lower, ctx)
        upper = normalize(upper, ctx)
        if lower.is_evaluable() and upper.is_evaluable() and expr.eval_expr(lower) > expr.eval_expr(upper):
            return -expr.Integral(self.var_name, upper, lower, new_e_body)
        else:
            return expr.Integral(self.var_name, lower, upper, new_e_body)


class ExpandPolynomial(Rule):
    """Expand multiplication and power."""

    def __init__(self):
        self.name = "ExpandPolynomial"

    def __str__(self):
        return "expand polynomial"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if e.is_power() and expr.is_const(e.args[1]) and e.args[1].val > 1 and \
                int(e.args[1].val) == e.args[1].val:
            n = int(e.args[1].val)
            base = to_poly(self.eval(e.args[0], ctx), ctx)
            res = base
            for i in range(n - 1):
                res = res * base
            return from_poly(res.reduce(ctx))
        elif e.is_times():
            s1, s2 = self.eval(e.args[0], ctx), self.eval(e.args[1], ctx)
            return from_poly((to_poly(s1, ctx) * to_poly(s2, ctx)).reduce(ctx))
        elif e.is_divides():
            s1, s2 = self.eval(e.args[0], ctx), self.eval(e.args[1], ctx)
            p1, p2 = to_poly(s1, ctx), to_poly(s2, ctx)
            if p2.is_monomial():
                return from_poly((p1 / p2).reduce(ctx))
            else:
                return from_poly((p1 / poly.singleton(from_poly(p2))).reduce(ctx))
        elif expr.is_integral(e):
            ctx2 = body_conds(e, ctx)
            return expr.Integral(e.var, e.lower, e.upper, self.eval(e.body, ctx2))
        elif expr.is_indefinite_integral(e):
            ctx2 = body_conds(e, ctx)
            return expr.IndefiniteIntegral(e.var, self.eval(e.body, ctx2), e.skolem_args)
        else:
            return e


class Equation(Rule):
    """Apply substitution for equal expressions"""

    def __init__(self, old_expr: Optional[Union[str, Expr]], new_expr: Union[str, Expr]):
        self.name = "Equation"
        if isinstance(old_expr, str):
            old_expr = parser.parse_expr(old_expr)
        if isinstance(new_expr, str):
            new_expr = parser.parse_expr(new_expr)
        self.old_expr = old_expr
        self.new_expr = new_expr

    def __str__(self):
        if self.old_expr is None:
            return "rewriting to %s" % self.new_expr
        else:
            return "rewriting %s to %s" % (self.old_expr, self.new_expr)

    def export(self):
        if self.old_expr is None:
            latex_str = "rewriting to \\(%s\\)" % latex.convert_expr(self.new_expr)
        else:
            latex_str = "rewriting \\(%s\\) to \\(%s\\)" % \
                        (latex.convert_expr(self.old_expr), latex.convert_expr(self.new_expr))
        res = {
            "name": self.name,
            "new_expr": str(self.new_expr),
            "str": str(self),
            "latex_str": latex_str
        }
        if self.old_expr:
            res['old_expr'] = str(self.old_expr)
        return res

    def eval(self, e: Expr, ctx: Context) -> Expr:
        # If old_expr is given, try to find it within e
        if self.old_expr is not None and self.old_expr != e:
            find_res = e.find_subexpr(self.old_expr)
            if len(find_res) == 0:
                raise AssertionError("Equation: old expression not found")
            loc = find_res[0]
            return OnLocation(self, loc).eval(e, ctx)

        # Now e is the old expression
        assert self.old_expr is None or self.old_expr == e

        r = FullSimplify()
        r1, r2 = r.eval(e, ctx), r.eval(self.new_expr, ctx)
        if r1 == r2:
            return self.new_expr

        # Rewriting 1 to sin(x)^2 + cos(x)^2
        x = Symbol("x", [VAR, CONST, OP, FUN])
        p = expr.sin(x) ** 2 + expr.cos(x) ** 2
        if e == Const(1) and expr.match(self.new_expr, p):
            return self.new_expr

        if norm.eq_quotient(e, self.new_expr, ctx):
            return self.new_expr

        if norm.eq_power(e, self.new_expr, ctx):
            return self.new_expr

        if norm.eq_log(e, self.new_expr, ctx):
            return self.new_expr

        if norm.eq_definite_integral(e, self.new_expr, ctx):
            return self.new_expr

        if norm.simp_definite_integral(e, ctx) == normalize(self.new_expr, ctx):
            return self.new_expr

        # x * sum(k,l,u,body) => sum(k, l, u, x* body)
        x = Symbol('x', [VAR, CONST, OP, FUN])
        y = Symbol('y', [SUMMATION])
        p = x * y
        mapping = expr.match(e, p)
        if mapping is not None:
            sum = mapping[y.name]
            idx = sum.index_var
            out = mapping[x.name]
            if idx not in out.get_vars():
                e = Summation(idx, sum.lower, sum.upper, out * sum.body)

        # sum(k, l, u, body1) + sum(i, l, u, body2) => sum(k, l, u, body1+body2)
        x = Symbol('x', [SUMMATION])
        y = Symbol('y', [SUMMATION])
        p = x + y
        mapping = expr.match(e, p)
        if mapping is not None:
            sum1:Summation = mapping[x.name]
            sum2:Summation = mapping[y.name]
            if sum1.lower == sum2.lower and sum1.upper == sum2.upper:
                e = Summation(sum1.index_var, sum1.lower,sum1.upper, sum1.body+sum2.body)

        if normalize(norm.normalize_exp(e), ctx) == normalize(self.new_expr, ctx):
            return self.new_expr

        raise AssertionError("Equation: rewriting %s to %s failed" % (e, self.new_expr))


class IntegrationByParts(Rule):
    """Apply integration by parts.

    The arguments u and v should satisfy u * dv equals the integrand.

    """

    def __init__(self, u: Union[str, Expr], v: Union[str, Expr]):
        self.name = "IntegrationByParts"
        if isinstance(u, str):
            u = parser.parse_expr(u)
        if isinstance(v, str):
            v = parser.parse_expr(v)
        assert isinstance(u, Expr) and isinstance(v, Expr)
        self.u = u
        self.v = v

    def __str__(self):
        return "integrate by parts u -> %s, v -> %s" % (self.u, self.v)

    def export(self):
        return {
            "name": self.name,
            "u": str(self.u),
            "v": str(self.v),
            "str": str(self),
            "latex_str": "integrate by parts \\(u \\to %s, v \\to %s\\)" % \
                         (latex.convert_expr(self.u), latex.convert_expr(self.v))
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not (expr.is_integral(e) or expr.is_indefinite_integral(e)):
            sep_ints = e.separate_integral()
            if len(sep_ints) == 0:
                return e
            else:
                return OnLocation(self, sep_ints[0][1]).eval(e, ctx)

        ctx2 = body_conds(e, ctx)
        e.body = normalize(e.body, ctx2)
        du = deriv(e.var, self.u, ctx)
        dv = deriv(e.var, self.v, ctx)
        udv = normalize(self.u * dv, ctx2)

        equal = False
        if udv == e.body:
            equal = True

        if not equal and norm.eq_quotient(udv, e.body, ctx2):
            equal = True

        if not equal and norm.eq_power(udv, e.body, ctx2):
            equal = True

        if equal:
            if expr.is_integral(e):
                return expr.EvalAt(e.var, e.lower, e.upper, normalize(self.u * self.v, ctx2)) - \
                    expr.Integral(e.var, e.lower, e.upper, normalize(self.v * du, ctx2))
            elif expr.is_indefinite_integral(e):
                return normalize(self.u * self.v, ctx2) - \
                    expr.IndefiniteIntegral(e.var, normalize(self.v * du, ctx2), e.skolem_args)
        else:
            raise AssertionError("Integration by parts: %s != %s" % (str(udv), str(e.body)))


class SplitRegion(Rule):
    """Split integral into two parts at a point."""

    def __init__(self, c: Union[Expr, str]):
        self.name = "SplitRegion"
        if isinstance(c, str):
            c = parser.parse_expr(c)
        self.c = c

    def __str__(self):
        return "split region at %s" % self.c

    def export(self):
        return {
            "name": self.name,
            "c": str(self.c),
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not expr.is_integral(e):
            sep_ints = e.separate_integral()
            if len(sep_ints) == 0:
                return e
            else:
                return OnLocation(self, sep_ints[0][1]).eval(e, ctx)

        x = Var("c")
        is_cpv = limits.reduce_inf_limit(e.body.subst(e.var, self.c + 1 / x), x.name, ctx) in [POS_INF, NEG_INF]
        if not is_cpv:
            return expr.Integral(e.var, e.lower, self.c, e.body) + \
                expr.Integral(e.var, self.c, e.upper, e.body)
        else:
            return Limit(x.name, POS_INF, Integral(e.var, e.lower, normalize(self.c - 1 / x, ctx), e.body) +
                         Integral(e.var, normalize(self.c + 1 / x, ctx), e.upper, e.body))


class IntegrateByEquation(Rule):
    """When the initial integral occurs in the steps."""

    def __init__(self, lhs: Union[str, Expr]):
        self.name = "IntegrateByEquation"
        if isinstance(lhs, str):
            lhs = parser.parse_expr(lhs)
        self.lhs = lhs
        self.coeff = None

    def __str__(self):
        return "integrate by equation"

    def export(self):
        return {
            "name": self.name,
            "lhs": str(self.lhs),
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        """Eliminate the lhs's integral in rhs by solving equation."""
        norm_e = normalize(e, ctx)
        rhs_var = None
        lhs = normalize(self.lhs, ctx)

        def get_coeff(t: Expr):
            nonlocal rhs_var
            if t == lhs:
                if expr.is_integral(t):
                    rhs_var = t.var
                return Const(1)

            if t.is_plus():
                return get_coeff(t.args[0]) + get_coeff(t.args[1])
            elif t.is_minus():
                return get_coeff(t.args[0]) - get_coeff(t.args[1])
            elif expr.is_uminus(t):
                return -get_coeff(t.args[0])
            elif t.is_times():
                return t.args[0] * get_coeff(t.args[1])
            elif t.is_divides():
                return get_coeff(t.args[0]) / t.args[1]
            else:
                return Const(0)

        coeff = normalize(get_coeff(norm_e), ctx)
        if coeff == Const(0):
            return e

        if rhs_var != None:
            new_rhs = normalize(norm_e + ((-coeff) * lhs.alpha_convert(rhs_var)), ctx)
        else:
            new_rhs = normalize(norm_e + ((-coeff) * lhs), ctx)
        self.coeff = normalize(-(coeff), ctx)
        return normalize(new_rhs / ((Const(1) - coeff)), ctx)


class ElimInfInterval(Rule):
    """Convert improper integral with infinite upper or lower limits to
    a limit expression.

    If both upper and lower limits are infinity, a split point need to be
    provided.

    """

    def __init__(self, a=Const(0), new_var='t'):
        self.name = "ElimInfInterval"
        self.a = a
        self.new_var = new_var

    def __str__(self):
        return "eliminate improper integral"

    def export(self):
        return {
            "name": self.name,
            "a": str(self.a),
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        def gen_lim_expr(new_var, lim, lower, upper, drt=None):
            return expr.Limit(new_var, lim, expr.Integral(e.var, lower, upper, e.body), drt)

        if not expr.is_integral(e):
            sep_ints = e.separate_integral()
            if len(sep_ints) == 0:
                return e
            else:
                return OnLocation(self, sep_ints[0][1]).eval(e, ctx)

        inf = Inf(Decimal('inf'))
        neg_inf = Inf(Decimal('-inf'))
        upper, lower = e.upper, e.lower
        new_var = self.new_var

        if upper == inf and lower != neg_inf and lower != inf:
            # INT x:[a,oo]. body => lim t->oo. INT x:[a,t]. body
            return gen_lim_expr(new_var, inf, lower, Var(new_var))
        elif upper == neg_inf and lower != neg_inf and lower != inf:
            return gen_lim_expr(new_var, inf, lower, Var(new_var))
        elif upper != inf and upper != neg_inf and lower == neg_inf:
            # INT x:[-oo,a]. body => lim t->-oo. INT x:[t,a]. body
            return gen_lim_expr(new_var, neg_inf, Var(new_var), upper)
        elif upper != inf and upper != neg_inf and lower == inf:
            return gen_lim_expr(new_var, inf, Var(new_var), upper)
        elif upper == inf and lower == neg_inf:
            # INT x:[-oo,oo]. body =>
            # lim t->-oo. INT x:[t,a]. body + lim t->oo. INT x:[a,t]. body
            assert self.a is not None, "No split point provided"
            lim1 = gen_lim_expr(new_var, neg_inf, Var(new_var), self.a)
            lim2 = gen_lim_expr(new_var, inf, self.a, Var(new_var))
            return Op('+', lim1, lim2)
        elif upper == neg_inf and lower == inf:
            assert self.a is not None, "No split point provided"
            lim1 = gen_lim_expr(new_var, inf, Var(new_var), self.a)
            lim2 = gen_lim_expr(new_var, neg_inf, self.a, Var(new_var))
            return Op('+', lim1, lim2)
        else:
            raise NotImplementedError


class LHopital(Rule):
    """Apply L'Hoptial rule."""

    def __init__(self):
        self.name = "LHopital"

    def __str__(self):
        return "l'Hopital's rule"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not expr.is_limit(e):
            sep_lims = e.separate_limits()
            if len(sep_lims) == 0:
                return e
            else:
                return OnLocation(self, sep_lims[0][1]).eval(e, ctx)

        if not (isinstance(e.body, expr.Op) and e.body.op == '/'):
            return e

        numerator, denominator = e.body.args
        rule = DerivativeSimplify()
        return expr.Limit(e.var, e.lim, Op('/', rule.eval(Deriv(e.var, numerator), ctx),
                                           rule.eval(Deriv(e.var, denominator), ctx)), e.drt)


def check_item(item, target=None, *, debug=False):
    """Check application of rules in the item."""
    problem = parser.parse_expr(item['problem'])

    if debug:
        print("\n%s: %s" % (item['name'], problem))

    current = problem
    prev_steps = []
    ctx = Context()

    for step in item['calc']:
        reason = step['reason']
        expected = parser.parse_expr(step['text'])

        if reason == 'Initial':
            result = current

        elif reason == 'Simplification':
            if "location" in step:
                result = OnLocation(FullSimplify(), step["location"]).eval(current, ctx)
            else:
                result = FullSimplify().eval(current, ctx)

        elif reason == 'Substitution':
            var_name = step['params']['var_name']
            f = parser.parse_expr(step['params']['f'])
            g = parser.parse_expr(step['params']['g'])
            rule = Substitution(var_name, g)
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current, ctx)
            else:
                result = rule.eval(current, ctx)
            rule.f = parser.parse_expr(str(rule.f))  # trick to eliminate difference in printing
            if rule.f != f:
                print("Expected f: %s" % f)
                print("Actual f: %s" % rule.f)
                raise AssertionError("Unexpected value of f in substitution")

        elif reason == 'Integrate by parts':
            u = parser.parse_expr(step['params']['parts_u'])
            v = parser.parse_expr(step['params']['parts_v'])
            rule = IntegrationByParts(u, v)
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current, ctx)
            else:
                result = rule.eval(current, ctx)

        elif reason == 'Rewrite':
            rhs = parser.parse_expr(step['params']['rhs'])
            if 'denom' in step['params']:
                rule = Equation(rhs, parser.parse_expr(step['params']['denom']))
            else:
                rule = Equation(rhs)
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current, ctx)
            else:
                result = rule.eval(current, ctx)

        elif reason == 'Substitution inverse':
            var_name = step['params']['var_name']
            g = parser.parse_expr(step['params']['g'])
            rule = SubstitutionInverse(var_name, g)
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current, ctx)
            else:
                result = rule.eval(current, ctx)

        elif reason == 'Split region':
            c = parser.parse_expr(step['params']['c'])
            rule = SplitRegion(c)
            if 'location' in step:
                result = OnLocation(rule, step['location']).eval(current, ctx)
            else:
                result = rule.eval(current, ctx)

        elif reason == 'Solve equation':
            prev_id = int(step['params']['prev_id'])
            rule = IntegrateByEquation(prev_steps[prev_id])
            result = rule.eval(current, ctx)

        else:
            print("Reason: %s" % reason)
            raise NotImplementedError

        if result != expected:
            print("Expected: %s" % expected)
            print("Result: %s" % result)
            raise AssertionError("Error on intermediate step (%s)" % reason)

        current = result
        prev_steps.append(current)

    if target is not None:
        target = parser.parse_expr(target)
        if current != target:
            print("Target: %s" % target)
            print("Result: %s" % current)
            raise AssertionError("Error on final answer")


class DerivIntExchange(Rule):
    """Exchanging derivative and integral"""

    def __init__(self):
        self.name = "DerivIntExchange"

    def __str__(self):
        return "exchange derivative and integral"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if expr.is_deriv(e) and expr.is_integral(e.body):
            return Integral(e.body.var, e.body.lower, e.body.upper, Deriv(e.var, e.body.body))
        elif expr.is_deriv(e) and expr.is_indefinite_integral(e.body):
            return IndefiniteIntegral(e.body.var, Deriv(e.var, e.body.body), e.skolem_args)
        elif expr.is_indefinite_integral(e) and expr.is_deriv(e.body):
            return Deriv(e.body.var, IndefiniteIntegral(e.var, e.body.body, e.skolem_args))
        elif expr.is_integral(e) and expr.is_deriv(e.body):
            return Deriv(e.body.var, Integral(e.var, e.upper, e.lower, e.body.body))
        else:
            return e


class ExpandDefinition(Rule):
    """Expand a definition"""

    def __init__(self, func_name: str, simp=True):
        self.name = "ExpandDefinition"
        assert isinstance(func_name, str)
        self.func_name: str = func_name
        self.simp = simp

    def __str__(self):
        return "expand definition"

    def export(self):
        return {
            "name": self.name,
            "func_name": self.func_name,
            "str": str(self)
        }

    @staticmethod
    def search(e: Expr, ctx: Context) -> List[Tuple[Expr, expr.Location]]:
        subexprs = e.find_subexpr_pred(lambda t: expr.is_var(t) or expr.is_fun(t))
        res = []
        for sube, loc in subexprs:
            if expr.is_fun(sube):
                for identity in ctx.get_definitions():
                    if expr.is_fun(identity.lhs) and identity.lhs.func_name == sube.func_name:
                        res.append((sube, loc))
            if expr.is_var(sube):
                for identity in ctx.get_definitions():
                    if expr.is_symbol(identity.lhs) and identity.lhs.name == sube.name:
                        res.append((sube, loc))
        return res

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if expr.is_fun(e) and e.func_name == self.func_name:
            for identity in ctx.get_definitions():
                if expr.is_fun(identity.lhs) and identity.lhs.func_name == self.func_name:
                    inst = expr.match(e, identity.lhs)
                    if inst == None:
                        continue
                    tmp_conds = [cond.inst_pat(inst) for cond in identity.conds.data]
                    flag = True
                    for cond in tmp_conds:
                        flag = flag and ctx.check_condition(cond)
                    if flag:
                        if self.simp:
                            return normalize(identity.rhs.inst_pat(inst), ctx)
                        else:
                            return identity.rhs.inst_pat(inst)
        if expr.is_var(e) and e.name == self.func_name:
            for identity in ctx.get_definitions():
                if identity.lhs.is_symbol() and identity.lhs.name == self.func_name:
                    return identity.rhs

        # Not found
        return e


class FoldDefinition(Rule):
    """Fold a definition"""

    def __init__(self, func_name: str):
        self.name = "FoldDefinition"
        assert isinstance(func_name, str)
        self.func_name: str = func_name

    def __str__(self):
        return "fold definition"

    def export(self):
        return {
            "name": self.name,
            "func_name": self.func_name,
            "str": str(self)
        }

    @staticmethod
    def search(e: Expr, ctx: Context) -> List[Tuple[Expr, expr.Location, str]]:
        subexprs = e.find_all_subexpr()
        res = []
        for sube, loc in subexprs:
            for identity in ctx.get_definitions():
                inst = expr.match(sube, identity.rhs)
                if inst:
                    if expr.is_fun(identity.lhs):
                        res.append((sube, loc, identity.lhs.func_name))
                    else:
                        res.append((sube, loc, identity.lhs.name))
        return res

    def eval(self, e: Expr, ctx: Context) -> Expr:
        for identity in ctx.get_definitions():
            if expr.is_fun(identity.lhs) and identity.lhs.func_name == self.func_name:
                inst = expr.match(e, identity.rhs)
                if inst:
                    return normalize(identity.lhs.inst_pat(inst), ctx)

            if expr.is_symbol(identity.lhs) and identity.lhs.name == self.func_name:
                if e == identity.rhs:
                    return identity.lhs

        # Not found
        return e


class IntegralEquation(Rule):
    """Integrate an equation where the left side is a derivative.

    Convert (D a. f(a)) = g(a) into f(a) = INT a. g(a). The right side
    can then be evaluated to produce a Skolem constant.

    """

    def __init__(self):
        self.name = "IntegrateBothSide"

    def eval(self, e: Expr, ctx: Context):
        assert e.is_equals() and expr.is_deriv(e.lhs)

        # Variable to differentiate, this will also be the variable
        # of integration.
        var = e.lhs.var

        # List of Skolem arguments is the free variables on the left side
        skolem_args = tuple(v for v in e.lhs.get_vars() if v != var)

        # Return f(a) = INT a. g(a)
        return Op("=", e.lhs.body, IndefiniteIntegral(var, e.rhs, skolem_args))

    def __str__(self):
        return "integrate both side"

    def export(self):
        return {
            "name": self.name,
            "str": str(self),
        }


class SummationEquation(Rule):
    '''
    a(n) = b(n) => Sum(n, lower, upper ,a(n)) = Sum(n, lower, upper, b(n))
    '''

    def __init__(self, index_var: str, lower: Union[Expr, str], upper: Union[Expr, str]):
        if isinstance(lower, str):
            lower = parser.parse_expr(lower)
        if isinstance(upper, str):
            upper = parser.parse_expr(upper)
        self.name = "SummationEquation"
        self.index_var = index_var
        self.lower = lower
        self.upper = upper

    def eval(self, e: Expr, ctx: Context):
        assert e.is_equals()
        e1 = Summation(self.index_var, self.lower, self.upper, e.lhs)
        e2 = Summation(self.index_var, self.lower, self.upper, e.rhs)
        return Op("=", e1, e2)

    def __str__(self):
        return "sum both side"

    def export(self):
        return {
            "name": self.name,
            "str": str(self),
            'index_var': self.index_var,
            'lower': str(self.lower),
            'upper': str(self.upper)
        }


class ChangeSummationIndex(Rule):
    '''
    sum(n, 1, oo, a(n)) => sum(n, 0, oo, a(n+1))
    '''

    def __init__(self, new_lower: Union[Expr, str]):
        self.name = "ChangeSummationIndex"
        self.new_lower = new_lower if isinstance(new_lower, Expr) else parser.parse_expr(new_lower)

    def eval(self, e: Expr, ctx: Context):
        if not expr.is_summation(e):
            return e
        tmp = normalize(Var(e.index_var, type=expr.IntType) + e.lower - self.new_lower, ctx)
        new_upper = normalize(e.upper + self.new_lower - e.lower, ctx) \
            if e.upper != POS_INF else POS_INF
        return Summation(e.index_var, self.new_lower, new_upper, e.body.replace(Var(e.index_var, type=expr.IntType), tmp))

    def __str__(self):
        return "change summation index"

    def export(self):
        return {
            "name": self.name,
            "str": str(self),
            "new_lower": str(self.new_lower)
        }


class LimitEquation(Rule):
    """Apply limit to both sides of the equation.
    
        A = B -> LIM {x -> a}. A = LIM {x -> a}. B

    """

    def __init__(self, var: str, lim: Expr):
        self.name = "LimitEquation"
        self.var: str = var
        self.lim: Expr = lim

    def __str__(self):
        return "apply limit %s -> %s to equation" % (self.var, self.lim)

    def eval(self, e: Expr, ctx: Context):
        v, lim = self.var, self.lim
        lim1 = Limit(v, lim, e.lhs)
        lim2 = Limit(v, lim, e.rhs)
        return Op('=', lim1, lim2)

    def export(self):
        return {
            "name": self.name,
            "str": str(self),
            "var": self.var,
            "lim": str(self.lim),
            "latex_str": "apply limit \\(%s \\to %s\\) to equation" %
                         (self.var, latex.convert_expr(self.lim))
        }


class IntSumExchange(Rule):
    """Exchange integral and summation"""

    def __init__(self):
        self.name = "IntSumExchange"

    def __str__(self):
        return "exchange integral and sum"

    def test_converge(self, svar, sl, su, ivar, il, iu, body, ctx: Context):
        if ctx.is_not_negative(body):
            return True
        if ctx.is_not_positive(body):
            return True
        if su != expr.POS_INF:
            return True
        abs_body = normalize(Fun("abs", body), ctx)
        goal1 = Fun("converges", Summation(svar, sl, su, Integral(ivar, il, iu, abs_body)))

        abs_int = normalize(Fun("abs", Integral(ivar, il, iu, body)), ctx)
        goal2 = Fun("converges", Summation(svar, sl, su, abs_int))
        for lemma in ctx.get_lemmas():
            if normalize(lemma.expr,ctx) == normalize(goal1,ctx) or \
                    normalize(lemma.expr,ctx) == normalize(goal2,ctx):
                return True
        return False

    def eval(self, e: Expr, ctx: Context):
        if expr.is_integral(e) and expr.is_summation(e.body):
            ctx2 = body_conds(e, body_conds(e.body, ctx))
            s = e.body
            if self.test_converge(s.index_var, s.lower, s.upper, e.var, e.lower, e.upper, e.body.body, ctx2):
                return Summation(s.index_var, s.lower, s.upper, Integral(e.var, e.lower, e.upper, s.body))
        elif expr.is_summation(e) and expr.is_integral(e.body):
            ctx2 = body_conds(e, body_conds(e.body, ctx))
            i = e.body
            if self.test_converge(e.index_var, e.lower, e.upper, i.var, i.lower, i.upper, e.body.body, ctx2):
                return Integral(i.var, i.lower, i.upper, Summation(e.index_var, e.lower, e.upper, i.body))
        return e

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }


class VarSubsOfEquation(Rule):
    """Substitute variable for any expression in an equation.
    """

    def __init__(self, subst: Dict[str, Union[str, Expr]]):
        self.name = "VarSubsOfEquation"
        for i in range(len(subst)):
            if isinstance(subst[i]['expr'], str):
                if subst[i]['expr'] == "":
                    subst[i]['expr'] = None
                else:
                    subst[i]['expr'] = parser.parse_expr(subst[i]['expr'])
        self.subst = subst

    def __str__(self):
        str_of_substs = ', '.join(item['var'] + " for " + str(item['expr']) for item in self.subst
                                  if item['expr'] is not None)
        return "substitute " + str_of_substs + " in equation"

    def export(self):
        latex_str_of_substs = ', '.join('\\(' + item['var'] + "\\) for \\(" + latex.convert_expr(item['expr']) + '\\)'
                                        for item in self.subst if item['expr'] is not None)
        json_substs = list()
        for item in self.subst:
            json_substs.append({'var': item['var'], 'expr': str(item['expr'])})
        return {
            "name": self.name,
            "str": str(self),
            "subst": json_substs,
            "latex_str": "substitute %s in equation" % latex_str_of_substs
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if e.is_equals():
            for item in self.subst:
                if item['expr'] is not None:
                    e = e.subst(item['var'], item['expr'])
            return e
        else:
            return e


class MergeSummation(Rule):
    "SUM(u,0,oo, body1) + SUM(k,0,oo,body2) = SUM(u, 0, oo, body1+body2)"

    def __init__(self):
        self.name = "MergeSummation"

    def __str__(self):
        return "merge summation"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not (e.ty == OP and e.op in ('+', '-') and all([isinstance(arg, Summation) for arg in e.args])):
            return e
        a, b = e.args
        if not (a.lower == b.lower and a.upper == b.upper):
            return e
        if a.index_var != b.index_var:
            b = b.alpha_convert(a.index_var)
        return Summation(a.index_var, a.lower, a.upper, Op(e.op, a.body, b.body))


alphabet = "ijkmnabcdef"
def change_index(e:Expr, bd:List):
    ''' using new index variable for summation '''
    if expr.is_summation(e):
        if e.index_var in bd:
            for var in alphabet:
                if var not in bd:
                    e = e.alpha_convert(var)
                    bd.append(var)
                    break
        else:
            bd.append(e.index_var)
        res = Summation(e.index_var, e.lower, e.upper, change_index(e.body, bd))
        bd.pop()
        return res
    elif expr.is_op(e):
        args = [change_index(arg, bd) for arg in e.args]
        return Op(e.op, *args)
    else:
        return e

class SplitSummation(Rule):
    """
    Split a summation into several summations.
    input: SUM(i, 1, 7, i / (i + 1)), cond: i <= 4
    output: SUM(i, 1, 4, i / (i + 1)) + SUM(i, 5, 7, i / (i + 1))
    Currently, the cond only supports two kinds of input forms: i % k and i < k,
    where i is a variable and k is an integer.
    ('<' can be replaced with other comparison operators, such as '!=')
    The lower and upper of summation should be an integer or inf.
    """

    def __init__(self, cond: Expr):
        self.name = "SplitSummation"
        if isinstance(cond, str):
            cond = parser.parse_expr(cond)
        self.cond = cond

    def __str__(self):
        return "split summation on %s" % self.cond

    def export(self):
        return {
            "name": self.name,
            "str": str(self),
            "cond": str(self.cond),
            "latex_str": "split summation on \\(%s\\)" % latex.convert_expr(self.cond)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not expr.is_summation(e):
            return e

        cond = self.cond
        n = Var(e.index_var, type=expr.IntType)
        eq = expr.Eq(Fun('f', n), e.body)
        eq_pat = eq.subst(e.index_var, Symbol(e.index_var, pat=[VAR, CONST, OP, FUN, INTEGRAL, MATRIX, INF]))
        bd = list(e.get_vars(with_bd=True))
        r0 = ExpandDefinition("f", simp=False)
        r = OnSubterm(r0)
        tmp_ctx = Context(ctx, ctx.d+1)
        tmp_ctx.definitions.append(context.Identity(eq_pat))
        for id in ctx.get_summation_split_identities():
            id: context.Identity
            inst_split_cond = expr.match(cond, id.split_cond)
            if inst_split_cond is not None:
                new_expr = change_index(id.expr, bd)
                new_expr = r.eval(new_expr, tmp_ctx)
                inst_lhs = expr.match(e, new_expr.lhs)
                if inst_lhs is not None:
                    inst_split_cond.update(inst_lhs)
                    tmp_conds = [c.inst_pat(inst_split_cond) for c in id.conds.data]
                    flag = True
                    for c in tmp_conds:
                        if not ctx.check_condition(c):
                            flag = False
                            break
                    if flag:
                        res = new_expr.rhs.inst_pat(inst_split_cond)
                        res = r.eval(res, tmp_ctx)
                        other_vars = res.get_vars(with_bd=True).difference(bd)
                        for var in other_vars:
                            while ctx.d != 0:
                                ctx = ctx.parent
                            ctx.add_fix(var, expr.IntType)
                        return res
        return e


class DerivEquation(Rule):
    """Differentiate both sides with respect to some variable."""

    def __init__(self, var: str):
        self.name = "DerivEquation"
        self.var: str = var

    def __str__(self):
        return "derivate both sides"

    def export(self):
        return {
            "name": self.name,
            "str": str(self),
            "var": self.var
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not e.is_equals():
            return e
        return Op('=', Deriv(self.var, e.lhs), Deriv(self.var, e.rhs))


class SolveEquation(Rule):
    """Solve equation for the given expression."""

    def __init__(self, solve_for: Union[Expr, str]):
        if isinstance(solve_for, str):
            solve_for = parser.parse_expr(solve_for)
        self.solve_for = solve_for
        self.name = "SolveEquation"

    def eval(self, e: Expr, ctx: Context):
        assert e.is_equals()

        res = solve_for_term(e, self.solve_for, ctx)
        if not res:
            raise AssertionError("SolveEquation: cannot solve")
        return Op("=", self.solve_for, normalize(res, ctx))

    def __str__(self):
        return "solve equation for %s" % str(self.solve_for)

    def export(self):
        return {
            "name": self.name,
            "str": str(self),
            "solve_for": str(self.solve_for),
            "latex_str": "solve equation for \\(%s\\)" % latex.convert_expr(self.solve_for)
        }


class FunEquation(Rule):
    """a = b => fun(a) = fun(b) if a,b belong to the domain of f"""

    def __init__(self, func_name: str):
        self.name = "FunEquation"
        self.func_name: str = func_name

    def __str__(self):
        return "function on both sides"

    def export(self):
        return {
            "name": self.name,
            "str": str(self),
            "func_name": self.func_name
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if not e.is_equals():
            return e
        ne = Op('=', Fun(self.func_name, e.lhs), Fun(self.func_name, e.rhs))
        if len(check_wellformed(ne, ctx)) == 0:
            return ne
        return e


class ExpandMatFunc(Rule):
    """Expand functions on matrices."""
    def __init__(self):
        self.name = "ExpandMatFunc"

    def __str__(self):
        return "expand functions of matrices"

    def export(self):
        return {
            "name": self.name,
            "str": str(self)
        }

    def eval(self, e: Expr, ctx: Context) -> Expr:
        if expr.is_var(e):
            if expr.is_matrix_type(e.type):
                r, c = expr.num_row(e.type), expr.num_col(e.type)
                if expr.is_const(r) and expr.is_const(c):
                    # Expand into matrix form
                    return matrix.unfold_matrix(e, r.val, c.val)
            # All other cases: leave unchanged
            return e
        elif e.is_power() and expr.is_matrix(e.args[0]) and e.args[1] == Const(2):
            return matrix.multiply(e.args[0], e.args[0], ctx)
        elif expr.is_fun(e):
            if e.func_name == 'hat' and len(e.args) == 1 and expr.is_matrix_type(e.args[0].type):
                return matrix.hat(e.args[0])
            elif e.func_name == 'unit_matrix' and len(e.args) == 1 and expr.is_const(e.args[0]):
                return matrix.unit_matrix(e.args[0].val)
            elif e.func_name == 'T' and len(e.args) == 1:
                return matrix.transpose(e.args[0])
            elif e.func_name == "zero_matrix" and len(e.args) == 2 and all(expr.is_const(arg) for arg in e.args):
                return matrix.zero_matrix(e.args[0].val, e.args[1].val)
            elif e.func_name == "norm" and len(e.args) == 1 and expr.is_matrix_type(e.args[0].type):
                return matrix.norm(e.args[0])
        return e
