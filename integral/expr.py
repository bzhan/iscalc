"""Expressions."""
import copy
import math
import functools
import operator
from decimal import Decimal
from fractions import Fraction
from collections.abc import Iterable
from typing import Dict, List, Optional, Set, TypeGuard, Tuple, Union, Callable


VAR, CONST, OP, FUN, DERIV, INTEGRAL, EVAL_AT, SYMBOL, LIMIT, INF, INDEFINITEINTEGRAL, \
SKOLEMFUNC, SUMMATION, LAZYSERIES, VECTOR, MATRIX = range(16)

op_priority = {
    "+": 65, "-": 65, "*": 70, "/": 70, "^": 75, "=": 50, "<": 50, ">": 50, "<=": 50, ">=": 50, "!=": 50
}


class Location:
    """Location within an expression."""

    def __init__(self, data):
        if isinstance(data, Iterable) and all(isinstance(n, int) for n in data):
            self.data = tuple(data)
        elif isinstance(data, str):
            if data in (".", ""):
                self.data = tuple([])
            else:
                self.data = tuple(int(n) for n in data.split('.'))
        elif isinstance(data, Location):
            self.data = data.data
        else:
            raise TypeError

    def __str__(self):
        if not self.data:
            return "."
        else:
            return ".".join(str(n) for n in self.data)

    def is_empty(self):
        return len(self.data) == 0

    @property
    def head(self):
        return self.data[0]

    @property
    def rest(self):
        return Location(self.data[1:])

    def append(self, i: int) -> "Location":
        return Location(self.data + (i,))


class Expr:
    """Expressions."""

    def __add__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        return Op("+", self, other)

    def __radd__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        return Op("+", other, self)

    def __sub__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        return Op("-", self, other)

    def __rsub__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        return Op("-", other, self)

    def __mul__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        return Op("*", self, other)

    def __rmul__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        return Op("*", other, self)

    def __truediv__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        if self.is_const() and other.is_const() and isinstance(self.val, int) and isinstance(other.val, int):
            return Const(Fraction(self.val, other.val))
        return Op("/", self, other)

    def __rtruediv__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        return Op("/", other, self)

    def __xor__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        return Op("^", self, other)

    def __pow__(self, other):
        if isinstance(other, (int, Fraction)):
            other = Const(other)
        return Op("^", self, other)

    def __neg__(self):
        if self == POS_INF:
            return NEG_INF
        elif self == NEG_INF:
            return POS_INF
        elif self.is_const() and self.val > 0:
            return Const(-self.val)
        return Op("-", self)

    def size(self):
        if self.ty in (VAR, CONST, SYMBOL, INF):
            return 1
        elif self.is_op() or self.is_fun():
            return 1 + sum(arg.size() for arg in self.args)
        elif self.is_deriv():
            return 1 + self.body.size()
        elif self.ty in (INTEGRAL, EVAL_AT):
            return 1 + self.lower.size() + self.upper.size() + self.body.size()
        elif self.ty == LIMIT:
            return 1 + self.lim.size() + self.body.size()
        elif self.ty == INDEFINITEINTEGRAL:
            return 1 + self.body.size()
        elif self.ty == SKOLEMFUNC:
            return 1 + len(self.dependent_vars)
        elif self.ty == SUMMATION:
            return 1 + self.lower.size() + self.upper.size() + self.body.size()
        elif self.ty == VECTOR:
            return 1 + sum(e.size() for e in self.data)
        elif self.ty == MATRIX:
            return 1 + sum([row.size() for row in self.rows])
        else:
            raise NotImplementedError

    def is_var(self) -> TypeGuard["Var"]:
        return self.ty == VAR

    def is_const(self) -> TypeGuard["Const"]:
        return self.ty == CONST

    def is_op(self) -> TypeGuard["Op"]:
        return self.ty == OP

    def is_fun(self) -> TypeGuard["Fun"]:
        return self.ty == FUN

    def is_deriv(self) -> TypeGuard["Deriv"]:
        return self.ty == DERIV

    def is_skolem_func(self) -> TypeGuard["SkolemFunc"]:
        return self.ty == SKOLEMFUNC

    def is_symbol(self) -> TypeGuard["Symbol"]:
        return self.ty == SYMBOL

    def is_zero(self) -> bool:
        return self.is_const() and self.val == 0

    def is_integral(self) -> bool:
        return self.ty == INTEGRAL

    def is_indefinite_integral(self) -> bool:
        return self.ty == INDEFINITEINTEGRAL

    def is_evalat(self) -> bool:
        return self.ty == EVAL_AT

    def is_limit(self) -> bool:
        return self.ty == LIMIT

    def is_plus(self):
        return self.ty == OP and self.op == '+'

    def is_uminus(self):
        return self.ty == OP and self.op == '-' and len(self.args) == 1

    def is_minus(self):
        return self.ty == OP and self.op == '-' and len(self.args) == 2

    def is_times(self):
        return self.ty == OP and self.op == '*'

    def is_divides(self):
        return self.ty == OP and self.op == '/'

    def is_power(self):
        return self.ty == OP and self.op == '^'

    def is_equals(self):
        return self.ty == OP and self.op == '='

    def is_not_equals(self):
        return self.ty == OP and self.op == "!="

    def is_less(self):
        return self.ty == OP and self.op == "<"

    def is_less_eq(self):
        return self.ty == OP and self.op == "<="

    def is_greater(self):
        return self.ty == OP and self.op == ">"

    def is_greater_eq(self):
        return self.ty == OP and self.op == ">="

    def is_compare(self) -> bool:
        return self.ty == OP and self.op in ('=', '!=', '<', '<=', '>', '>=')

    def is_inf(self):
        return self.ty == INF and (self.t == Decimal("inf") or self.t == Decimal("-inf"))

    def is_pos_inf(self):
        return self.ty == INF and self.t == Decimal("inf")

    def is_neg_inf(self):
        return self.ty == INF and self.t == Decimal("-inf")

    def is_trig(self):
        return self.ty == FUN and self.func_name in ("sin", "cos", "tan", "cot", "csc", "sec")

    def is_inverse_trig(self):
        return self.ty == FUN and self.func_name in ("asin", "acos", "atan", "acot", "acsc", "asec")

    def is_skolem_term(self):
        if self.get_vars() != set():
            return False
        if not self.is_constant():
            return True
        else:
            return False

    def is_odd(self, var, conds) -> bool:
        from integral import poly
        tmp1 = self
        tmp2 = self.subst(var, -Var(var))
        if poly.normalize(tmp1 + tmp2, conds) == Const(0):
            return True
        return False

    def is_summation(self) -> TypeGuard["Summation"]:
        return self.ty == SUMMATION

    @property
    def lhs(self) -> "Expr":
        if self.is_equals():
            return self.args[0]
        else:
            raise AssertionError("lhs: term is not an equality")

    @property
    def rhs(self) -> "Expr":
        if self.is_equals():
            return self.args[1]
        else:
            raise AssertionError("rhs: term is not an equality")

    def __le__(self, other):
        if isinstance(other, (int, Fraction)):
            return False

        if self.size() != other.size():
            return self.size() <= other.size()

        if self.ty != other.ty:
            return self.ty <= other.ty

        if self.is_var():
            return self.name <= other.name
        elif self.is_const():
            return self.val <= other.val
        elif self.is_op():
            return (self.op, self.args) <= (other.op, other.args)
        elif self.is_fun():
            return (self.func_name, self.args) <= (other.func_name, other.args)
        elif self.is_deriv() or self.is_indefinite_integral():
            return (self.body, self.var) <= (other.body, other.var)
        elif self.is_integral() or self.is_evalat():
            return (self.body, self.lower, self.upper, self.var) <= \
                   (other.body, other.lower, other.upper, other.var)
        elif self.is_symbol():
            return sum(self.ty) <= sum(other.ty)
        elif self.is_summation():
            return (self.body, self.lower, self.upper, self.index_var) <= \
                   (other.body, other.lower, other.upper, other.index_var)
        elif self.is_skolem_func():
            return (self.name, self.dependent_vars) <= (other.name, other.dependent_vars)
        elif self.is_limit():
            return (self.var, self.lim, self.body, self.drt) <= (other.var, other.lim, other.body, other.drt)
        elif self.is_vector():
            return (self.is_column, *(item for item in self.data)) <= (other.is_column, *(item for item in other.data))
        elif self.is_matrix():
            return (self.shape[0]*self.shape[1], *(rv for rv in self.rows)) <= (other.shape[0]*other.shape[1], *(rv for rv in other.rows))
        else:
            print(type(self))
            raise NotImplementedError

    def __lt__(self, other):
        return self <= other and self != other

    def __gt__(self, other):
        return other <= self and self != other

    def __ge__(self, other):
        return not self < other

    def priority(self):
        if self.ty in (VAR, SYMBOL, INF, SKOLEMFUNC, LAZYSERIES, VECTOR, MATRIX):
            return 100
        elif self.ty == CONST:
            if isinstance(self.val, Fraction) and self.val.denominator != 1:
                return op_priority['/']
            elif self.val < 0:
                # return 80  # priority of uminus
                return 74
            else:
                return 100
        elif self.ty == OP:
            if len(self.args) == 1:
                return 80  # priority of uminus
            elif self.op in op_priority:
                return op_priority[self.op]
            else:
                raise NotImplementedError
        elif self.ty in (FUN, SUMMATION):
            return 95
        elif self.ty in (DERIV, INTEGRAL, EVAL_AT, INDEFINITEINTEGRAL):
            return 10
        elif self.ty == LIMIT:
            return 5
        else:
            raise NotImplementedError

    def __lt__(self, other):
        return self <= other and self != other

    def get_subexpr(self, loc) -> "Expr":
        """Given an expression, return the subexpression at location."""
        if not isinstance(loc, Location):
            loc = Location(loc)
        if loc.is_empty():
            return self
        elif self.is_var() or self.is_const():
            raise AssertionError("get_subexpr: invalid location")
        elif self.is_op() or self.is_fun():
            assert loc.head < len(self.args), "get_subexpr: invalid location"
            return self.args[loc.head].get_subexpr(loc.rest)
        elif self.is_deriv():
            assert loc.head == 0, "get_subexpr: invalid location"
            return self.body.get_subexpr(loc.rest)
        elif self.is_integral() or self.is_evalat():
            if loc.head == 0:
                return self.body.get_subexpr(loc.rest)
            elif loc.head == 1:
                return self.lower.get_subexpr(loc.rest)
            elif loc.head == 2:
                return self.upper.get_subexpr(loc.rest)
            else:
                raise AssertionError("get_subexpr: invalid location")
        elif self.is_limit():
            assert loc.head == 0, "get_subexpr: invalid location"
            return self.body.get_subexpr(loc.rest)

        else:
            raise NotImplementedError

    def replace_expr(self, loc, new_expr: "Expr") -> "Expr":
        """Replace self's subexpr at location."""
        if not isinstance(loc, Location):
            loc = Location(loc)
        if loc.is_empty():
            return new_expr
        elif self.is_var() or self.is_const():
            raise AssertionError("replace_expr: invalid location")
        elif self.is_op():
            assert loc.head < len(self.args), "replace_expr: invalid location"
            if len(self.args) == 1:
                return Op(self.op, self.args[0].replace_expr(loc.rest, new_expr))
            elif len(self.args) == 2:
                if loc.head == 0:
                    return Op(self.op, self.args[0].replace_expr(loc.rest, new_expr), self.args[1])
                elif loc.head == 1:
                    return Op(self.op, self.args[0], self.args[1].replace_expr(loc.rest, new_expr))
                else:
                    raise AssertionError("replace_expr: invalid location")
            else:
                raise NotImplementedError
        elif self.is_fun():
            assert loc.head < len(self.args), "replace_expr: invalid location"
            arg = self.args[loc.head].replace_expr(loc.rest, new_expr)
            return Fun(self.func_name, arg)
        elif self.is_integral():
            if loc.head == 0:
                return Integral(self.var, self.lower, self.upper, self.body.replace_expr(loc.rest, new_expr))
            elif loc.head == 1:
                return Integral(self.var, self.lower.replace_expr(loc.rest, new_expr), self.upper, self.body)
            elif loc.head == 2:
                return Integral(self.var, self.lower, self.upper.replace_expr(loc.rest, new_expr), self.body)
            else:
                raise AssertionError("replace_expr: invalid location")
        elif self.is_evalat():
            if loc.head == 0:
                return EvalAt(self.var, self.lower, self.upper, self.body.replace_expr(loc.rest, new_expr))
            elif loc.head == 1:
                return EvalAt(self.var, self.lower.replace_expr(loc.rest, new_expr), self.upper, self.body)
            elif loc.head == 2:
                return EvalAt(self.var, self.lower, self.upper.replace_expr(loc.rest, new_expr), self.body)
            else:
                raise AssertionError("replace_expr: invalid location")
        elif self.is_deriv():
            assert loc.head == 0, "replace_expr: invalid location"
            return Deriv(self.var, self.body.replace_expr(loc.rest, new_expr))
        elif self.is_limit():
            assert loc.head == 0, "replace_expr: invalid location"
            return Limit(self.var, self.limit, self.body.replace_expr(loc.rest, new_expr))
        else:
            raise NotImplementedError

    def get_location(self) -> Location:
        """Returns the location at which the 'selected' field is True."""
        location = []

        def get(exp: Expr, loc=''):
            if hasattr(exp, 'selected') and exp.selected == True:
                location.append(loc[1:])
                exp.selected = False  # Once it is found, restore it.
            elif exp.is_op() or exp.is_fun():
                for i in range(len(exp.args)):
                    get(exp.args[i], loc + "." + str(i))
            elif exp.is_integral() or exp.is_evalat():
                get(exp.lower, loc + ".1")
                get(exp.upper, loc + ".2")
                get(exp.body, loc + ".0")
            elif exp.is_deriv() or exp.is_summation() or exp.is_limit():
                get(exp.body, loc + ".0")

        get(self)
        return location[0]

    def find_subexpr(self, subexpr: "Expr") -> List[Location]:
        """Returns the location of a subexpression."""
        locations = []

        def find(e: Expr, loc: Location):
            if e == subexpr:
                locations.append(Location(loc))
            elif e.is_op() or e.is_fun():
                for i, arg in enumerate(e.args):
                    find(arg, loc.append(i))
            elif e.is_integral() or e.is_evalat():
                find(e.lower, loc.append(1))
                find(e.upper, loc.append(2))
                find(e.body, loc.append(0))
            elif e.is_deriv() or e.is_limit() or e.is_indefinite_integral():
                find(e.body, loc.append(0))
            elif e.is_summation():
                find(e.body, loc.append(0))
                find(e.lower, loc.append(1))
                find(e.upper, loc.append(2))

        find(self, Location(""))
        return locations

    def find_subexpr_pred(self, pred: Callable[["Expr"], bool]) -> List[Tuple["Expr", Location]]:
        """Find list of subexpressions satisfying a given predicate.

        Larger expressions are placed later.

        """
        results = []

        def find(e: Expr, loc: Location):
            if e.is_op() or e.is_fun():
                for i, arg in enumerate(e.args):
                    find(arg, loc.append(i))
            elif e.is_integral() or e.is_evalat():
                find(e.lower, loc.append(1))
                find(e.upper, loc.append(2))
                find(e.body, loc.append(0))
            elif e.is_deriv() or e.is_limit() or e.is_indefinite_integral():
                find(e.body, loc.append(0))
            elif e.is_summation():
                find(e.body, loc.append(0))
                find(e.lower, loc.append(1))
                find(e.upper, loc.append(2))

            if pred(e):
                results.append((e, Location(loc)))

        find(self, Location(""))
        return results

    def find_all_subexpr(self) -> List[Tuple["Expr", Location]]:
        return self.find_subexpr_pred(lambda t: True)

    def subst(self, var: str, e: "Expr") -> "Expr":
        """Substitute occurrence of var for e in self."""
        assert isinstance(var, str) and isinstance(e, Expr)
        if self.is_var():
            if self.name == var:
                return e
            else:
                return self
        elif self.is_const():
            return self
        elif self.is_skolem_func():
            return SkolemFunc(self.name, tuple(arg.subst(var, e) for arg in self.dependent_vars))
        elif self.is_symbol():
            return self
        elif self.is_op():
            return Op(self.op, *[arg.subst(var, e) for arg in self.args])
        elif self.is_fun():
            return Fun(self.func_name, *[arg.subst(var, e) for arg in self.args])
        elif self.is_deriv():
            return Deriv(self.var, self.body.subst(var, e))
        elif self.is_limit():
            return Limit(self.var, self.lim.subst(var, e), self.body.subst(var, e))
        elif self.is_inf():
            return self
        elif self.is_integral():
            return Integral(self.var, self.lower.subst(var, e), self.upper.subst(var, e), self.body.subst(var, e))
        elif self.is_indefinite_integral():
            return IndefiniteIntegral(self.var, self.body.subst(var, e), self.skolem_args)
        elif self.is_evalat():
            return EvalAt(self.var, self.lower.subst(var, e), self.upper.subst(var, e), self.body.subst(var, e))
        elif self.is_summation():
            return Summation(self.index_var, self.lower.subst(var, e), self.upper.subst(var, e),
                             self.body.subst(var, e))
        elif self.is_vector():
            return Vector([item.subst(var, e) for item in self.data], self.is_column)
        elif self.is_matrix():
            return Matrix([rv.subst(var,e) for rv in self.rows])
        else:
            print('subst on', self)
            raise NotImplementedError

    def is_constant(self):
        """Determine whether expr is a number.

        Note Inf is not considered to be constants.

        """
        if self.is_const():
            return True
        elif self.is_fun() or self.is_op():
            return all(arg.is_constant() for arg in self.args)
        else:
            return False

    def is_evaluable(self):
        return self.is_constant() or self.is_inf()

    def get_vars(self) -> Set[str]:
        """Obtain the set of variables in self."""
        res = set()

        def rec(t, bd_vars):
            if t.ty == VAR:
                if t.name not in bd_vars:
                    res.add(t.name)
            elif t.ty in (CONST, INF, SKOLEMFUNC):
                return
            elif t.ty in (OP, FUN):
                for arg in t.args:
                    rec(arg, bd_vars)
            elif t.ty == DERIV:
                res.add(t.var)
                rec(t.body, bd_vars + [t.var])
            elif t.ty == LIMIT:
                rec(t.lim, bd_vars + [t.var])
                rec(t.body, bd_vars + [t.var])
            elif t.ty in (INTEGRAL, EVAL_AT):
                rec(t.lower, bd_vars + [t.var])
                rec(t.upper, bd_vars + [t.var])
                rec(t.body, bd_vars + [t.var])
            elif t.ty == INDEFINITEINTEGRAL:
                rec(t.body, bd_vars + [t.var])
            elif t.ty == SUMMATION:
                rec(t.lower, bd_vars + [t.index_var])
                rec(t.upper, bd_vars + [t.index_var])
                rec(t.body, bd_vars + [t.index_var])
            elif t.is_equals():
                rec(t.bd_vars)
                rec(t.rhs, bd_vars)
            elif t.is_vector():
                for item in t.data:
                    rec(item, bd_vars)
            elif t.is_matrix():
                for rv in t.rows:
                    rec(rv, bd_vars)
            else:
                print(t, type(t))
                raise NotImplementedError

        rec(self, [])
        return res

    def has_symbol(self) -> bool:
        if isinstance(self, Symbol):
            return True
        elif isinstance(self, Union[Var, Const, Inf, SkolemFunc]):
            return False
        elif isinstance(self, Integral):
            return self.upper.has_symbol() or self.lower.has_symbol() or self.body.has_symbol()
        elif isinstance(self, IndefiniteIntegral):
            return self.body.has_symbol()
        elif isinstance(self, Union[Op, Fun]):
            return any([arg.has_symbol() for arg in self.args])
        elif isinstance(self, Summation):
            return self.body.has_symbol()
        elif isinstance(self, Limit):
            return self.body.has_symbol() or self.lim.has_symbol()
        elif isinstance(self, Deriv):
            return self.body.has_symbol()
        elif isinstance(self, Vector):
            return any([item.has_symbol() for item in self.data])
        elif isinstance(self, Matrix):
            return any([rv.has_symbol() for rv in self.rows])
        else:
            print(self)
            raise NotImplementedError

    def has_vector(self):
        if self.is_vector() or self.is_matrix():
            return True
        elif isinstance(self, Union[Var, Const, Inf, SkolemFunc, Symbol]):
            return False
        elif isinstance(self, Integral):
            return self.upper.has_vector() or self.lower.has_vector() or self.body.has_vector()
        elif isinstance(self, IndefiniteIntegral):
            return self.body.has_vector()
        elif isinstance(self, Union[Op, Fun]):
            return any([arg.has_vector() for arg in self.args])
        elif isinstance(self, Summation):
            return self.body.has_vector()
        elif isinstance(self, Limit):
            return self.body.has_vector() or self.lim.has_vector()
        elif isinstance(self, Deriv):
            return self.body.has_vector()
        else:
            print(self)
            raise NotImplementedError

    def contains_var(self, x: str) -> bool:
        """Whether self contains variable x."""
        assert isinstance(x, str)
        return x in self.get_vars()

    def replace(self, e: "Expr", repl_e: "Expr") -> "Expr":
        """Replace occurrences of e with repl_e."""
        assert isinstance(e, Expr) and isinstance(repl_e, Expr)
        if self == e:
            return repl_e
        elif self.ty in (VAR, CONST, INF):
            return self
        elif self.is_op():
            return Op(self.op, *[arg.replace(e, repl_e) for arg in self.args])
        elif self.is_fun():
            return Fun(self.func_name, *[arg.replace(e, repl_e) for arg in self.args])
        elif self.is_deriv():
            return Deriv(self.var, self.body.replace(e, repl_e))
        elif self.is_integral():
            return Integral(self.var, self.lower.replace(e, repl_e), self.upper.replace(e, repl_e),
                            self.body.replace(e, repl_e))
        elif self.is_evalat():
            return EvalAt(self.var, self.lower.replace(e, repl_e), self.upper.replace(e, repl_e),
                          self.body.replace(e, repl_e))
        elif self.is_skolem_func():
            return SkolemFunc(self.name, tuple(var.replace(e, repl_e) for var in self.dependent_vars))
        elif self.is_summation():
            return Summation(self.index_var, self.lower, self.upper, self.body.replace(e, repl_e))
        elif self.is_limit():
            return Limit(self.var, self.lim.replace(e, repl_e), self.body.replace(e, repl_e), self.drt)
        elif self.is_vector():
            return Vector([item.replace(e, repl_e) for item in self.data], self.is_column)
        elif self.is_matrix():
            return Matrix([Vector([item.replace(e, repl_e) for item in rv.data], is_column=False) for rv in self.rows])
        else:
            print(self, e, repl_e)
            raise NotImplementedError

    def has_func(self, func_name: str) -> bool:
        # determine whether expression has function called func_name

        if self.is_op():
            args = self.args
            for a in args:
                if a.has_func(func_name):
                    return True
        elif self.is_fun():
            if (self.func_name == func_name):
                return True
            else:
                args = self.args
                for a in args:
                    if a.has_func(func_name):
                        return True
        elif self.is_integral():
            return self.lower.has_func(func_name) or self.upper.has_func(func_name) or self.body.has_func(func_name)
        elif self.is_deriv():
            return self.body.has_func(func_name)
        elif self.is_limit():
            return self.body.has_func(func_name)
        else:
            return False

    def separate_integral(self) -> List[Tuple["Expr", Location]]:
        """Collect the list of all integrals appearing in self."""
        return self.find_subexpr_pred(
            lambda e: e.is_integral() or e.is_indefinite_integral())

    def separate_limits(self) -> List[Tuple["Expr", Location]]:
        """Collect the list of all integrals appearing in self."""
        return self.find_subexpr_pred(lambda e: e.is_limit())

    @property
    def depth(self):
        """Return the depth of expression as an estimate of problem difficulty."""

        def d(expr):
            if expr.ty in (VAR, CONST):
                return 0
            elif expr.ty in (OP, FUN):
                if len(expr.args) == 0:
                    return 1
                return 1 + max([d(expr.args[i]) for i in range(len(expr.args))])
            elif expr.ty in (EVAL_AT, INTEGRAL, DERIV):
                return d(expr.body)
            elif expr.ty == SYMBOL:
                raise TypeError

        return d(self)

    def is_spec_function(self, fun_name):
        """Return true iff e is formed by rational options of fun_name."""
        v = Symbol("v", [VAR, OP, FUN])
        if fun_name == "sin":
            pat1 = sin(v)
        elif fun_name == "cos":
            pat1 = cos(v)
        else:
            return False
        if len(find_pattern(self, pat1)) != 1:
            return False

        def rec(ex):
            if ex.ty == CONST:
                return True
            elif ex.ty == VAR:
                return False
            elif ex.ty == OP:
                return all(rec(arg) for arg in ex.args)
            elif ex.ty == FUN:
                return True if ex.func_name == fun_name else False
            else:
                return False

        return rec(self)

    def nonlinear_subexpr(self):
        """Return nonlinear & nonconstant subexpression."""
        subs = []
        a = Symbol('a', [CONST])
        b = Symbol('b', [CONST])
        x = Symbol('x', [VAR])
        patterns = [a * x, a * x + b, a * x - b, x, b + a * x, a + x, x + a]

        def traverse(exp):
            table = [match(exp, p) for p in patterns]
            is_linear = functools.reduce(lambda x, y: x or y, table)
            if not exp.is_constant() and not is_linear:
                if exp not in subs:
                    subs.append(exp)
            if exp.ty in (OP, FUN):
                for arg in exp.args:
                    traverse(arg)
            elif exp.ty in (INTEGRAL, EVAL_AT, DERIV):
                traverse(exp.body)

        traverse(self)
        if self in subs:
            subs.remove(self)
        return tuple(subs)

    def inst_pat(self, mapping: Dict) -> "Expr":
        """Instantiate by replacing symbols in term with mapping."""
        if self.is_var() or self.is_const() or self.is_inf():
            return self
        elif self.is_symbol():
            if self.name in mapping:
                return mapping[self.name]
            else:
                return self
        elif self.is_op():
            return Op(self.op, *(arg.inst_pat(mapping) for arg in self.args))
        elif self.is_fun():
            return Fun(self.func_name, *(arg.inst_pat(mapping) for arg in self.args))
        elif self.is_skolem_func():
            return SkolemFunc(self.name, tuple(arg.inst_pat(mapping) for arg in self.dependent_vars))
        elif self.is_integral():
            return Integral(self.var, self.lower.inst_pat(mapping), self.upper.inst_pat(mapping),
                            self.body.inst_pat(mapping))
        elif self.is_evalat():
            return EvalAt(self.var, self.lower.inst_pat(mapping), self.upper.inst_pat(mapping),
                          self.body.inst_pat(mapping))
        elif self.is_deriv():
            if self.var in mapping and mapping[self.var].is_var():
                return Deriv(mapping[self.var].name, self.body.inst_pat(mapping))
            return Deriv(self.var, self.body.inst_pat(mapping))
        elif self.is_summation():
            return Summation(self.index_var, self.lower.inst_pat(mapping), self.upper.inst_pat(mapping), \
                             self.body.inst_pat(mapping))
        elif self.is_limit():
            return Limit(self.var, self.lim.inst_pat(mapping), self.body.inst_pat(mapping), self.drt)
        elif self.is_vector():
            return Vector([item.inst_pat(mapping) for item in self.data], self.is_column)
        elif self.is_matrix():
            return Matrix([Vector([item.inst_pat(mapping) for item in rv], rv.is_column) for rv in self.rows])
        else:
            print(type(self))
            raise NotImplementedError

    def has_var(self, var):
        """Check if var occurs in self"""
        assert isinstance(var, Expr) and var.ty == VAR, \
            "%s is not a var" % var
        if self.ty in (VAR, CONST):
            return self == var
        elif self.ty == SKOLEMFUNC:
            return var in self.dependent_vars
        elif self.ty in (OP, FUN):
            return any(subexpr.has_var(var) for subexpr in self.args)
        elif self.ty == DERIV:
            return self.body.has_var(var)
        elif self.ty == INTEGRAL:
            return self.lower.has_var(var) or self.upper.has_var(var) or \
                   self.body.has_var(var)
        elif self.ty == EVAL_AT:
            return self.var != str(var) and (self.body.has_var(var) or \
                                             self.upper.has_var(var) or self.lower.has_var(var))
        else:
            raise NotImplementedError

    def is_vector(self)  -> TypeGuard["Vector"]:
        return isinstance(self, Vector) and self.ty == VECTOR

    def is_matrix(self)  -> TypeGuard["Matrix"]:
        return isinstance(self, Matrix) and self.ty == MATRIX

    def get_type(self) -> str:
        if self.is_constant() or self.is_inf():
            if self.is_const():
                if type(self.val) == int:
                    return 'int'
            return 'real'
        elif self.is_matrix():
            return 'matrix'
        elif self.is_var():
            return self.ty2
        elif self.is_op():
            if self.is_plus():
                a, b = self.args
                if a.get_type() == 'real' and b.get_type() == 'real':
                    return 'real'
                elif a.get_type() == 'matrix' and b.get_type() == 'matrix':
                    # check shapes of a and b
                    return 'matrix'
                elif a.get_type() == 'int' and b.get_type() == 'real':
                    return 'real'
                elif a.get_type() == 'real' and b.get_type() == 'int':
                    return 'real'
                elif a.get_type() == 'int' and b.get_type() == 'int':
                    return 'int'
                else:
                    print(a, b)
                    print(a.get_type(), b.get_type())
                    raise TypeError
            elif self.is_times():
                a, b = self.args
                if a.get_type() == 'real' and b.get_type() == 'real':
                    return 'real'
                elif a.get_type() == 'real' and b.get_type() == 'matrix':
                    return 'matrix'
                elif a.get_type() == 'matrix' and b.get_type() == 'real':
                    return 'matrix'
                elif a.get_type() == 'matrix' and b.get_type() == 'matrix':
                    # check shapes of a and b
                    return 'matrix'
                elif a.get_type() == 'int' and b.get_type() == 'real':
                    return 'real'
                elif a.get_type() == 'real' and b.get_type() == 'int':
                    return 'int'
                else:
                    print(a,b)
                    print(a.get_type(), b.get_type())
                    raise TypeError
            elif self.is_divides():
                a, b = self.args
                if a.get_type() == 'real' and b.get_type() == 'real':
                    return 'real'
                elif a.get_type() == 'int' and b.get_type() == 'real':
                    return 'real'
                elif a.get_type() == 'real' and b.get_type() == 'int':
                    return 'real'
                print(a,b,a.get_type(), b.get_type())
                raise NotImplementedError
            elif self.is_uminus() or self.is_minus():
                a = self.args[0]
                if a.get_type() == 'real':
                    return 'real'
                elif a.get_type() == 'matrix':
                    return 'matrix'
                else:
                    raise NotImplementedError
            elif self.is_power():
                a, b = self.args
                if a.get_type() == 'matrix' and b.get_type() == 'int':
                    return 'matrix'
                elif a.get_type() == 'real' and b.get_type() == 'real':
                    return 'real'
                elif a.get_type() == 'real' and b.get_type() == 'int':
                    return 'real'
                elif a.get_type() == 'int' and b.get_type() == 'real':
                    return 'real'
                elif a.get_type() == 'matrix' and b.get_type == 'int':
                    # TODO: check whether a is a squre matrix and b > 0
                    return 'matrix'
                print(a, b)
                print(a.get_type(), b.get_type())
                raise NotImplementedError
        elif self.is_fun():
            a = self.args[0]
            if self.func_name in ('hat','trans','inv','exp') and a.get_type() == 'matrix':
                return 'matrix'
            elif self.func_name in ('unit_matrix','zero_matrix'):
                return 'matrix'
            else:
                return 'real'
        elif self.is_integral():
            if self.body.get_type() in ('int', 'real'):
                return 'real'
            print(self.body, self.body.get_type())
            raise NotImplementedError
        elif self.is_indefinite_integral():
            return 'real'
        elif self.is_summation():
            return 'real'
        elif self.is_evalat():
            return 'real'
        elif self.is_equals():
            return 'equation'
        elif self.is_greater():
            return 'greater'
        elif self.is_deriv():
            return 'real'
        elif self.is_limit():
            return 'real'
        elif self.is_skolem_func():
            return 'real'
        elif self.is_symbol():
            return 'real'
        elif self.is_skolem_term():
            return 'real'
        else:
            print(self)
            raise NotImplementedError

    def get_shape(self):
        if self.is_var():
            return self.shape
        elif self.is_fun():
            if self.func_name == 'inv':
                return self.args[0].shape
            raise NotImplementedError
        elif self.is_op():
            a, b = self.args
            if self.is_times():
                shape1 = a.get_shape()
                shape2 = b.get_shape()
                # check shape1[1] = shape2[0]
                return (shape1[0], shape2[1])
            raise NotImplementedError
        else:
            print(self)
            raise NotImplementedError


def match(exp: Expr, pattern: Expr) -> Optional[Dict]:
    """Match expr with given pattern.

    If successful, return a dictionary mapping symbols to expressions.
    Otherwise returns None.

    """
    d = dict()

    def rec(exp: Expr, pattern: Expr, bd_vars: Dict[str, str]):
        if isinstance(pattern, Symbol):
            if pattern.name in d:
                return exp == d[pattern.name]
            # Check exp does not contain bound variables
            for var in exp.get_vars():
                if var in bd_vars.values():
                    return False
            if exp.ty in pattern.pat:
                d[pattern.name] = exp
                return True
            else:
                return False
        if exp.ty != pattern.ty:
            return False
        if exp.is_var():
            return pattern.name == exp.name or \
                (pattern.name in bd_vars and bd_vars[pattern.name] == exp.name)
        elif exp.is_const():
            return pattern.val == exp.val
        elif exp.is_op():
            if exp.op != pattern.op or len(exp.args) != len(pattern.args):
                return False
            for i in range(len(exp.args)):
                if not rec(exp.args[i], pattern.args[i], bd_vars):
                    return False
            return True
        elif exp.is_fun():
            if exp.func_name != pattern.func_name or len(exp.args) != len(pattern.args):
                return False
            for i in range(len(exp.args)):
                if not rec(exp.args[i], pattern.args[i], bd_vars):
                    return False
            return True
        elif exp.is_skolem_func():
            if exp.name != pattern.name or len(exp.dependent_vars) != len(pattern.dependent_vars):
                return False
            for i in range(len(exp.dependent_vars)):
                if not rec(exp.dependent_vars[i], pattern.dependent_vars[i], bd_vars):
                    return False
            return True
        elif exp.is_indefinite_integral():
            # Note this ignores set of skolem arguments
            bd_vars[pattern.var] = exp.var
            res = rec(exp.body, pattern.body, bd_vars)
            del bd_vars[pattern.var]
            return res
        elif exp.is_integral():
            bd_vars[pattern.var] = exp.var
            res1 = rec(exp.upper, pattern.upper, bd_vars)
            res2 = rec(exp.lower, pattern.lower, bd_vars)
            res3 = rec(exp.body, pattern.body, bd_vars)
            del bd_vars[pattern.var]
            return res1 and res2 and res3
        elif exp.is_summation():
            bd_vars[pattern.index_var] = exp.index_var
            res1 = rec(exp.upper, pattern.upper, bd_vars)
            res2 = rec(exp.lower, pattern.lower, bd_vars)
            res3 = rec(exp.body, pattern.body, bd_vars)
            del bd_vars[pattern.index_var]
            return res1 and res2 and res3
        elif exp.is_inf():
            return exp.t == pattern.t
        elif exp.is_limit():
            bd_vars[pattern.var] = exp.var
            res1 = rec(exp.body, pattern.body, bd_vars)
            res2 = rec(exp.lim, pattern.lim, bd_vars)
            del bd_vars[pattern.var]
            return res1 and res2
        elif exp.is_vector():
            if exp.is_column != pattern.is_column or exp.dim != pattern.dim:
                return False
            return all([rec(item, pattern.data[idx], bd_vars) for (idx, item) in enumerate(exp.data)])
        elif exp.is_matrix():
            if exp.shape != pattern.shape:
                return False
            return all([all([rec(item, pattern.rows[i].data[j], bd_vars)\
                        for (j,item) in enumerate(exp.rows[i].data)])\
                        for (i, rv) in enumerate(exp.rows)])
        else:
            # Currently not implemented
            print("Match Failed")
            return False

    bd_vars = dict()
    if rec(exp, pattern, bd_vars):
        return d
    else:
        return None


def expr_to_pattern(e: Expr) -> Expr:
    """Convert an expression to pattern."""
    vars = e.get_vars()
    for var in vars:
        e = e.subst(var, Symbol(var, [VAR, CONST, OP, FUN, INTEGRAL, MATRIX]))
    return e


def find_pattern(expr, pat, transform=None):
    """Find all subexpr can be matched with the given pattern.

    Return a list of: matched expression, location, mapping of symbols.
    If the transform function is provided, first apply it to the mapping
    of symbols.

    """
    c = []

    def rec(e, pat, cur_loc):
        mapping = match(e, pat)
        if mapping:
            if transform is None:
                c.append((e, cur_loc, mapping))
            else:
                c.append((e, cur_loc, transform(mapping)))
        if e.ty in (OP, FUN):
            for i in range(len(e.args)):
                rec(e.args[i], pat, cur_loc + (i,))
        elif e.ty in (INTEGRAL, DERIV, EVAL_AT):
            rec(e.body, pat, cur_loc + (0,))

    rec(expr, pat, tuple())
    return c


def collect_spec_expr(expr, symb):
    c = [p.args[0] for p, _, _ in find_pattern(expr, symb) if len(p.args) != 0]
    return c


def decompose_expr_factor(e):
    """Get production factors from expr."""
    num_factors, denom_factors = [], []
    def rec(e: Expr, sign):
        if e.is_times():
            rec(e.args[0], sign)
            rec(e.args[1], sign)
        elif e.is_uminus():
            num_factors.append(Const(-1))
            rec(e.args[0], sign)
        elif e.is_divides():
            rec(e.args[0], sign)
            rec(e.args[1], -1 * sign)
        elif sign == 1:
            num_factors.append(e)
        else:
            denom_factors.append(e)
    rec(e, 1)
    return num_factors, denom_factors



class Var(Expr):
    """Variable."""

    def __init__(self, name: str, ty2:str=None, shape:List[Expr]=None):
        assert isinstance(name, str)
        self.ty = VAR
        self.name = name
        if ty2 is None:
            self.ty2 = 'real'
            self.shape = (Const(1), Const(1))
        else:
            if ty2 == 'matrix':
                self.ty2 = ty2
                self.shape = shape
            elif ty2 == 'int':
                self.ty2 = ty2
                self.shape = (Const(1), Const(1))
            else:
                raise NotImplementedError



    def __hash__(self):
        return hash((VAR, self.name, self.ty2, self.shape))

    def __eq__(self, other):
        return isinstance(other, Var) and self.name == other.name and self.ty2 == other.ty2\
        and self.shape == other.shape

    def __str__(self):
        if self.ty2 == 'real':
            return self.name
        elif self.ty2 == 'matrix':
            return self.ty2+" "+self.name+"["+str(self.shape[0])+"]["+str(self.shape[1])+"]"
        elif self.ty2 == 'int':
            return self.ty2+" "+self.name
        else:
            raise NotImplementedError
    def __repr__(self):
        return "Var(%s)" % self.name


class Const(Expr):
    """Constants."""

    def __init__(self, val: Union[int, Fraction]):
        assert isinstance(val, (int, Fraction))
        self.ty = CONST
        if isinstance(val, Fraction) and val.denominator == 1:
            self.val = val.numerator
        else:
            self.val = val

    def __hash__(self):
        return hash((CONST, self.val))

    def __eq__(self, other):
        return isinstance(other, Const) and self.val == other.val

    def __str__(self):
        return str(self.val)

    def __repr__(self):
        return "Const(%s)" % str(self.val)


class Op(Expr):
    """Operators."""

    def __init__(self, op: str, *args):
        assert isinstance(op, str) and all(isinstance(arg, Expr) for arg in args), str([type(arg) for arg in args])
        if len(args) == 1:
            assert op == "-"
        elif len(args) == 2:
            assert op in ["+", "-", "*", "/", "^", "=", "!=", "<", "<=", ">", ">="]
        else:
            raise NotImplementedError
        self.ty = OP
        self.op = op
        self.args = tuple(args)

    def __hash__(self):
        return hash((OP, self.op, tuple(self.args)))

    def __eq__(self, other):
        return isinstance(other, Op) and self.op == other.op and self.args == other.args

    def __str__(self):
        if len(self.args) == 1:
            a, = self.args
            s = str(a)
            if a.priority() < self.priority():
                s = "(%s)" % s
            return "%s%s" % (self.op, s)
        elif len(self.args) == 2:
            a, b = self.args
            if self.op == '/' and a.is_const() and b.is_const() and isinstance(a.val, int) and isinstance(b.val, int):
                return "%s/%s" % (a.val, b.val)
            s1, s2 = str(a), str(b)
            if a.priority() < op_priority[self.op]:
                s1 = "(%s)" % s1
            if b.priority() <= op_priority[self.op]:
                s2 = "(%s)" % s2
            if a.priority() > op_priority[self.op]:
                if a.is_uminus() and self.op == '^':
                    s1 = "(%s)" % s1
            return "%s %s %s" % (s1, self.op, s2)
        else:
            raise NotImplementedError

    def __repr__(self):
        return "Op(%s,%s)" % (self.op, ",".join(repr(arg) for arg in self.args))


class Fun(Expr):
    """Functions."""

    def __init__(self, func_name: str, *args):
        assert isinstance(func_name, str) and all(isinstance(arg, Expr) for arg in args)

        self.ty = FUN
        self.func_name = func_name
        self.args = tuple(args)

    def __hash__(self):
        return hash((FUN, self.func_name, self.args))

    def __eq__(self, other):
        return isinstance(other, Fun) and self.func_name == other.func_name and self.args == other.args

    def __str__(self):
        if len(self.args) > 0:
            return "%s(%s)" % (self.func_name, ",".join(str(arg) for arg in self.args))
        else:
            return self.func_name

    def __repr__(self):
        if len(self.args) > 0:
            return "Fun(%s,%s)" % (self.func_name, ",".join(repr(arg) for arg in self.args))
        else:
            return "Fun(%s)" % self.func_name


class Limit(Expr):
    """Limit expression.

    - var: variable which approaches the limit
    - lim: variable
    - body: expression
    - dir: limit side

    """

    def __init__(self, var: str, lim: Expr, body: Expr, drt=None):
        assert isinstance(var, str) and isinstance(lim, Expr) and isinstance(body, Expr), \
            "Illegal expression: %s %s %s" % (type(var), type(lim), type(body))
        self.ty = LIMIT
        self.var = var
        self.lim = lim
        self.body = body
        self.drt = drt

    def __eq__(self, other):
        return isinstance(other, Limit) and other.var == self.var and \
               other.drt == self.drt and self.lim == other.lim and \
               self.body == other.body

    def __hash__(self):
        return hash((LIMIT, self.var, self.lim, self.body, self.drt))

    def __str__(self):
        if self.lim == inf() or self.lim == neg_inf():
            return "LIM {%s -> %s}. %s" % (self.var, self.lim, self.body)
        else:
            return "LIM {%s -> %s %s}. %s" % (
                self.var, self.lim, self.drt if self.drt != None else "", self.body)

    def __repr__(self):
        if self.lim == inf() or self.lim == neg_inf():
            return "Limit(%s, %s, %s)" % (self.var, self.lim, self.body)
        else:
            return "Limit(%s, %s%s, %s)" % (
                self.var, self.lim, "" if self.drt == None else self.drt, self.body)


class Inf(Expr):
    """The infinity."""

    def __init__(self, t):
        assert t in (Decimal("inf"), Decimal("-inf"))
        self.ty = INF
        self.t = t

    def __str__(self):
        if self.t == Decimal("inf"):
            return "oo"
        else:
            return "-oo"

    def __repr__(self):
        return "Inf(%s)" % self.t

    def __hash__(self):
        return hash((INF, self.t))

    def __eq__(self, other):
        return isinstance(other, Inf) and self.t == other.t

    def keys(self):
        return ('ty', 't')

    def __getitem__(self, item):
        return getattr(self, item)


class SkolemFunc(Expr):
    """Skolem variable or function"""
    def __init__(self, name, dep_vars: Tuple[Expr]):
        self.ty = SKOLEMFUNC
        self.name = name
        self.dependent_vars = tuple(dep_vars)

    def __eq__(self, other):
        return isinstance(other, SkolemFunc) and \
            self.dependent_vars == other.dependent_vars and self.name == other.name

    def __str__(self):
        if not self.dependent_vars:
            return "SKOLEM_CONST(" + self.name + ")"
        else:
            return "SKOLEM_FUNC(" + self.name + "(" + ", ".join(str(var) for var in self.dependent_vars) + "))"

    def __hash__(self):
        return hash((self.name, tuple(self.dependent_vars), self.ty))


class Vector(Expr):
    """ Vector """

    @staticmethod
    def zero(dim: int, is_column=True) -> 'Vector':
        return Vector([Const(0) for i in range(dim)], is_column=is_column)
    @property
    def norm(self) -> Expr:

        return Fun("sqrt", functools.reduce(operator.add, (x^2 for x in self.data[1:]), self.data[0]^2))

    def __init__(self, data: List[Expr], is_column=True):
        self.data = copy.deepcopy(data)
        self.dim = len(self.data)
        self.is_column = is_column
        self.is_row = not is_column
        self.ty = VECTOR

    def __getitem__(self, item) -> Expr:
        return self.data[item]

    def __hash__(self):
        return hash(tuple(self.data+[self.ty, self.is_column]))

    def transpose(self) -> 'Vector':
        # get transpose of the vector
        return Vector(self.data, is_column=not self.is_column)

    def get_w(self):
        assert self.is_column and self.dim == 6
        return Vector(self.data[3:])

    def get_v(self):
        assert self.is_column and self.dim == 6
        return Vector(self.data[0:3])

    def __eq__(self, other):
        return isinstance(other, Vector) and self.is_column == other.is_column and \
               self.data == other.data

    @property
    def t(self):
        return self.transpose()

    @property
    def hat(self):
        # if self.is_row:
        #     raise ValueError("hat operator can only apply to column vectors")
        if self.dim == 3:
            # get skew matrix of the 3-dimension vector
            # formula 2.4 at page 26 of a mathematical introduction of robotic manipulation
            rows = [Vector([Const(0), -self.data[2], self.data[1]], is_column=False),
                   Vector([self.data[2], Const(0), -self.data[0]], is_column=False),
                   Vector([-self.data[1], self.data[0], Const(0)], is_column=False)]
            return Matrix(rows)
        elif self.dim == 6:
            # get the matrix in se(3) form
            # formula 2.26 at page 39
            v, w = self.get_v(), self.get_w()
            return w.hat.concatenate(v, col_concatenate=True). \
                concatenate(Vector.zero(4, is_column=False), col_concatenate=False)
        else:
            raise NotImplementedError

    def __mul__(self, other: Union['Vector', 'Matrix']):
        if isinstance(other, Vector):
            if self.dim != other.dim:
                raise ValueError("can not evaluate this multiplication")
            if self.is_row and other.is_column:
                res = None
                for i in range(self.dim):
                    if i == 0:
                        res = self[i] * other[i]
                    else:
                        res = res + self[i] * other[i]
                return res
            elif self.is_column and other.is_row:
                res = []
                for a in self.data:
                    tmp = []
                    for b in other.data:
                        tmp.append(a*b)
                    res.append(Vector(tmp, is_column=False))
                return Matrix(res)

        elif isinstance(other, Matrix):
            if self.is_row:
                if self.dim != other.shape[0]:
                    raise ValueError("the dimension of vector is not equal to the number of matrix's rows")
                else:
                    return Vector([self*other.get_col(i) for i in range(other.shape[1])], is_column=False)
            else:
                raise NotImplementedError
        else:
            raise NotImplementedError
    def __add__(self, other:'Vector'):
        assert self.is_column == other.is_column and self.dim == other.dim
        return Vector([self.data[i] + other.data[i] for i in range(self.dim)], is_column=self.is_column)

    def __sub__(self, other: 'Vector'):
        assert self.is_column == other.is_column and self.dim == other.dim
        return Vector([self.data[i] - other.data[i] for i in range(self.dim)], is_column=self.is_column)

    def concatenate(self, other: Union['Matrix', 'Vector'], col_concatenate: bool = True) -> Union['Matrix', 'Vector']:
        if isinstance(other, Vector):
            if self.dim == other.dim and \
                    (self.is_column and other.is_column or self.is_row and other.is_row):
                if self.is_column:
                    if col_concatenate:
                        res = [[self[i] if j == 0 else other[i] for j in range(2)]
                               for i in range(self.dim)]
                        return Matrix((self.dim, 2), res)
                    else:
                        res = [self[i] if i < self.dim else other[i - self.dim]
                               for i in range(self.dim * 2)]
                        return Vector(res)
                else:
                    if col_concatenate:
                        res = [self[i] if i < self.dim else other[i - self.dim]
                               for i in range(self.dim * 2)]
                        return Vector(res, False)
                    else:
                        res = [[self[j] if i == 0 else other[j] for j in range(self.dim)] for i in range(2)]
                        return Matrix((2, self.dim), res)
            else:
                return ValueError("can't concatenate these two vectors")
        elif isinstance(other, Matrix):
            if col_concatenate:
                if self.is_column and self.dim == other.shape[0]:
                    cols = other.cols
                    arr = Matrix.vectors2arr([self, ] + cols, is_row_vectors=False)
                    return Matrix((self.dim, len(cols) + 1), arr)
                else:
                    return ValueError("can't concatenate this vector with the matrix")
            else:
                if self.is_row and self.dim == other.shape[1]:
                    rows = other.rows
                    arr = Matrix.vectors2arr([self, ] + rows, is_row_vectors=True)
                    return Matrix((len(rows) + 1, self.dim), arr)
                else:
                    return ValueError("can't concatenate this vector with the matrix")
        else:
            raise TypeError

    def __str__(self):
        res = "{" + ", ".join(str(item) for item in self.data) + "}"
        if self.is_row:
            return res
        else:
            return "column("+res+")"

    def get_angle_velocity(self):
        assert self.is_column and self.dim == 6
        return Vector(self.data[3:], is_column=True)

    def get_line_velocity(self):
        assert self.is_column and self.dim == 6
        return Vector(self.data[:3], is_column=True)

    @staticmethod
    def scalar_mul(t, v: 'Vector'):
        return Vector([t * e for e in v.data], is_column=v.is_column)

    @staticmethod
    def row_one(idx:int, dim:int):
        return Vector([Const(0) if idx != i else Const(1) for i in range(dim)], is_column=False)


class Matrix(Expr):
    """ Matrix """

    def __init__(self, vectors: List[Vector], is_row=True):
        assert len(vectors) != 0 and all(v.dim == vectors[0].dim for v in vectors)
        self.ty = MATRIX
        self.rows = []  # row vectors
        self.cols = []  # column vectors
        if is_row:
            self.shape = (len(vectors), vectors[0].dim)
            for row_vec in vectors:
                self.rows.append(row_vec)
            for j in range(self.shape[1]):
                tmp = []
                for i in range(self.shape[0]):
                    tmp.append(self.rows[i][j])
                self.cols.append(Vector(tmp, is_column=True))
        else:
            self.shape = (vectors[0].dim, len(vectors))
            for col_vec in vectors:
                self.cols.append(col_vec)
            for i in range(self.shape[0]):
                tmp = []
                for j in range(self.shape[1]):
                    tmp.append(self.cols[j][i])
                self.rows.append(Vector(tmp, is_column=False))


    @staticmethod
    def unit_matrix(dim: int):
        return Matrix([Vector.row_one(i, dim) for i in range(dim)])

    @staticmethod
    def homo_matrix(R, p):
        row = Vector([Const(0), Const(0), Const(0), Const(1)], is_column=False)
        return R.concatenate(p).concatenate(row, col_concatenate=False)


    def __hash__(self):
        res = []
        for row in self.rows:
            res.append(row)
        res.append(self.ty)
        res = res + list(self.shape)
        return hash(tuple(res))

    @staticmethod
    def scalar_mul(scalar: Expr, mat: 'Matrix'):
        arr = mat.data
        return Matrix(mat.shape, [[scalar * mat[i][j] for j in range(mat.shape[1])]
                                  for i in range(mat.shape[0])])

    def __add__(self, other: 'Matrix'):
        assert isinstance(other, Matrix) and self.shape == other.shape
        return Matrix([rv + other.rows[i] for (i, rv) in enumerate(self.rows)])

    def is_orthogonal(self):
        # A * A.t = I
        return self.shape[0] == self.shape[1] and \
               self * self.transpose() == Matrix.unit_matrix(self.shap[0])

    @staticmethod
    def vectors2arr(vectors: List[Vector], is_row_vectors=True):
        '''
            if is_row_vector = True
                [[1,2,3],[2,3,4]] these two vectors are treated as row vector
                then the final resulting matrix is [[1,2,3],[2,3,4]]
            else
                this two vectors are treated as column vector
                then the final resulting matrix is [[1,2],[2,3],[3,4]]
        '''
        arr = []
        if is_row_vectors:
            for vec in vectors:
                arr.append(copy.deepcopy(vec.data))
        else:
            m = len(vectors)
            n = vectors[0].dim
            arr = [[0 for j in range(m)] for i in range(n)]
            for i in range(n):
                for j in range(m):
                    arr[i][j] = vectors[j][i]
        return arr

    def transpose(self):
        return Matrix([col.t for col in self.cols])

    def get_row(self, idx):
        return self.rows[idx]

    def get_col(self, idx):
        return self.cols[idx]

    def concatenate(self, other: Union['Matrix', 'Vector'], col_concatenate=True):
        if isinstance(other, Matrix):
            if col_concatenate:
                assert self.shape[0] == other.shape[0]
                arr = Matrix.vectors2arr(self.cols + other.cols, is_row_vectors=False)
                return Matrix((self.shape[0], self.shape[1] + other.shape[1]), arr)
            else:
                assert self.shape[1] == other.shape[1]
                arr = Matrix.vectors2arr(self.rows + other.rows, is_row_vectors=True)
                return Matrix((self.shape[0] + other.shape[0], self.shape[1]), arr)
        elif isinstance(other, Vector):
            if col_concatenate:
                assert other.is_column and other.dim == self.shape[0]
                arr = Matrix.vectors2arr(self.cols + [other, ], is_row_vectors=False)
                return Matrix((self.shape[0], self.shape[1] + 1), arr)
            else:
                assert other.is_row and other.dim == self.shape[1]
                arr = Matrix.vectors2arr(self.rows + [other, ], is_row_vectors=True)
                return Matrix((self.shape[0] + 1, self.shape[1]), arr)

        else:
            raise TypeError

    def is_se3(self):
        return self.shape == (4, 4) and self.get_row(3) == Vector.zero(4, is_column=False)



    def __eq__(self, other: 'Matrix'):
        return isinstance(other, Matrix) and self.ty == other.ty and self.shape == other.shape and\
               self.rows == other.rows and self.cols == other.cols


    def __sub__(self, other: Union['Matrix','Expr']):
        if isinstance(other, Matrix) and self.shape == other.shape:
            return Matrix([rv-other.rows[i] for (i, rv) in enumerate(self.rows)])
        else:
            return Op('-', self, other)
    def is_so3(self):
        if self.shape != (3, 3) and not self.is_skew():
            return False
        for i in range(3):
            for j in range(3):
                if i == j and self.data[i][j] != Const(0):
                    return False
        return True

    @property
    def vee(self) -> 'Vector':
        if self.is_se3():
            # formula 2.30 at page 41
            w_hat: 'Matrix' = self.get_lt33()
            v: 'Vector' = self.get_rt31()
            return v.concatenate(w_hat.vee, col_concatenate=False)
        elif self.is_so3():
            return Vector([self.data[2][1], self.data[0][2], self.data[1][0]], is_column=True)
        else:
            raise NotImplementedError

    def get_lt33(self):
        # get the left top 3*3 matrix
        if self.shape[0] < 3 or self.shape[1] < 3:
            return None
        arr = [[0 for i in range(3)] for j in range(3)]
        for i in range(3):
            for j in range(3):
                arr[i][j] = self.data[i][j]
        return Matrix((3, 3), arr)

    def get_rt31(self):
        # get the right top 3*1 vector
        if self.shape[0] < 3:
            return None
        arr = [0 for i in range(3)]
        for i in range(3):
            arr[i] = self.data[i][-1]
        return Vector(arr, is_column=True)

    def det(self):
        # calculate determinant
        return Const(1)

    def is_SO3(self):
        return self.is_orthogonal() and self.det() == Const(1)

    def is_SE3(self):
        # Example A.4 at page 409
        if self.shape != (4, 4):
            return False
        R = self.get_lt33()
        p = self.get_rt31()
        # R.is_skew R.is_orthogonal
        return R.is_SO3() and  p.dim == 3

    @staticmethod
    def zero(shape:Tuple[int]):
        return Matrix([Vector.zero(shape[1],is_column=False) for i in range(shape[0])])

    @property
    def t(self):
        return self.transpose()

    def adjoint(self, inverse=False):
        # assert self.is_SE3()
        # formula 2.58 at page 55
        R = self.get_lt33()
        p = self.get_rt31()
        Zero = Matrix.zero((3,3))
        if not inverse:
            part1 = R.concatenate(p.hat * R, col_concatenate=True)
            part2 = Zero.concatenate(R, col_concatenate=True)
            return part1.concatenate(part2, col_concatenate=False)
        else:
            # at page 56
            part1 = R.t.concatenate(Matrix.scalar_mul(Const(-1), (R.t * p.hat)))  # scalar operation for matrix
            part2 = Zero.concatenate(R.t)
            return part1.concatenate(part2, col_concatenate=False)

    def __getitem__(self, item):
        if self.shape[0] == 1:
            return self.data[0][item]
        if self.shape[1] == 1:
            return self.data[item][0]
        res = Matrix((1, self.shape[1]), [self.data[item]])
        return res

    def __mul__(self, other: Union['Matrix', 'Vector', 'Expr']):
        if isinstance(other, Matrix):
            assert self.shape[1] == other.shape[0]
            res = []
            for (i, rv) in enumerate(self.rows):
                tmp = []
                for (j, cv) in enumerate(other.cols):
                    tmp.append(rv * cv)
                res.append(Vector(tmp, is_column=False))
            return Matrix(res)
        elif isinstance(other, Vector):
            if other.is_column:
                if self.shape[1] != other.dim:
                    raise ValueError
                else:
                    arr = []
                    for i in range(self.shape[0]):
                        arr.append(self.rows[i] * other)
                    return Vector(arr, is_column=True)
            else:
                raise NotImplementedError
        else:
            # raise NotImplementedError(str(self)+"%%%"+str(other))
            if other.has_vector():
                return Op('*', self, other)
            else:
                return Op('*', other, self)

    def __str__(self):
        return "{"+", ".join(str(row) for row in self.rows)+"}"

    @staticmethod
    def diagonal(arr:List[Expr]):
        dim = len(arr)
        res = [[arr[i] if i==j else Const(0) for j in range(dim)] for i in range(dim)]
        return Matrix((dim, dim), res)

NEG_INF = Inf(Decimal('-inf'))
POS_INF = Inf(Decimal('inf'))
ZERO = Const(0)

def inf():
    return Inf(Decimal("inf"))

def neg_inf():
    return Inf(Decimal("-inf"))

def sin(e):
    return Fun("sin", e)

def cos(e):
    return Fun("cos", e)

def tan(e):
    return Fun("tan", e)

def cot(e):
    return Fun("cot", e)

def sec(e):
    return Fun("sec", e)

def csc(e):
    return Fun("csc", e)

def log(e):
    return Fun("log", e)

def exp(e):
    return Fun("exp", e)

def arcsin(e):
    return Fun("asin", e)

def arccos(e):
    return Fun("acos", e)

def arctan(e):
    return Fun("atan", e)

def sqrt(e):
    return Fun("sqrt", e)


def binom(e1: Expr, e2: Expr) -> Expr:
    """Binomial coefficients"""
    return Fun("binom", e1, e2)


def factorial(e: Expr) -> Expr:
    """Factorial of e"""
    return Fun('factorial', e)


pi = Fun("pi")
E = Fun("exp", Const(1))
G = Fun("G")


def Eq(s: Expr, t: Expr) -> Expr:
    return Op("=", s, t)


class Deriv(Expr):
    """Derivative of an expression."""

    def __init__(self, var: str, body: Expr):
        assert isinstance(var, str) and isinstance(body, Expr)
        self.ty = DERIV
        self.var: str = var
        self.body: Expr = body

    def __hash__(self):
        return hash((DERIV, self.var, self.body))

    def __eq__(self, other):
        return isinstance(other, Deriv) and self.var == other.var and self.body == other.body

    def __str__(self):
        return "D %s. %s" % (self.var, str(self.body))

    def __repr__(self):
        return "Deriv(%s,%s)" % (self.var, repr(self.body))


class IndefiniteIntegral(Expr):
    """Indefinite integral of an expression."""

    def __init__(self, var: str, body: Expr, skolem_args: Tuple[str]):
        assert isinstance(var, str) and isinstance(body, Expr)
        self.ty = INDEFINITEINTEGRAL
        self.var = var
        self.body = body
        self.skolem_args = tuple(skolem_args)

    def __hash__(self):
        return hash((INDEFINITEINTEGRAL, self.var, self.body, self.skolem_args))

    def __eq__(self, other):
        return isinstance(other, IndefiniteIntegral) and self.body == other.alpha_convert(self.var).body and \
            self.skolem_args == other.skolem_args

    def __str__(self):
        if self.skolem_args:
            return "INT %s [%s]. %s" % (self.var, ', '.join(self.skolem_args), self.body)
        else:
            return "INT %s. %s" % (self.var, self.body)

    def __repr__(self):
        return "IndefiniteIntegral(%s,%s,%s)" % (self.var, repr(self.body), self.skolem_args)

    def alpha_convert(self, new_name: str):
        """Change the variable of integration to new_name."""
        assert isinstance(new_name, str), "alpha_convert"
        return IndefiniteIntegral(new_name, self.body.subst(self.var, Var(new_name)), self.skolem_args)


class Integral(Expr):
    """Integral of an expression."""

    def __init__(self, var: str, lower: Expr, upper: Expr, body: Expr):
        assert isinstance(var, str) and isinstance(lower, Expr) and \
               isinstance(upper, Expr) and isinstance(body, Expr)
        self.ty = INTEGRAL
        self.var = var
        self.lower = lower
        self.upper = upper
        self.body = body

    def __hash__(self):
        return hash((INTEGRAL, self.var, self.lower, self.upper, self.body))

    def __eq__(self, other):
        return isinstance(other, Integral) and self.lower == other.lower and self.upper == other.upper and \
               self.body == other.alpha_convert(self.var).body

    def __str__(self):
        return "INT %s:[%s,%s]. %s" % (self.var, str(self.lower), str(self.upper), str(self.body))

    def __repr__(self):
        return "Integral(%s,%s,%s,%s)" % (self.var, repr(self.lower), repr(self.upper), repr(self.body))

    def alpha_convert(self, new_name):
        """Change the variable of integration to new_name."""
        assert isinstance(new_name, str), "alpha_convert"
        return Integral(new_name, self.lower, self.upper, self.body.subst(self.var, Var(new_name)))


class EvalAt(Expr):
    """Evaluation at upper and lower, then subtract."""

    def __init__(self, var: str, lower: Expr, upper: Expr, body: Expr):
        assert isinstance(var, str) and isinstance(lower, Expr) and \
               isinstance(upper, Expr) and isinstance(body, Expr)
        self.ty = EVAL_AT
        self.var = var
        self.lower = lower
        self.upper = upper
        self.body = body

    def __hash__(self):
        return hash((EVAL_AT, self.var, self.lower, self.upper, self.body))

    def __eq__(self, other):
        return isinstance(other, EvalAt) and self.var == other.var and \
               self.lower == other.lower and self.upper == other.upper and self.body == other.body

    def __str__(self):
        return "[%s]_%s=%s,%s" % (str(self.body), self.var, str(self.lower), str(self.upper))

    def __repr__(self):
        return "EvalAt(%s,%s,%s,%s)" % (self.var, repr(self.lower), repr(self.upper), repr(self.body))


class Symbol(Expr):
    """Pattern expression.
    
    It can be used to find expression with the given specific structure.
    
    """
    def __init__(self, name: str, pat: List[str]):
        self.ty = SYMBOL
        self.name = name
        self.pat = tuple(pat)

    def __eq__(self, other):
        return isinstance(other, Symbol) and self.name == other.name and self.pat == other.pat

    def __hash__(self):
        return hash((SYMBOL, self.name, self.ty, sum(self.pat)))

    def __str__(self):
        return "?%s" % self.name

    def __repr__(self):
        return "Symbol(%s, %s)" % (self.name, self.pat)


class Summation(Expr):
    """Summation of integers over some range."""
    def __init__(self, index_var: str, lower: Expr, upper: Expr, body: Expr):
        self.ty = SUMMATION
        self.index_var: str = index_var
        self.lower: Expr = lower
        self.upper: Expr = upper
        self.body: Expr = body

    def __str__(self):
        return "SUM(" + self.index_var + ", " + str(self.lower) + ", " + str(self.upper) + ", " + str(self.body) + ")"

    def __eq__(self, other):

        if isinstance(other, Summation):
            if self.index_var == other.index_var:
                return self.lower == other.lower and \
                self.upper == other.upper and \
                self.body == other.body
            else:
                return other.alpha_convert(self.index_var) == self
        return False

    def __hash__(self):
        return hash((SUMMATION, self.index_var, self.ty, self.lower, self.upper, self.body))

    def alpha_convert(self, new_var: str):
        """Rename the bound variable of a summation."""
        assert isinstance(new_var, str), "alpha_convert"
        return Summation(new_var, self.lower, self.upper, self.body.subst(self.index_var, Var(new_var)))


def eval_expr(e: Expr):
    if e.is_inf():
        if e == POS_INF:
            return float('inf')
        else:
            return float('-inf')
    elif e.is_const():
        return e.val
    elif e.is_plus():
        return eval_expr(e.args[0]) + eval_expr(e.args[1])
    elif e.is_uminus():
        return -eval_expr(e.args[0])
    elif e.is_minus():
        return eval_expr(e.args[0]) - eval_expr(e.args[1])
    elif e.is_times():
        return eval_expr(e.args[0]) * eval_expr(e.args[1])
    elif e.is_divides():
        return eval_expr(e.args[0]) / eval_expr(e.args[1])
    elif e.is_power():
        return eval_expr(e.args[0]) ** eval_expr(e.args[1])
    elif e.is_fun():
        if e.func_name == 'sqrt':
            return math.sqrt(eval_expr(e.args[0]))
        elif e.func_name == 'exp':
            return math.exp(eval_expr(e.args[0]))
        elif e.func_name == 'abs':
            return abs(eval_expr(e.args[0]))
        elif e.func_name == 'pi':
            return math.pi
        elif e.func_name == 'sin':
            return math.sin(eval_expr(e.args[0]))
        elif e.func_name == 'cos':
            return math.cos(eval_expr(e.args[0]))
        elif e.func_name == 'tan':
            return math.tan(eval_expr(e.args[0]))
        elif e.func_name == 'cot':
            return 1.0 / math.tan(eval_expr(e.args[0]))
        elif e.func_name == 'sec':
            return 1.0 / math.cos(eval_expr(e.args[0]))
        elif e.func_name == 'csc':
            return 1.0 / math.sin(eval_expr(e.args[0]))
        elif e.func_name == 'asin':
            return math.asin(eval_expr(e.args[0]))
        elif e.func_name == 'acos':
            return math.acos(eval_expr(e.args[0]))
        elif e.func_name == 'atan':
            return math.atan(eval_expr(e.args[0]))
        elif e.func_name == 'log':
            return math.log(eval_expr(e.args[0]))
        elif e.func_name == 'factorial':
            arg = eval_expr(e.args[0])
            if int(arg) == arg:
                return math.factorial(arg)
            else:
                from scipy.special import gamma
                return gamma(float(arg) + 1)
        elif e.func_name == 'Gamma':
            arg = eval_expr(e.args[0])
            from scipy.special import gamma
            return gamma(float(arg))

    print(e)
    raise NotImplementedError


def neg_expr(ex: Expr):
    if ex.is_op():
        if ex.op == "=":
            return Op("!=", ex.args[0], ex.args[1])
        elif ex.op == "!=":
            return Op("=", ex.args[0], ex.args[1])
        elif ex.op == ">":
            return Op("<=", ex.args[0], ex.args[1])
        elif ex.op == "<":
            return Op(">=", ex.args[0], ex.args[1])
        elif ex.op == ">=":
            return Op("<", ex.args[0], ex.args[1])
        elif ex.op == "<=":
            return Op(">", ex.args[0], ex.args[1])
        else:
            raise NotImplementedError
    else:
        raise NotImplementedError
