"""Expressions."""
import math
import functools
from decimal import Decimal
from fractions import Fraction
from collections.abc import Iterable
from typing import Dict, List, Optional, Set, TypeGuard, Tuple, Union, Callable


class Type:
    """Types of expressions.
    
    Each type consists of name and a list of arguments. Each argument
    may be types or expressions.
    
    """
    def __init__(self, name: str, *args):
        self.name = name
        self.args = tuple(args)

    def __eq__(self, other):
        return isinstance(other, Type) and self.name == other.name and self.args == other.args

    def __repr__(self):
        return "Type(%s, %s)" % (self.name, ", ".join(str(arg) for arg in self.args))

    def __str__(self):
        if len(self.args) == 0:
            return "$%s" % self.name
        else:
            return "$%s(%s)" % (self.name, ", ".join(str(arg) for arg in self.args))
        if self.name == "fun":
            assert len(self.args) >= 2
            if len(self.args) == 2:
                return "%s => %s" % (self.args[0], self.args[1])
            else:
                return "(%s) => %s" % (', '.join(str(arg) for arg in self.args[:-1]), self.args[-1])
        elif len(self.args) == 0:
            return "$%s" % self.name
        else:
            return "$%s(%s)" % (self.name, ", ".join(str(arg) for arg in self.args))
        
    def __hash__(self):
        return hash(("Type", self.name, self.args))

    @property
    def eleType(self):
        assert self.name == 'tensor'
        return self.args[0]

    @property
    def row(self):
        assert is_matrix_type(self), str(self)
        return self.args[1]

    @property
    def col(self):
        assert is_matrix_type(self)
        return self.args[2]

    @property
    def args_num(self):
        assert is_fun_type(self)
        return len(self.args) - 1

    def get_args_type(self) -> List['Type']:
        assert is_fun_type(self)
        return list(self.args[:-1])

    def get_return_type(self):
        assert is_fun_type(self)
        return self.args[-1]

    def subst(self, var:str, e:"Expr"):
        if self in (RealType, IntType, BoolType, Unknown):
            return self
        elif self.name == 'tensor':
            eleType = self.eleType.subst(var,e)
            row = self.row.subst(var, e)
            col = self.col.subst(var,e)
            return TensorType(eleType, row, col)
        elif self.name == 'fun':
            args = [arg.subst(var, e) for arg in self.args]
            return FunType(*args)
        raise NotImplementedError("type is %s"%(str(self)))

    def inst_pat(self, mapping:Dict):
        if self in (RealType, IntType, BoolType, Unknown):
            return self
        elif self.name in ("tensor", "fun"):
            return Type(self.name, *[arg.inst_pat(mapping) for arg in self.args])
        else:
            raise NotImplementedError

def FunType(*args) -> Type:
    """Type of functions. The first n-1 arguments are the input types
    of the function. The last argument is the return type.
    
    """
    return Type("fun", *args)

# Type of real numbers
RealType = Type("real")

# Type of integers
IntType = Type("int")
BoolType = Type("bool")
Unknown = Type("unknown")
RealInfType = Type("inf", "$real")
IntInfType = Type("inf", "$int")
InfType = Type("inf")


def TensorType(eleType: Type, *dims) -> Type:
    """Types of tensors, including vectors and matrices.
    
    The first argument is the type of elements in the tensor. The remaining
    arguments are the dimensions (expressions that should evaluate to integer).

    """
    return Type("tensor", eleType, *dims)

# Type of vectors (1-dimensional tensor)
def RowVectorType(eleType: Type, len) -> Type:
    return TensorType(eleType, len)

# Type of matrices (2-dimensional tensor)
def MatrixType(eleType: Type, row, col) -> Type:
    return TensorType(eleType, row, col)

def is_vector_type(type: Type) -> bool:
    return type.name == "tensor" and len(type.args) == 3 and eval_expr(type.args[2]) == 1

def is_row_type(type: Type) -> bool:
    return type.name == "tensor" and len(type.args) == 2

def is_matrix_type(type: Type) -> bool:
    return isinstance(type, Type) and type.name == "tensor" and len(type.args) == 3

def is_fun_type(type:Type) -> bool:
    return isinstance(type, Type) and type.name == 'fun'

def num_row(type: Type) -> "Expr":
    if not is_matrix_type(type):
        raise AssertionError("num_row: input must be a matrix type, got %s" % type)
    return type.args[1]
        
def num_col(type: Type) -> "Expr":
    if not is_matrix_type(type):
        raise AssertionError("num_col: input must be a matrix type, got %s" % type)
    return type.args[2]

VAR, CONST, OP, FUN, DERIV, INTEGRAL, EVAL_AT, SYMBOL, LIMIT, INF, INDEFINITEINTEGRAL, \
SKOLEMFUNC, SUMMATION, LAZYSERIES, VECTOR, MATRIX, PRODUCT = range(17)

op_priority = {
    "+": 65, "-": 65, "*": 70, "/": 70, "%": 70, "^": 75, "=": 50, "<": 50, ">": 50, "<=": 50, ">=": 50, "!=": 50
}
# matrix addition, multiplication, concatenation
type_mapping = {(RealType, RealType):RealType,
                    (RealType, IntType):RealType,
                    (IntType, RealType):RealType,
                    (IntType, IntType):IntType,
                (Unknown, Unknown):Unknown}

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
    def top2(self):
        return self.data[:2]
    @property
    def rest(self):
        return Location(self.data[1:])

    @property
    def rest2(self):
        return Location(self.data[2:])

    def append(self, i: int) -> "Location":
        return Location(self.data + (i,))


class Expr:
    """Expressions."""
    def __init__(self):
        # Type of the expression. None indicates that type is currently
        # not inferred.
        self.type: Optional[Type] = None

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
        if is_const(self) and is_const(other) and isinstance(self.val, int) and isinstance(other.val, int):
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

    def __mod__(self, other):
        if isinstance(other, (int, Fraction)):
            other = CONST(other)
        return Op("%", self, other)

    def __neg__(self):
        if self == POS_INF:
            return NEG_INF
        elif self == NEG_INF:
            return POS_INF
        elif is_const(self) and self.val > 0:
            return Const(-self.val)
        return Op("-", self)

    def size(self):
        if self.ty in (VAR, CONST, SYMBOL, INF):
            return 1
        elif is_op(self) or is_fun(self):
            return 1 + sum(arg.size() for arg in self.args)
        elif is_deriv(self):
            return 1 + self.body.size()
        elif is_integral(self) or is_evalat(self):
            return 1 + self.lower.size() + self.upper.size() + self.body.size()
        elif is_limit(self):
            return 1 + self.lim.size() + self.body.size()
        elif is_indefinite_integral(self):
            return 1 + self.body.size()
        elif is_skolem_func(self):
            return 1 + len(self.dependent_vars)
        elif is_summation(self):
            return 1 + self.lower.size() + self.upper.size() + self.body.size()
        elif is_product(self):
            return 1 + self.lower.size() + self.upper.size() + self.body.size()
        elif is_matrix(self):
            return 1 + sum([sum([item.size() for item in row]) for row in self.data])
        else:
            raise NotImplementedError

    def is_zero(self) -> bool:
        return is_const(self) and self.val == 0

    def is_plus(self):
        return self.ty == OP and self.op == '+'

    def is_minus(self):
        return self.ty == OP and self.op == '-' and len(self.args) == 2

    def is_times(self):
        return self.ty == OP and self.op == '*'

    def is_divides(self):
        return self.ty == OP and self.op == '/'

    def is_power(self):
        return self.ty == OP and self.op == '^'

    def is_mod(self):
        return self.ty == OP and self.op == '%'

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

        if is_var(self):
            return self.name <= other.name
        elif is_const(self):
            return self.val <= other.val
        elif is_op(self):
            return (self.op, self.args) <= (other.op, other.args)
        elif is_fun(self):
            return (self.func_name, self.args) <= (other.func_name, other.args)
        elif is_deriv(self) or is_indefinite_integral(self):
            return (self.body, self.var) <= (other.body, other.var)
        elif is_integral(self) or is_evalat(self):
            return (self.body, self.lower, self.upper, self.var) <= \
                   (other.body, other.lower, other.upper, other.var)
        elif is_symbol(self):
            return sum(self.ty) <= sum(other.ty)
        elif is_summation(self):
            return (self.body, self.lower, self.upper, self.index_var) <= \
                   (other.body, other.lower, other.upper, other.index_var)
        elif is_skolem_func(self):
            return (self.name, self.dependent_vars) <= (other.name, other.dependent_vars)
        elif is_limit(self):
            return (self.var, self.lim, self.body, self.drt) <= (other.var, other.lim, other.body, other.drt)
        elif is_matrix(self):
            return ([[item for item in r] for r in self.data]) <= ([[item for item in r] for r in other.data])
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
        elif self.ty in (FUN, SUMMATION, PRODUCT):
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
        elif is_var(self) or is_const(self):
            raise AssertionError("get_subexpr: invalid location")
        elif is_op(self) or is_fun(self):
            assert loc.head < len(self.args), "get_subexpr: invalid location"
            return self.args[loc.head].get_subexpr(loc.rest)
        elif is_deriv(self):
            assert loc.head == 0, "get_subexpr: invalid location"
            return self.body.get_subexpr(loc.rest)
        elif is_integral(self) or is_evalat(self):
            if loc.head == 0:
                return self.body.get_subexpr(loc.rest)
            elif loc.head == 1:
                return self.lower.get_subexpr(loc.rest)
            elif loc.head == 2:
                return self.upper.get_subexpr(loc.rest)
            else:
                raise AssertionError("get_subexpr: invalid location")
        elif is_limit(self):
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
        elif is_var(self) or is_const(self):
            raise AssertionError("replace_expr: invalid location")
        elif is_op(self):
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
        elif is_fun(self):
            assert loc.head < len(self.args), "replace_expr: invalid location"
            arg = self.args[loc.head].replace_expr(loc.rest, new_expr)
            return Fun((self.func_name, self.type), arg)
        elif is_integral(self):
            if loc.head == 0:
                return Integral(self.var, self.lower, self.upper, self.body.replace_expr(loc.rest, new_expr))
            elif loc.head == 1:
                return Integral(self.var, self.lower.replace_expr(loc.rest, new_expr), self.upper, self.body)
            elif loc.head == 2:
                return Integral(self.var, self.lower, self.upper.replace_expr(loc.rest, new_expr), self.body)
            else:
                raise AssertionError("replace_expr: invalid location")
        elif is_evalat(self):
            if loc.head == 0:
                return EvalAt(self.var, self.lower, self.upper, self.body.replace_expr(loc.rest, new_expr))
            elif loc.head == 1:
                return EvalAt(self.var, self.lower.replace_expr(loc.rest, new_expr), self.upper, self.body)
            elif loc.head == 2:
                return EvalAt(self.var, self.lower, self.upper.replace_expr(loc.rest, new_expr), self.body)
            else:
                raise AssertionError("replace_expr: invalid location")
        elif is_deriv(self):
            assert loc.head == 0, "replace_expr: invalid location"
            return Deriv(self.var, self.body.replace_expr(loc.rest, new_expr))
        elif is_limit(self):
            assert loc.head == 0, "replace_expr: invalid location"
            return Limit(self.var, self.limit, self.body.replace_expr(loc.rest, new_expr), self.drt, self.var_type)
        else:
            raise NotImplementedError

    def get_location(self) -> Location:
        """Returns the location at which the 'selected' field is True."""
        location = []

        def get(exp: Expr, loc=''):
            if hasattr(exp, 'selected') and exp.selected == True:
                location.append(loc[1:])
                exp.selected = False  # Once it is found, restore it.
            elif is_op(exp) or is_fun(exp):
                for i in range(len(exp.args)):
                    get(exp.args[i], loc + "." + str(i))
            elif is_integral(exp) or is_evalat(exp):
                get(exp.lower, loc + ".1")
                get(exp.upper, loc + ".2")
                get(exp.body, loc + ".0")
            elif is_deriv(exp) or is_summation(exp) or is_limit(exp):
                get(exp.body, loc + ".0")

        get(self)
        return location[0]
    def get_all_func_name(self) -> Set[str]:
        return set([pair[0].func_name for pair in self.find_all_subexpr() if is_fun(pair[0])])

    def get_all_symbols(self) -> Set["Symbol"]:
        return set([pair[0] for pair in self.find_all_subexpr() if is_symbol(pair[0])])

    def find_subexpr(self, subexpr: "Expr") -> List[Location]:
        """Returns the location of a subexpression."""
        locations = []

        def find(e: Expr, loc: Location):
            if e == subexpr:
                locations.append(Location(loc))
            elif is_op(e) or is_fun(e):
                for i, arg in enumerate(e.args):
                    find(arg, loc.append(i))
            elif is_integral(e) or is_evalat(e):
                find(e.lower, loc.append(1))
                find(e.upper, loc.append(2))
                find(e.body, loc.append(0))
            elif is_deriv(e) or is_limit(e) or is_indefinite_integral(e):
                find(e.body, loc.append(0))
            elif is_summation(e):
                find(e.body, loc.append(0))
                find(e.lower, loc.append(1))
                find(e.upper, loc.append(2))
            elif is_matrix(e):
                for i, rv in enumerate(e.data):
                    for j, item in enumerate(rv):
                        find(item, loc.append(i).append(j))
        find(self, Location(""))
        return locations

    def find_subexpr_pred(self, pred: Callable[["Expr"], bool]) -> List[Tuple["Expr", Location]]:
        """Find list of subexpressions satisfying a given predicate.

        Larger expressions are placed later.

        """
        results = []

        def find(e: Expr, loc: Location):
            if is_op(e) or is_fun(e):
                for i, arg in enumerate(e.args):
                    find(arg, loc.append(i))
            elif is_integral(e) or is_evalat(e):
                find(e.lower, loc.append(1))
                find(e.upper, loc.append(2))
                find(e.body, loc.append(0))
            elif is_deriv(e) or is_limit(e) or is_indefinite_integral(e):
                find(e.body, loc.append(0))
            elif is_summation(e):
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
        if is_var(self):
            if self.name == var:
                return e
            else:
                return self
        elif is_const(self):
            return self
        elif is_skolem_func(self):
            return SkolemFunc(self.name, tuple(arg.subst(var, e) for arg in self.dependent_vars))
        elif is_symbol(self):
            return self
        elif is_op(self):
            return Op(self.op, *[arg.subst(var, e) for arg in self.args])
        elif is_fun(self):
            func_type = self.func_type.subst(var, e)
            return Fun((self.func_name, func_type), *[arg.subst(var, e) for arg in self.args])
        elif is_deriv(self):
            return Deriv(self.var, self.body.subst(var, e))
        elif is_limit(self):
            return Limit(self.var, self.lim.subst(var, e), self.body.subst(var, e), var_type=self.var_type)
        elif is_inf(self):
            return self
        elif is_integral(self):
            return Integral(self.var, self.lower.subst(var, e), self.upper.subst(var, e), self.body.subst(var, e))
        elif is_indefinite_integral(self):
            return IndefiniteIntegral(self.var, self.body.subst(var, e), self.skolem_args)
        elif is_evalat(self):
            return EvalAt(self.var, self.lower.subst(var, e), self.upper.subst(var, e), self.body.subst(var, e))
        elif is_summation(self):
            return Summation(self.index_var, self.lower.subst(var, e), self.upper.subst(var, e),
                             self.body.subst(var, e))
        elif is_product(self):
            return Product(self.index_var, self.lower.subst(var, e), self.upper.subst(var, e),
                             self.body.subst(var, e))
        elif is_matrix(self):
            return Matrix([[item.subst(var,e) for item in rv] for rv in self.data])
        else:
            print('subst on', self)
            raise NotImplementedError

    def is_constant(self):
        """Determine whether expr is a number.

        Note Inf is not considered to be constants.

        """
        if is_const(self):
            return True
        elif is_op(self):
            return all(arg.is_constant() for arg in self.args)
        elif is_fun(self):
            self: Fun
            if self.func_name in ('inv', 'unit_matrix', 'zero_matrix'):
                return False
            return all(arg.is_constant() for arg in self.args)
        else:
            return False

    def is_evaluable(self):
        return self.is_constant() or is_inf(self)

    def get_bounded_vars(self) -> dict[str, Type]:
        """Obtain the set of variables in self."""
        def rec(t, bd_vars):
            if is_var(t):
                return
            elif t.ty in (CONST, INF, SYMBOL):
                return
            elif is_op(t) or is_fun(t):
                for arg in t.args:
                    rec(arg, bd_vars)
            elif is_deriv(t):
                bd_vars[t.var] = t.var_type
                rec(t.body, bd_vars)
            elif is_limit(t):
                bd_vars[t.var] = t.var_type
                if t.var_type is None:
                    raise NotImplementedError
                rec(t.lim, bd_vars)
                rec(t.body, bd_vars)
            elif is_integral(t) or is_evalat(t):
                bd_vars[t.var] = t.var_type
                rec(t.lower, bd_vars)
                rec(t.upper, bd_vars)
                rec(t.body, bd_vars)
            elif is_indefinite_integral(t):
                bd_vars[t.var] = t.var_type
                rec(t.body, bd_vars)
            elif is_summation(t):
                bd_vars[t.index_var] = t.index_var_type
                rec(t.lower, bd_vars)
                rec(t.upper, bd_vars)
                rec(t.body, bd_vars)
            elif is_product(t):
                bd_vars[t.index_var] = t.index_var_type
                rec(t.lower, bd_vars)
                rec(t.upper, bd_vars)
                rec(t.body, bd_vars)
            elif t.is_equals():
                rec(t.lhs, bd_vars)
                rec(t.rhs, bd_vars)
            elif is_matrix(t):
                for rv in t.data:
                    for d in rv:
                        rec(d, bd_vars)
            elif is_skolem_func(t):
                t: SkolemFunc
                for var in t.dependent_vars:
                    rec(var, bd_vars)
            else:
                print(t, type(t))
                raise NotImplementedError

        bd = dict()
        rec(self, bd)
        return bd

    def get_vars(self, with_bd = False, with_type = False) -> Set[str]:
        """Obtain the set of variables in self."""
        res = set()

        def add(res, with_bd, with_type, name, type=None):
            if with_bd:
                if with_type:
                    res.add((name, type))
                else:
                    res.add(name)

        def rec(t, bd_vars):
            nonlocal with_bd, with_type
            if is_var(t):
                if with_type:
                    if t.name not in bd_vars:
                        res.add((t.name, t.type))
                else:
                    if t.name not in bd_vars:
                        res.add(t.name)
            elif t.ty in (CONST, INF, SYMBOL):
                return
            elif is_op(t) or is_fun(t):
                for arg in t.args:
                    rec(arg, bd_vars)
            elif is_deriv(t):
                add(res, with_bd, with_type, t.var, RealType)
                rec(t.body, bd_vars + [t.var])
            elif is_limit(t):
                add(res, with_bd, with_type, t.var, RealType)
                rec(t.lim, bd_vars + [t.var])
                rec(t.body, bd_vars + [t.var])
            elif is_integral(t) or is_evalat(t):
                add(res, with_bd, with_type, t.var, RealType)
                rec(t.lower, bd_vars + [t.var])
                rec(t.upper, bd_vars + [t.var])
                rec(t.body, bd_vars + [t.var])
            elif is_indefinite_integral(t):
                add(res, with_bd, with_type, t.var, RealType)
                rec(t.body, bd_vars + [t.var])
            elif is_summation(t):
                add(res, with_bd, with_type, t.index_var, IntType)
                rec(t.lower, bd_vars + [t.index_var])
                rec(t.upper, bd_vars + [t.index_var])
                rec(t.body, bd_vars + [t.index_var])
            elif is_product(t):
                add(res, with_bd, with_type, t.index_var, IntType)
                rec(t.lower, bd_vars + [t.index_var])
                rec(t.upper, bd_vars + [t.index_var])
                rec(t.body, bd_vars + [t.index_var])
            elif t.is_equals():
                rec(t.lhs, bd_vars)
                rec(t.rhs, bd_vars)
            elif is_matrix(t):
                for rv in t.data:
                    for d in rv:
                        rec(d, bd_vars)
            elif is_skolem_func(t):
                t:SkolemFunc
                for var in t.dependent_vars:
                    rec(var, bd_vars)
            else:
                print(t, type(t))
                raise NotImplementedError
        bd = []
        rec(self, bd)
        return res

    def contains_var(self, x: str) -> bool:
        """Whether self contains variable x."""
        assert isinstance(x, str)
        return x in self.get_vars()

    def replace(self, e: "Expr", repl_e: "Expr") -> "Expr":
        """Replace occurrences of e with repl_e."""
        assert isinstance(e, Expr) and isinstance(repl_e, Expr)
        if self == e:
            return repl_e
        elif self.ty in (VAR, CONST, INF, SYMBOL):
            return self
        elif is_op(self):
            return Op(self.op, *[arg.replace(e, repl_e) for arg in self.args])
        elif is_fun(self):
            return Fun((self.func_name, self.func_type), *[arg.replace(e, repl_e) for arg in self.args])
        elif is_deriv(self):
            return Deriv(self.var, self.body.replace(e, repl_e))
        elif is_integral(self):
            return Integral(self.var, self.lower.replace(e, repl_e), self.upper.replace(e, repl_e),
                            self.body.replace(e, repl_e))
        elif is_evalat(self):
            return EvalAt(self.var, self.lower.replace(e, repl_e), self.upper.replace(e, repl_e),
                          self.body.replace(e, repl_e))
        elif is_skolem_func(self):
            return SkolemFunc(self.name, tuple(var.replace(e, repl_e) for var in self.dependent_vars))
        elif is_summation(self):
            nl = self.lower.replace(e, repl_e)
            nu = self.upper.replace(e, repl_e)
            nbody = self.body.replace(e, repl_e)
            return Summation(self.index_var, nl, nu, nbody)
        elif is_product(self):
            nl = self.lower.replace(e, repl_e)
            nu = self.upper.replace(e, repl_e)
            nbody = self.body.replace(e, repl_e)
            return Product(self.index_var, nl, nu, nbody)
        elif is_limit(self):
            return Limit(self.var, self.lim.replace(e, repl_e), self.body.replace(e, repl_e), self.drt, var_type=self.var_type)
        elif is_matrix(self):
            return Matrix([[item.replace(e, repl_e) for item in rv] for rv in self.data])
        else:
            print(self, e, repl_e)
            raise NotImplementedError

    def separate_integral(self) -> List[Tuple["Expr", Location]]:
        """Collect the list of all integrals appearing in self."""
        return self.find_subexpr_pred(lambda e: is_integral(e) or is_indefinite_integral(e))

    def separate_limits(self) -> List[Tuple["Expr", Location]]:
        """Collect the list of all integrals appearing in self."""
        return self.find_subexpr_pred(lambda e: is_limit(e))

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

    def inst_pat(self, mapping: Dict, func_type:Dict=None) -> "Expr":
        """Instantiate by replacing symbols in term with mapping."""
        if is_var(self) or is_const(self) or is_inf(self):
            return self
        elif is_symbol(self):
            if self.name in mapping:
                res = mapping[self.name]
                res.type.inst_pat(mapping)
                return res
            else:
                return self
        elif is_op(self):
            return Op(self.op, *(arg.inst_pat(mapping, func_type) for arg in self.args))
        elif is_fun(self):
            return Fun((self.func_name, self.func_type.inst_pat(mapping)),
                       *(arg.inst_pat(mapping, func_type) for arg in self.args))
        elif is_skolem_func(self):
            return SkolemFunc(self.name, tuple(arg.inst_pat(mapping, func_type) for arg in self.dependent_vars))
        elif is_integral(self):
            return Integral(self.var, self.lower.inst_pat(mapping, func_type), self.upper.inst_pat(mapping, func_type),
                            self.body.inst_pat(mapping, func_type))
        elif is_evalat(self):
            return EvalAt(self.var, self.lower.inst_pat(mapping, func_type), self.upper.inst_pat(mapping, func_type),
                          self.body.inst_pat(mapping, func_type))
        elif is_deriv(self):
            if self.var in mapping and is_var(mapping[self.var]):
                return Deriv(mapping[self.var].name, self.body.inst_pat(mapping, func_type))
            return Deriv(self.var, self.body.inst_pat(mapping, func_type))
        elif is_summation(self):
            return Summation(self.index_var, self.lower.inst_pat(mapping, func_type), self.upper.inst_pat(mapping, func_type), \
                             self.body.inst_pat(mapping, func_type))
        elif is_product(self):
            return Product(self.index_var, self.lower.inst_pat(mapping, func_type), self.upper.inst_pat(mapping, func_type), \
                             self.body.inst_pat(mapping, func_type))
        elif is_limit(self):
            return Limit(self.var, self.lim.inst_pat(mapping, func_type), self.body.inst_pat(mapping, func_type), self.drt, var_type=self.var_type)
        elif is_matrix(self):
            return Matrix([[item.inst_pat(mapping, func_type) for item in rv] for rv in self.data])
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


def is_var(e: Expr) -> TypeGuard["Var"]:
    return e.ty == VAR

def is_const(e: Expr) -> TypeGuard["Const"]:
    return e.ty == CONST

def is_op(e: Expr) -> TypeGuard["Op"]:
    return e.ty == OP

def is_fun(e: Expr) -> TypeGuard["Fun"]:
    return e.ty == FUN

def is_deriv(e: Expr) -> TypeGuard["Deriv"]:
    return e.ty == DERIV

def is_skolem_func(e: Expr) -> TypeGuard["SkolemFunc"]:
    return e.ty == SKOLEMFUNC

def is_symbol(e: Expr) -> TypeGuard["Symbol"]:
    return e.ty == SYMBOL

def is_integral(e: Expr) -> TypeGuard["Integral"]:
    return e.ty == INTEGRAL

def is_indefinite_integral(e: Expr) -> TypeGuard["IndefiniteIntegral"]:
    return e.ty == INDEFINITEINTEGRAL

def is_evalat(e: Expr) -> TypeGuard["EvalAt"]:
    return e.ty == EVAL_AT

def is_limit(e: Expr) -> TypeGuard["Limit"]:
    return e.ty == LIMIT

def is_summation(e: Expr) -> TypeGuard["Summation"]:
    return e.ty == SUMMATION

def is_product(e: Expr) -> TypeGuard["Product"]:
    return e.ty == PRODUCT

def is_inf(e: Expr) -> TypeGuard["Inf"]:
    return e.ty == INF and (e.t == Decimal("inf") or e.t == Decimal("-inf"))

def is_pos_inf(e: Expr) -> TypeGuard["Inf"]:
    return e.ty == INF and e.t == Decimal("inf")

def is_neg_inf(e: Expr) -> TypeGuard["Inf"]:
    return e.ty == INF and e.t == Decimal("-inf")

def is_matrix(e: Expr) -> TypeGuard["Matrix"]:
    return e.ty == MATRIX

def is_uminus(e: Expr) -> TypeGuard["Op"]:
    return e.ty == OP and e.op == '-' and len(e.args) == 1

def type_match(t: Type, pat:Type) -> Dict:
    if not isinstance(t, Type) or not isinstance(pat, Type):
        return None
    if pat in (RealType, IntType, BoolType, Unknown):
        if t == pat:
            return dict()
        elif pat == RealType and t == IntType:
            return dict()
        return None
    elif t.name in ("tensor","fun") and pat.name == t.name:
        res = dict()
        for t, p in zip(t.args, pat.args):
            if isinstance(t, Type) and isinstance(p, Type):
                inst = type_match(t, p)
                if inst is None:
                    return None
                else:
                    res.update(inst)
            elif isinstance(t, Expr) and isinstance(p, Expr):
                inst = match(t, p)
                if inst is None:
                    return None
                else:
                    res.update(inst)
            else:
                return None
        return res
    else:
        return None

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
                type_inst = type_match(exp.type, pattern.type)
                if type_inst is None:
                    return False
                else:
                    for k in type_inst:
                        if k in d and type_inst[k] != d[k]:
                            return False
                    d.update(type_inst)
                    return True
            else:
                return False
        if exp.ty != pattern.ty:
            return False
        if is_var(exp):
            return pattern.name == exp.name or \
                (pattern.name in bd_vars and bd_vars[pattern.name] == exp.name)
        elif is_const(exp):
            return pattern.val == exp.val
        elif is_op(exp):
            if exp.op != pattern.op or len(exp.args) != len(pattern.args):
                return False
            for i in range(len(exp.args)):
                if not rec(exp.args[i], pattern.args[i], bd_vars):
                    return False
            return True
        elif is_fun(exp):
            if exp.func_name != pattern.func_name or len(exp.args) != len(pattern.args):
                return False
            for i in range(len(exp.args)):
                if not rec(exp.args[i], pattern.args[i], bd_vars):
                    return False
            func_type_inst = type_match(exp.func_type, pattern.func_type)
            if func_type_inst is None:
                return False
            for k in func_type_inst:
                if k in d and func_type_inst[k] != d[k]:
                    return False
            d.update(func_type_inst)
            return True
        elif is_skolem_func(exp):
            if exp.name != pattern.name or len(exp.dependent_vars) != len(pattern.dependent_vars):
                return False
            for i in range(len(exp.dependent_vars)):
                if not rec(exp.dependent_vars[i], pattern.dependent_vars[i], bd_vars):
                    return False
            return True
        elif is_indefinite_integral(exp):
            # Note this ignores set of skolem arguments
            bd_vars[pattern.var] = exp.var
            res = rec(exp.body, pattern.body, bd_vars)
            del bd_vars[pattern.var]
            return res
        elif is_integral(exp):
            bd_vars[pattern.var] = exp.var
            res1 = rec(exp.upper, pattern.upper, bd_vars)
            res2 = rec(exp.lower, pattern.lower, bd_vars)
            res3 = rec(exp.body, pattern.body, bd_vars)
            del bd_vars[pattern.var]
            return res1 and res2 and res3
        elif is_summation(exp):
            bd_vars[pattern.index_var] = exp.index_var
            res1 = rec(exp.upper, pattern.upper, bd_vars)
            res2 = rec(exp.lower, pattern.lower, bd_vars)
            res3 = rec(exp.body, pattern.body, bd_vars)
            del bd_vars[pattern.index_var]
            return res1 and res2 and res3
        elif is_product(exp):
            bd_vars[pattern.index_var] = exp.index_var
            res1 = rec(exp.upper, pattern.upper, bd_vars)
            res2 = rec(exp.lower, pattern.lower, bd_vars)
            res3 = rec(exp.body, pattern.body, bd_vars)
            del bd_vars[pattern.index_var]
            return res1 and res2 and res3
        elif is_inf(exp):
            return exp.t == pattern.t
        elif is_limit(exp):
            bd_vars[pattern.var] = exp.var
            res1 = rec(exp.body, pattern.body, bd_vars)
            res2 = rec(exp.lim, pattern.lim, bd_vars)
            del bd_vars[pattern.var]
            return res1 and res2
        elif is_deriv(exp):
            # TODO: think more about matching of derivatives
            res1 = pattern.var == exp.var
            res2 = rec(exp.body, pattern.body, bd_vars)
            return res1 and res2
        elif is_matrix(exp):
            if len(exp.data) == len(pattern.data) and \
                    all(len(exp.data[i]) == len(pattern.data[i]) for i in range(len(exp.data))):
                return all([all([rec(item, pattern.data[i][j], bd_vars)\
                            for (j, item) in enumerate(rv)])\
                            for (i, rv) in enumerate(exp.data)])
            else:
                return False
        else:
            # Currently not implemented
            print("Match Failed for type:", type(exp))
            return False

    bd_vars = dict()
    if rec(exp, pattern, bd_vars):
        return d
    else:
        return None


def type_to_pattern(t:Type) -> Type:
    if t in (RealType, IntType, BoolType, Unknown):
        return t
    elif t.name == "tensor":
        eleType = type_to_pattern(t.args[0])
        args = [expr_to_pattern(arg) for arg in t.args[1:]]
        return TensorType(eleType, *args)
    elif t.name == 'fun':
        return FunType(*[type_to_pattern(arg) for arg in t.args])
    raise NotImplementedError(str(t))

def expr_to_pattern(e: Expr) -> Expr:
    """Convert an expression to pattern."""
    vars = e.get_vars(with_type=True)
    def rec(_e:Expr):
        if _e.ty in (CONST, SYMBOL, VAR, INF, SKOLEMFUNC):
            return _e
        elif _e.ty == OP:
            return Op(_e.op, *[rec(arg) for arg in _e.args])
        elif _e.ty == FUN:
            func_type = type_to_pattern(_e.func_type)
            return Fun((_e.func_name, func_type), *[rec(arg) for arg in _e.args])
        elif _e.ty == SUMMATION:
            return Summation(_e.index_var, rec(_e.lower), rec(_e.upper), rec(_e.body))
        elif _e.ty == PRODUCT:
            return Product(_e.index_var, rec(_e.lower), rec(_e.upper), rec(_e.body))
        elif _e.ty == INTEGRAL:
            return Integral(_e.var, rec(_e.lower), rec(_e.upper), rec(_e.body))
        elif _e.ty == EVAL_AT:
            return EvalAt(_e.var, rec(_e.lower), rec(_e.upper), rec(_e.body))
        elif _e.ty == INDEFINITEINTEGRAL:
            return IndefiniteIntegral(_e.var, rec(_e.body), e.skolem_args)
        elif _e.ty == LIMIT:
            return Limit(_e.var, rec(_e.lim), rec(_e.body), _e.drt, _e.var_type)
        elif _e.ty == DERIV:
            return Deriv(_e.var, rec(_e.body))
        else:
            raise NotImplementedError(str(_e))
    e = rec(e)
    for var in vars:
        type = type_to_pattern(var[1])
        sym = Symbol(var[0], [VAR, CONST, OP, FUN, INTEGRAL, MATRIX, INF, SYMBOL], type)
        e = e.subst(var[0], sym)
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
        elif is_uminus(e):
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
    def __init__(self, name: str, *, type: Optional[Type] = None):
        assert isinstance(name, str)
        self.ty = VAR
        self.name = name
        assert isinstance(type, Type) or type is None, str(type)
        if type is None:
            self.type = RealType  # default
        else:
            self.type = type

    def __hash__(self):
        return hash((VAR, self.name, self.type))

    def __eq__(self, other):
        return isinstance(other, Var) and self.name == other.name and self.type == other.type

    def __str__(self):
        return self.name

    def __repr__(self):
        if self.type == RealType:
            return "Var(%s)" % self.name
        else:
            return "Var(%s,%s)" % (self.name, self.type)

class Const(Expr):
    """Constants."""

    def __init__(self, val: Union[int, Fraction], type:Type=None):
        assert isinstance(val, (int, Fraction))
        self.ty = CONST
        if isinstance(val, Fraction) and val.denominator == 1:
            self.val = val.numerator
        else:
            self.val = val

        if type == IntType or self.val == int(self.val):
            self.type = IntType
        else:
            self.type = RealType

    def __hash__(self):
        return hash((CONST, self.val))

    def __eq__(self, other):
        return isinstance(other, Const) and self.val == other.val

    def __str__(self):
        return str(self.val)

    def __repr__(self):
        if self.type == RealType:
            return "Const(%s)" % str(self.val)
        else:
            return "Const(%s, %s)" % (str(self.val), str(self.type))


class Op(Expr):
    """Operators."""
    def __init__(self, op: str, *args):
        assert isinstance(op, str)
        assert all(isinstance(arg, Expr) for arg in args), op +":"+ str(args)
        if len(args) == 1:
            assert op == "-"
        elif len(args) == 2:
            assert op in ["+", "-", "*", "/", "%", "^", "=", "!=", "<", "<=", ">", ">="]
        else:
            raise NotImplementedError
        self.ty = OP
        self.op = op
        self.args: Tuple[Expr] = tuple(args)
        self.type = RealType
        if len(args) == 2:
            t1, t2 = args[0].type, args[1].type
            if op in ['+', '-']:
                if t1 in (IntType, RealType) and t2 in (IntType, RealType):
                    self.type = type_mapping[(t1,t2)]
                elif is_matrix_type(t1) and is_matrix_type(t2):
                    self.type = MatrixType(type_mapping[(t1.eleType, t2.eleType)], t1.row, t1.col)
            elif op == '*':
                if t1 in (IntType, RealType) and t2 in (RealType, IntType):
                    self.type = type_mapping[(t1, t2)]
                elif is_matrix_type(t1) and is_matrix_type(t2):
                    self.type = MatrixType(type_mapping[(t1.eleType, t2.eleType)], t1.row, t2.col)
                elif t1 in (IntType, RealType) and is_matrix_type(t2):
                    self.type = MatrixType(type_mapping[(t1, t2.eleType)], t2.row, t2.col)
                elif t2 in (IntType, RealType) and is_matrix_type(t1):
                    self.type = MatrixType(type_mapping[(t2, t1.eleType)], t1.row, t1.col)
            elif op == '/':
                if is_matrix_type(t1) and t2 in (RealType, IntType):
                    self.type = MatrixType(type_mapping[(t1.eleType, t2)], t1.row, t1.col)
            elif op == '^':
                if is_matrix_type(t1) and t2 == IntType:
                    self.type = t1
                elif t1 in (RealType, IntType) and t2 in (RealType, IntType):
                    self.type = type_mapping[(t1, t2)]
            elif op in (">=", "<=", "=", "!=", ">", "<"):
                self.type = BoolType
        elif len(self.args) == 1:
            t = args[0].type
            if op == '-':
                if is_matrix_type(t):
                    self.type = t
                elif t in (RealType, IntType):
                    self.type = t

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
            if self.op == '/' and is_const(a) and is_const(b) and isinstance(a.val, int) and isinstance(b.val, int):
                return "%s/%s" % (a.val, b.val)
            s1, s2 = str(a), str(b)
            if a.priority() < op_priority[self.op]:
                s1 = "(%s)" % s1
            if b.priority() <= op_priority[self.op]:
                s2 = "(%s)" % s2
            if a.priority() > op_priority[self.op]:
                if is_uminus(a) and self.op == '^':
                    s1 = "(%s)" % s1
            return "%s %s %s" % (s1, self.op, s2)
        else:
            raise NotImplementedError

    def __repr__(self):
        return "Op(%s,%s)" % (self.op, ",".join(repr(arg) for arg in self.args))


class Fun(Expr):
    """Functions."""

    def __init__(self, func_name: Union[str, Tuple[str, Type]], *args):
        assert (isinstance(func_name, str) or isinstance(func_name,tuple)) and \
               all(isinstance(arg, Expr) for arg in args), func_name

        self.ty = FUN
        self.args: Tuple[Expr] = tuple(args)
        if isinstance(func_name, str):
            self.func_name = func_name
            self.type = RealType
            self.func_type = FunType(*[RealType for i in range(len(args) + 1)])
            args_type = [arg.type for arg in self.args]
            # TODO: add more type inference
        elif func_name[1] is None:
            self.func_name = func_name[0]
            self.func_type = FunType(*[RealType for i in range(len(args) + 1)])
            self.type = RealType
        else:
            self.func_name, self.func_type = func_name
            self.type = self.func_type.args[-1]

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

    def __init__(self, var: str, lim: Expr, body: Expr, drt=None, var_type:Type = RealType):
        assert isinstance(var, str) and isinstance(lim, Expr) and isinstance(body, Expr), \
            "Illegal expression: %s %s %s" % (type(var), type(lim), type(body))
        self.ty = LIMIT
        self.var = var
        self.lim = lim
        self.body = body.subst(var, Var(var, type=var_type))
        self.drt = drt
        self.type = RealType
        self.var_type = var_type

    def alpha_convert(self, new_name: str):
        """Change the variable of limit expression to new_name."""
        assert isinstance(new_name, str), "alpha_convert"
        return Limit(new_name, self.lim, self.body.subst(self.var, Var(new_name)), self.drt, var_type=self.var_type)

    def __eq__(self, other):

        if not isinstance(other, Limit):
            return False
        if other.var == self.var:
            return other.drt == self.drt and \
                other.lim == self.lim and \
                other.body == self.body
        else:
            return other.alpha_convert(self.var) == self

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

    def __init__(self, t, type=RealType):
        assert t in (Decimal("inf"), Decimal("-inf"))
        self.ty = INF
        self.t = t
        self.type = type

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
    def __init__(self, name: str, dep_vars: Iterable[Expr]):
        self.ty = SKOLEMFUNC
        self.name = name
        self.dependent_vars: Tuple[Expr] = tuple(dep_vars)
        self.type = RealType

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


class Matrix(Expr):
    """Matrix expressions.
    
    Data is a list/matrix/etc of expressions.

    """
    def __init__(self, data: Union[List[Expr], List[List[Expr]]], type:Type=None):
        self.ty = MATRIX

        # Check validity of input and derive type
        if len(data) == 0:
            raise AssertionError("Matrix: input is empty")

        if isinstance(data[0], Expr):
            # Vector case
            self.data = tuple(data)
            self.type = RowVectorType(data[0].type, Const(len(data)))
        else:
            if type == None:
                # Matrix case
                self.data = tuple(tuple(row) for row in data)
                if data[0][0].type in (RealType, IntType):
                    self.type = MatrixType(data[0][0].type, Const(len(data)), Const(len(data[0])))
                elif is_matrix_type(data[0][0].type):
                    if not all(all(is_matrix_type(ele.type) for ele in rv) for rv in data):
                        raise NotImplementedError
                    for idx, item in enumerate(data[0]):
                        col = num_col(data[0][idx].type) if idx == 0 \
                            else col + num_col(data[0][idx].type)
                    for idx, item in enumerate(data):
                        row = num_row(data[idx][0].type) if idx == 0 \
                            else row + num_row(data[idx][0].type)
                    self.type = MatrixType(RealType, row, col)
            else:
                self.data = tuple(tuple(row) for row in data)
                self.type = type

    def __hash__(self):
        return hash(("Matrix", self.data))

    def concatenate(self, other: Union["Matrix", "Matrix"], col_concatenate=True):
        if isinstance(other, Matrix):
            if col_concatenate:
                assert self.shape[0] == other.shape[0]
                arr = Matrix.vectors2arr(self.cols + other.cols, is_row_vectors=False)
                return Matrix((self.shape[0], self.shape[1] + other.shape[1]), arr)
            else:
                assert self.shape[1] == other.shape[1]
                arr = Matrix.vectors2arr(self.rows + other.rows, is_row_vectors=True)
                return Matrix((self.shape[0] + other.shape[0], self.shape[1]), arr)
        else:
            raise TypeError

    def __eq__(self, other: 'Matrix'):
        return isinstance(other, Matrix) and self.ty == other.ty and self.data == other.data

    def __str__(self):
        if is_matrix_type(self.type):
            return "[" + ", ".join("[" + ", ".join(str(val) for val in row) + "]" for row in self.data) + "]"
        elif is_row_type(self.type):
            return "[" + ", ".join(str(val) for val in self.data) + "]"
        else:
            raise NotImplementedError


NEG_INF = Inf(Decimal('-inf'), RealInfType)
POS_INF = Inf(Decimal('inf'), RealInfType)
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
        self.body: Expr = body.subst(var, Var(var, type=RealType))
        self.type = RealType
        self.var_type = RealType
        if is_matrix_type(body.type):
            self.type = body.type

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
        self.body = body.subst(var, Var(var, type=RealType))
        self.skolem_args = tuple(skolem_args)
        self.type = RealType
        self.var_type = RealType

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
    """Integral of an expression.
    
    Note equality is with respect to alpha equivalence. The hash function
    is likewise.

    """
    def __init__(self, var: str, lower: Expr, upper: Expr, body: Expr):
        assert isinstance(var, str) and isinstance(lower, Expr) and \
               isinstance(upper, Expr) and isinstance(body, Expr)
        self.ty = INTEGRAL
        self.var = var
        self.lower = lower
        self.upper = upper
        self.body = body.subst(var, Var(var, type=RealType))
        self.type = RealType
        self.var_type = RealType

    def __hash__(self):
        # Convert to standard bound variable
        return hash((INTEGRAL, self.lower, self.upper, self.body.subst(self.var, Var("_u"))))

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
        self.body = body.subst(var, Var(var, type=RealType))
        self.type = RealType
        self.var_type = RealType

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
    def __init__(self, name: str, pat: List[str], type:Type=Unknown):
        self.ty = SYMBOL
        self.name = name
        self.pat = tuple(pat)
        self.type = type

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
        self.body: Expr = body.subst(index_var, Var(index_var, type=IntType))
        self.type = RealType
        self.index_var_type = IntType
        if is_matrix_type(self.body.type) or self.body.type in (RealType, IntType):
            self.type = self.body.type
        else:
            raise TypeError("body type is %s"%(str(body.type)))


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


class Product(Expr):
    """Summation of integers over some range."""
    def __init__(self, index_var: str, lower: Expr, upper: Expr, body: Expr):
        self.ty = PRODUCT
        self.index_var: str = index_var
        self.lower: Expr = lower
        self.upper: Expr = upper
        self.body: Expr = body.subst(index_var, Var(index_var, type=IntType))
        self.type = RealType
        self.index_var_type = IntType
        b = self.body
        if is_matrix_type(b.type):
            r, c = num_row(b.type), num_col(b.type)
            self.type = TensorType(b.type.args[0], r, c)
    def __str__(self):
        return "MUL(" + self.index_var + ", " + str(self.lower) + ", " + str(self.upper) + ", " + str(self.body) + ")"

    def __eq__(self, other):
        if isinstance(other, Product):
            if self.index_var == other.index_var:
                return self.lower == other.lower and \
                self.upper == other.upper and \
                self.body == other.body
            else:
                return other.alpha_convert(self.index_var) == self
        return False

    def __hash__(self):
        return hash((PRODUCT, self.index_var, self.ty, self.lower, self.upper, self.body))

    def alpha_convert(self, new_var: str):
        """Rename the bound variable of a product."""
        assert isinstance(new_var, str), "alpha_convert"
        return Product(new_var, self.lower, self.upper, self.body.subst(self.index_var, Var(new_var)))


def eval_expr(e: Expr):
    if is_inf(e):
        if e == POS_INF:
            return float('inf')
        else:
            return float('-inf')
    elif is_const(e):
        return e.val
    elif e.is_plus():
        return eval_expr(e.args[0]) + eval_expr(e.args[1])
    elif is_uminus(e):
        return -eval_expr(e.args[0])
    elif e.is_minus():
        return eval_expr(e.args[0]) - eval_expr(e.args[1])
    elif e.is_times():
        return eval_expr(e.args[0]) * eval_expr(e.args[1])
    elif e.is_divides():
        return eval_expr(e.args[0]) / eval_expr(e.args[1])
    elif e.is_mod():
        return eval_expr(e.args[0]) % eval_expr(e.args[1])
    elif e.is_power():
        return eval_expr(e.args[0]) ** eval_expr(e.args[1])
    elif is_fun(e):
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

    raise NotImplementedError(str(e))


def neg_expr(ex: Expr):
    if is_op(ex):
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

def type_le(t1:Type, t2:Type):
    import integral.poly
    import integral.context
    ctx = integral.context.Context()
    if t1 == IntType and t2 in (IntType, RealType):
        return True
    elif t1 in (RealType, BoolType) and t2 == t1:
        return True
    elif is_matrix_type(t1) and is_matrix_type(t2):
        if not type_le(t1.eleType, t2.eleType):
            return False
        if not integral.poly.normalize(t1.row, ctx) == integral.poly.normalize(t2.row, ctx):
            return False
        if not integral.poly.normalize(t1.col, ctx) == integral.poly.normalize(t2.col, ctx):
            return False
        return True
    elif is_fun_type(t1) and is_fun_type(t2):
        n, m = len(t1.args), len(t2.args)
        if n != m:
            return False
        for i in range(n):
            if not type_le(t1.args[i], t2.args[i]):
                return False
        return True
    return False