from typing import TypeGuard, Union

from integral import expr, condprover
from integral.context import Context
from integral.expr import Matrix, Const, Expr
from integral.poly import normalize


"""
def get_type(e, ctx=None) -> str:
    # print(e)
    if e.is_constant() or e.is_inf():
        if e.is_const():
            if type(e.val) == int:
                return 'int'
        return 'real'
    elif e.is_matrix():
        return 'matrix'
    elif expr.is_var(e):
        return e.ty2
    elif e.is_op():
        if e.is_plus():
            a, b = e.args
            if get_type(a, ctx) == 'real' and get_type(b, ctx) == 'real':
                return 'real'
            elif get_type(a, ctx) == 'matrix' and get_type(b, ctx) == 'matrix':
                # check shapes of a and b
                return 'matrix'
            elif get_type(a, ctx) == 'int' and get_type(b, ctx) == 'real':
                return 'real'
            elif get_type(a, ctx) == 'real' and get_type(b, ctx) == 'int':
                return 'real'
            elif get_type(a, ctx) == 'int' and get_type(b, ctx) == 'int':
                return 'int'
            else:
                print(a, b)
                print(get_type(a, ctx), get_type(b, ctx))
                raise TypeError
        elif e.is_times():
            a, b = e.args
            if get_type(a, ctx) == 'real' and get_type(b, ctx) == 'real':
                return 'real'
            elif get_type(a, ctx) == 'real' and get_type(b, ctx) == 'matrix':
                return 'matrix'
            elif get_type(a, ctx) == 'matrix' and get_type(b, ctx) == 'real':
                return 'matrix'
            elif get_type(a, ctx) == 'matrix' and get_type(b, ctx) == 'matrix':
                # check shapes of a and b
                return 'matrix'
            elif get_type(a, ctx) == 'int' and get_type(b, ctx) == 'real':
                return 'real'
            elif get_type(a, ctx) == 'real' and get_type(b, ctx) == 'int':
                return 'real'
            elif get_type(a, ctx) == 'int' and get_type(b, ctx) == 'int':
                return 'int'
            else:
                print(a,b)
                print(get_type(a, ctx), get_type(b, ctx))
                raise TypeError
        elif e.is_divides():
            a, b = e.args
            if get_type(a, ctx) == 'real' and get_type(b, ctx) == 'real':
                return 'real'
            elif get_type(a, ctx) == 'int' and get_type(b, ctx) == 'real':
                return 'real'
            elif get_type(a, ctx) == 'real' and get_type(b, ctx) == 'int':
                return 'real'
            print(a,b,get_type(a, ctx), get_type(b, ctx))
            raise NotImplementedError
        elif e.is_uminus() or e.is_minus():
            a = e.args[0]
            if get_type(a, ctx) == 'real':
                return 'real'
            elif get_type(a, ctx) == 'matrix':
                return 'matrix'
            else:
                raise NotImplementedError
        elif e.is_power():
            a, b = e.args
            if get_type(a, ctx) == 'matrix' and get_type(b, ctx) == 'int':
                return 'matrix'
            elif get_type(a, ctx) == 'real' and get_type(b, ctx) == 'real':
                return 'real'
            elif get_type(a, ctx) == 'real' and get_type(b, ctx) == 'int':
                return 'real'
            elif get_type(a, ctx) == 'int' and get_type(b, ctx) == 'real':
                return 'real'
            elif get_type(a, ctx) == 'matrix' and get_type(b,ctx) == 'int':
                # TODO: check whether a is a squre matrix and b > 0
                return 'matrix'
            elif get_type(a, ctx) == 'int' and get_type(b,ctx) == 'int':
                if condprover.check_condition(expr.Op(">=", b, Const(0)), ctx):
                    return 'int'
            print(a, b)
            print(get_type(a, ctx), get_type(b, ctx))
            raise NotImplementedError
    elif e.is_fun():
        a = e.args[0]
        if e.func_name in ('hat', 'T', 'inv', 'exp') and get_type(a, ctx) == 'matrix':
            return 'matrix'
        elif e.func_name in ('unit_matrix', 'zero_matrix'):
            return 'matrix'
        else:
            return 'real'
    elif e.is_integral():
        if get_type(e.body, ctx) in ('int', 'real'):
            return 'real'
        print(e.body, get_type(e.body, ctx))
        raise NotImplementedError
    elif e.is_indefinite_integral():
        return 'real'
    elif e.is_summation():
        return 'real'
    elif e.is_evalat():
        return 'real'
    elif e.is_equals():
        return 'equation'
    elif e.is_greater():
        return 'greater'
    elif e.is_deriv():
        return 'real'
    elif e.is_limit():
        return 'real'
    elif e.is_skolem_func():
        return 'real'
    elif e.is_symbol():
        return 'real'
    elif e.is_skolem_term():
        return 'real'
    else:
        print(e)
        raise NotImplementedError


def get_shape(e: Expr, ctx: Context):
    if e.is_const():
        return (Const(1), Const(1))
    elif expr.is_var(e):
        return e.shape
    elif e.is_fun():
        if e.func_name == 'inv':
            return e.args[0].shape
        raise NotImplementedError
    elif e.is_op() and len(e.args) == 2:
        a, b = e.args
        if e.is_times():
            shape1 = get_shape(a, ctx)
            shape2 = get_shape(b, ctx)
            # check shape1[1] = shape2[0]
            return (shape1[0], shape2[1])
        elif e.is_plus() or e.is_minus():
            shape1 = get_shape(a, ctx)
            shape2 = get_shape(b, ctx)
            if shape1 != shape2:
                raise ValueError
            return shape1
        elif e.is_power():
            if e.type == 'tensor':
                shape = get_shape(a, ctx)
                if shape[0] != shape[1]:
                    raise ValueError(f'{a} is not a square matrix')
                if b.type != 'int':
                    raise ValueError(f'{b} is not int')
                return shape
            else:
                return (Const(1), Const(1))
        print(e)
        raise NotImplementedError
    elif e.is_op() and len(e.args)==1:
        a = e.args[0]
        if e.is_uminus():
            return get_shape(a, ctx)
    elif e.is_matrix():
        return (e.type.args[0], e.type.args[1])
    else:
        print(e)
        raise NotImplementedError
"""

def has_vector(e: Expr):
    if expr.is_matrix(e):
        return True
    elif isinstance(e, Union[expr.Var, Const, expr.Inf, expr.SkolemFunc, expr.Symbol]):
        return False
    elif expr.is_integral(e):
        return e.upper.has_vector() or e.lower.has_vector() or e.body.has_vector()
    elif expr.is_indefinite_integral(e):
        return e.body.has_vector()
    elif expr.is_op(e) or expr.is_fun(e):
        return any([arg.has_vector() for arg in e.args])
    elif expr.is_summation(e):
        return e.body.has_vector()
    elif expr.is_limit(e):
        return e.body.has_vector() or e.lim.has_vector()
    elif expr.is_deriv(e):
        return e.body.has_vector()
    else:
        print(e)
        raise NotImplementedError

def transpose(e: Expr):
    if expr.is_matrix(e):
        r, c = len(e.data), len(e.data[0])
        return Matrix([[e.data[j][i] for j in range(r)] for i in range(c)])
    return e

def norm(e: Expr) -> Expr:
    if expr.is_matrix_type(e.type):
        res = None
        for r in e.data:
            for c in r:
                if res == None:
                    res = c^2
                else:
                    res += c^2
        return expr.Fun("sqrt", res)
    return e

def multiply(a: Matrix, b: Matrix, ctx: Context):
    assert isinstance(a, Matrix)
    assert isinstance(b, Matrix)
    assert expr.num_col(a.type) == expr.num_row(b.type)
    res = []
    for i in range(len(a.data)):
        tmp = []
        for j in range(len(b.data[0])):
            sum = Const(0)
            for k in range(len(a.data[0])):
                sum = normalize(sum+a.data[i][k] * b.data[k][j], ctx)
            tmp.append(sum)
        res.append(tmp)
    return Matrix(res)

def add(a: Expr, b: Expr, ctx: Context):
    assert expr.is_matrix(a) and expr.is_matrix(b), str(a) + ", " + str(b)
    assert expr.num_col(a.type) == expr.num_col(b.type)
    assert expr.num_row(a.type) == expr.num_row(b.type)
    assert len(a.data) == len(b.data)
    assert all(len(a.data[i]) == len(b.data[i]) for i in range(len(a.data)))
    res = [[Const(0) for j in range(len(a.data[0]))] for i in range(len(a.data))]
    for i in range(len(a.data)):
        for j in range(len(a.data[0])):
            res[i][j] = normalize(res[i][j]+a.data[i][j]+b.data[i][j],ctx)
    return Matrix(res)

def minus(a: Expr, b: Expr, ctx: Context):
    assert expr.is_matrix(a) and expr.is_matrix(b)
    assert expr.num_col(a.type) == expr.num_col(b.type)
    assert expr.num_row(a.type) == expr.num_row(b.type)
    assert len(a.data) == len(b.data)
    assert all(len(a.data[i]) == len(b.data[i]) for i in range(len(a.data)))
    res = [[Const(0) for j in range(len(a.data[0]))] for i in range(len(a.data))]
    for i in range(len(a.data)):
        for j in range(len(a.data[0])):
            res[i][j] = normalize(res[i][j] + a.data[i][j] - b.data[i][j], ctx)
    return Matrix(res)

def unit_matrix(dim: int) -> Matrix:
    """Return the unit matrix of the given dimension."""
    return Matrix([[Const(1) if i == j else Const(0) for j in range(dim)] for i in range(dim)])

def zero_matrix(r: int, c: int):
    assert type(r) == int and type(c) == int
    assert r > 0 and c > 0
    return Matrix([[Const(0) for j in range(c)] for i in range(r)])

def hat(e: Expr) -> Expr:
    if not expr.is_matrix(e) and expr.is_matrix_type(e.type):
        raise AssertionError("hat: type mismatch")

    if expr.is_matrix_type(e.type) and expr.num_row(e.type) == Const(3) and expr.num_col(e.type) == Const(1):
        res = [[ Const(0),  -e.data[2][0],  e.data[1][0]],
               [ e.data[2][0],  Const(0),  -e.data[0][0]],
               [-e.data[1][0],  e.data[0][0],  Const(0)]]
        return Matrix(res)
    elif expr.is_matrix_type(e.type) and expr.num_row(e.type) == Const(6) and expr.num_col(e.type) == Const(1):
        res = [[ Const(0),  -e.data[5][0],  e.data[4][0], e.data[0][0]],
               [ e.data[5][0],  Const(0),  -e.data[3][0], e.data[1][0]],
               [-e.data[4][0],  e.data[3][0],  Const(0),  e.data[2][0]],
               [ Const(0),   Const(0),   Const(0),  Const(0)]]
        return Matrix(res)
    else:
        raise AssertionError(f"{e} should be a 3 or 6-dimensional vector")

def unfold_matrix(e: Expr, r: int, c: int) -> Expr:
    return Matrix([[expr.Fun("nth", e, Const(i), Const(j)) for j in range(c)] for i in range(r)], e.type)


# def is_skew(m:Matrix, ctx:Context):
#     if not isinstance(m, Matrix):
#         return False
#     # a.transpose == -a
#     return normalize(m, ctx) == normalize(Matrix.scalar_mul(Const(-1), m.transpose()), ctx)
#
# def matrix_exp(m:Matrix, t:Expr, ctx:Context):
#     # t is a scalar
#     # determine whether self is an instance of se(3) or skew-matrices
#     # assert m.is_se3() or m.is_skew()
#     dim = m.shape[0]
#     m = normalize(m, ctx)
#     if m.is_se3():
#         twist = m.vee
#         v = twist.get_line_velocity()
#         w = twist.get_angle_velocity()
#         part2 = Matrix([Const(0), Const(0), Const(0), Const(1)], is_column=False)
#         if w != Matrix.zero(3, is_column=True):
#             # formula 2.36 at page 42
#             left_top = matrix_exp(w.hat, t, ctx)
#             right_top = (Matrix.unit_matrix(3) - left_top) * (w.hat * v) + \
#                          Matrix.scalar_mul(t, w * w.t * v)
#             part1 = left_top.concatenate(right_top)
#         else:
#             # formula 2.32 at page 41
#             part1 = Matrix.unit_matrix(3).concatenate(Matrix.scalar_mul(t, v))
#         return normalize(part1.concatenate(part2, col_concatenate=False), ctx)
#     elif is_skew(m, ctx):
#         # Rodrigues Formula
#         # Derivation: https://zhuanlan.zhihu.com/p/369659467
#         # exp(self * t) = I + sin(t) * self + (1-cos(t)) * self * self
#         res = Matrix.unit_matrix(dim) + Matrix.scalar_mul(Fun('sin', t), m) + \
#                Matrix.scalar_mul((Const(1) - Fun('cos', t)), m * m)
#         return normalize(res, ctx)
#     else:
#         raise NotImplementedError
#
# def compute_jacobian(t:List[Matrix], gsl:List[Matrix], theta:List[Expr], n:int, ctx:Context) -> Matrix:
#     r = FullSimplify()
#     jsl = [0 for i in range(n)]
#     for i in range(n):
#         jsl[i] = []
#         tmp = None
#         for j in range(n):
#             if j > i:
#                 tmp = Matrix.zero(6)
#             else:  # j<=i
#                 tmp = Matrix.unit_matrix(4)
#                 for k in range(j, i + 1):
#                     tmp = tmp * matrix_exp(t[k].hat, theta[k], ctx)
#                 tmp = tmp * gsl[i]
#                 tmp = tmp.adjoint(inverse=True)
#                 tmp = tmp * t[j]
#             jsl[i].append(tmp.data)
#         jsl[i] = normalize(Matrix((n, 6), jsl[i]).t,ctx)
#     return jsl