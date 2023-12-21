from typing import Union

from integral import expr
from integral.context import Context
from integral.expr import Matrix, Const, Expr

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
            for k in range(len(a.data[0])):
                if k == 0:
                    sum = expr.Op('*', a.data[i][k], b.data[k][j])
                else:
                    sum = expr.Op('+', sum, a.data[i][k] * b.data[k][j])
            tmp.append(sum)
        res.append(tmp)
    if all(all(not expr.is_matrix_type(ele.type) for ele in rv) for rv in res):
        return Matrix(res)
    elif all(all(expr.is_matrix_type(ele.type) for ele in rv) for rv in res):
        for idx, item in enumerate(res[0]):
            col = expr.num_col(res[0][idx].type) if idx==0 \
                else col + expr.num_col(res[0][idx].type)
        for idx, item in enumerate(res):
            row = expr.num_row(res[idx][0].type) if idx==0 \
                else row + expr.num_row(res[idx][0].type)
        type = expr.MatrixType(expr.RealType, row, col)
        return Matrix(res, type)
    else:
        raise NotImplementedError

def add(a: Expr, b: Expr, ctx: Context):
    assert expr.is_matrix(a) and expr.is_matrix(b), str(a) + ", " + str(b)
    assert expr.num_col(a.type) == expr.num_col(b.type)
    assert expr.num_row(a.type) == expr.num_row(b.type)
    assert len(a.data) == len(b.data)
    assert all(len(a.data[i]) == len(b.data[i]) for i in range(len(a.data)))
    res = [[Const(0) for j in range(len(a.data[0]))] for i in range(len(a.data))]
    for i in range(len(a.data)):
        for j in range(len(a.data[0])):
            res[i][j] = res[i][j]+a.data[i][j]+b.data[i][j]
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
            res[i][j] = res[i][j] + a.data[i][j] - b.data[i][j]
    return Matrix(res)

def unit_matrix(dim: int) -> Matrix:
    """Return the unit matrix of the given dimension."""
    return Matrix([[Const(1) if i == j else Const(0) for j in range(dim)] for i in range(dim)])

def zero_matrix(r: int, c: int):
    assert type(r) == int and type(c) == int, str(r)+","+str(c)
    assert r > 0 and c > 0
    return Matrix([[Const(0) for j in range(c)] for i in range(r)])

def hat(e: Expr, ctx:Context) -> Expr:
    if not expr.is_matrix(e) and not expr.is_matrix_type(e.type):
        raise AssertionError("hat: type mismatch")
    r = expr.eval_expr(expr.num_row(e.type))
    c = expr.eval_expr(expr.num_col(e.type))
    te = e.type
    res = None
    if expr.is_matrix(e) and r == 3 and c == 1:
        res = [[ Const(0),  -e.data[2][0],  e.data[1][0]],
               [ e.data[2][0],  Const(0),  -e.data[0][0]],
               [-e.data[1][0],  e.data[0][0],  Const(0)]]
        te = expr.TensorType(te.args[0], Const(3), Const(3))
        return Matrix(res, te)
    elif expr.is_matrix(e) and r == 6 and c == 1:
        data_r = len(e.data)
        data_c = len(e.data[0])
        if data_r == r and data_c == c:
            res = [[ Const(0),  -e.data[5][0],  e.data[4][0], e.data[0][0]],
                   [ e.data[5][0],  Const(0),  -e.data[3][0], e.data[1][0]],
                   [-e.data[4][0],  e.data[3][0],  Const(0),  e.data[2][0]],
                   [ Const(0),   Const(0),   Const(0),  Const(0)]]
            te = expr.TensorType(te.args[0], Const(4), Const(4))
        elif data_r == 2 and data_c == 1:
            w = e.data[0][0]
            v = e.data[1][0]
            tw = w.type
            tv = v.type
            twr = expr.eval_expr(expr.num_row(tw))
            twc = expr.eval_expr(expr.num_col(tw))
            tvr = expr.eval_expr(expr.num_row(tv))
            tvc = expr.eval_expr(expr.num_col(tv))
            assert twr == 3 and twc == 1 and tvr == 3 and tvc == 1
            res = [[expr.Fun(*ctx.get_func_type('hat', w)), v],
                   [expr.Fun(*ctx.get_func_type('zero_matrix', Const(1), Const(3))), expr.Fun(*ctx.get_func_type('zero_matrix', Const(1), Const(1)))]]
            te = expr.TensorType(te.args[0], Const(4), Const(4))
        else:
            raise NotImplementedError
        return Matrix(res, te)
    else:
        raise AssertionError(f"{e} should be a 3 or 6-dimensional vector")

def unfold_matrix(e: Expr, r: int, c: int, ctx: Context) -> Expr:
    return Matrix([[expr.Fun(*ctx.get_func_type("nth", e, Const(i), Const(j))) for j in range(c)] for i in range(r)], e.type)
