from typing import TypeGuard, Union

from integral import expr, condprover
from integral.context import Context
from integral.expr import Matrix, Const, Expr
from integral.poly import normalize


def is_vector(e:Expr, ctx:Context)  -> TypeGuard["Matrix"]:
    flag = isinstance(e, Matrix)
    if not flag:
        return flag
    r, c = get_shape(e, ctx)
    flag = flag and (r == Const(1) or c == Const(1))
    return flag

def get_type(e, ctx=None) -> str:
    # print(e)
    if e.is_constant() or e.is_inf():
        if e.is_const():
            if type(e.val) == int:
                return 'int'
        return 'real'
    elif e.is_matrix():
        return 'matrix'
    elif e.is_var():
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
        if e.func_name in ('hat','T','inv','exp') and get_type(a, ctx) == 'matrix':
            return 'matrix'
        elif e.func_name in ('unit_matrix','zero_matrix'):
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


def get_shape(e:Expr, ctx:Context):
    if e.is_const():
        return (Const(1), Const(1))
    elif e.is_var():
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
            if get_type(a, ctx) == 'matrix':
                shape = get_shape(a, ctx)
                if shape[0] != shape[1]:
                    raise ValueError(f'{a} is not a square matrix')
                if get_type(b, ctx) != 'int':
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
        if e.shape == None:
            rows = Const(0)
            cols = Const(0)
            for i in range(len(e.data[0])):
                cols = cols + get_shape(e.data[0][i], ctx)[1]
            for i in range(len(e.data)):
                rows = rows + get_shape(e.data[i][0], ctx)[0]
            e.shape = (normalize(rows, ctx), normalize(cols, ctx))
        return e.shape
    else:
        print(e)
        raise NotImplementedError

def transpose(e:Expr):
    if e.is_matrix():
        r, c = len(e.data), len(e.data[0])
        return Matrix([[e.data[j][i] for j in range(r)] for i in range(c)])
    return e

def norm(e:Expr, ctx:Context):
    if is_vector(e, ctx):
        res = None
        for r in e.data:
            for c in r:
                if res == None:
                    res = c^2
                else:
                    res += c^2
        return expr.Fun("sqrt", res)

def multiply(a:Matrix, b:Matrix, ctx:Context):
    assert isinstance(a, Matrix)
    assert isinstance(b, Matrix)
    assert len(a.data[0]) == len(b.data)
    res = []
    for i in range(len(a.data)):
        tmp = []
        for j in range(len(b.data[0])):
            sum = Const(0)
            for k in range(len(a.data[0])):
                sum = normalize(sum+a.data[i][k]*b.data[k][j], ctx)
            if len(a.data) == 1 and len(b.data[0]) == 1:
                return sum
            tmp.append(sum)
        res.append(tmp)
    return Matrix(res)

def add(a:Expr, b:Expr, ctx:Context):
    assert a.is_matrix() and b.is_matrix()
    assert get_shape(a, ctx) == get_shape(b, ctx)
    assert len(a.data) == len(b.data)
    assert all(len(a.data[i]) == len(b.data[i]) for i in range(len(a.data)))
    res = [[Const(0) for j in range(len(a.data[0]))] for i in range(len(a.data))]
    for i in range(len(a.data)):
        for j in range(len(a.data[0])):
            res[i][j] = normalize(res[i][j]+a.data[i][j]+b.data[i][j],ctx)
    return Matrix(res)

def minus(a, b, ctx):
    assert a.is_matrix() and b.is_matrix()
    assert get_shape(a, ctx) == get_shape(b, ctx)
    assert len(a.data) == len(b.data)
    assert all(len(a.data[i]) == len(b.data[i]) for i in range(len(a.data)))
    res = [[Const(0) for j in range(len(a.data[0]))] for i in range(len(a.data))]
    for i in range(len(a.data)):
        for j in range(len(a.data[0])):
            res[i][j] = normalize(res[i][j] + a.data[i][j] - b.data[i][j], ctx)
    return Matrix(res)

def unit_matrix(dim:int):
    return Matrix([[Const(1) if i==j else Const(0) for j in range(dim)] for i in range(dim)])

def zero_matrix(r:int ,c:int):
    assert type(r) == int and type(c) == int
    assert r > 0 and c > 0
    return Matrix([[Const(0) for j in range(c)] for i in range(r)])

def hat(e:Expr):
    if not e.is_matrix():
        return e
    if len(e.data[0]) == 1 or len(e.data) == 3:
        res = [[Const(0), -e.data[2][0], e.data[1][0]],
                [e.data[2][0], Const(0), -e.data[0][0]],
                [-e.data[1][0], e.data[0][0], Const(0)]]
        return Matrix(res)
    if len(e.data[0]) == 1 and len(e.data) == 6:
        res = [[Const(0), -e.data[5][0], e.data[4][0], e.data[0][0]],
               [e.data[5][0], Const(0), -e.data[3][0], e.data[1][0]],
               [-e.data[4][0], e.data[3][0], Const(0), e.data[2][0]],
               [Const(0),Const(0),Const(0),Const(0)]]
        return Matrix(res)
    raise ValueError(f"{e} should be a vector of 6- or 3-dimension")