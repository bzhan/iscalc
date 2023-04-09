from typing import Set, Callable, Generator, List

from integral import expr, poly, context, rules
from integral.expr import Expr, Var, Const, Op, Fun, POS_INF, NEG_INF
from integral.poly import normalize
from integral.context import Context
from integral.rules import deriv
from integral.parser import parse_expr
global_map = dict()
class LazySeries(Expr):
    def __init__(self, head, f, args, var):
        self.head = head
        self.f:Callable = f
        self.args = args
        self.var = var
        self.ty = expr.LAZYSERIES

    @property
    def head_coff(self):
        return self.head[0]
    @property
    def head_power(self):
        return self.head[1]
    @property
    def head_term(self):
        tmp = self
        while tmp.head_coff == Const(0):
            tmp = tmp.tail()
        return tmp.head

    def __str__(self):
        ctx = Context()
        ctx.load_book('base')
        s = "lazyseries(["
        s += ','.join([str(normalize(e, ctx)) for e in self.head])+'], '
        if self.f != None:
            s += self.f.__name__+'(%s), '%(','.join(str(arg) if not isinstance(arg, Callable) \
                                                        else arg.__name__\
                                                for arg in self.args))
        s += self.var+")"
        return s

    def tail(self) -> 'LazySeries':
        def rec(args):
            if args == list():
                return list()
            res = []
            for arg in args:
                if isinstance(arg, list) and isinstance(arg[0], Callable):
                    res.append(arg[0](*rec(arg[1])))
                else:
                    res.append(arg)
            return res
        if self.f != None:
            # return self.f(*rec(self.args))
            if self not in global_map:
                global_map[self] = self.f(*rec(self.args))
            return global_map[self]
        elif self.args != None:
            return self.args
        else:
            return None

    def print(self, n:int = 6):
        ctx = Context()
        ctx.load_book('base')
        tmp = self
        s = []
        cnt = 1
        while True:
            if ctx.check_condition(Op('=', normalize(tmp.head_coff, ctx), Const(0))):
                tmp = tmp.tail()
                if tmp == None:
                    break
            else:
                s.append(str(normalize(tmp.head_coff, ctx))+'*'+self.var+'^'+str(normalize(tmp.head_power, ctx)))
                tmp = tmp.tail()
                if tmp == None:
                    break;
                cnt = cnt + 1;
            if cnt == n:
                break
        if s == []:
            s = '0'
        else:
            s = ' + '.join(s)
        if tmp != None:
            s += ' + O(%s)'%(self.var+'^'+str(normalize(tmp.head_power, ctx)))
        print(s)

def lazy_series(head, f, args, x:str):
    return LazySeries(head, f, args, x)

def make_series(head, f, args, x):
    return lazy_series(head, f, args, x)

def expfrom(n:int, x:str):
    return make_series([Const(1)/Fun('factorial', Const(n)), Const(n)], expfrom, [n+1, x], x)

def map_series(f:Callable, p:LazySeries):
    if p == None:
        return None
    return make_series(f(*p.head), map_series, [f, [p.tail, []]], p.var)

def scale_series(c:Expr, p:LazySeries, ctx:Context = None):
    if ctx == None:
        ctx = Context()
        ctx.load_book('base')
    def scale(a:Expr, b:Expr):
        nonlocal c, ctx
        return [normalize(Op('*', c, a),ctx), normalize(b,ctx)]
    setattr(scale, '__name__', 'scale_['+str(c)+']')
    return map_series(scale, p)

def shift_series(n:Expr, p:LazySeries, ctx:Context = None):
    if ctx == None:
        ctx = Context()
        ctx.load_book('base')
    def shift(a, b):
        nonlocal n, ctx
        return [normalize(a, ctx), normalize(n + b,ctx)]
    setattr(shift, '__name__', 'shift_'+str(n))
    return map_series(shift, p)

def diff_series(p:LazySeries, ctx:Context=None):
    if ctx == None:
        ctx = Context()
        ctx.load_book('base')
    def deriv(a, b):
        nonlocal ctx
        return [normalize(a*b, ctx), normalize(b-Const(1),ctx)]

    res = map_series(deriv, p)
    if ctx.check_condition(Op('=', res.head_coff, Const(0))):
        return res.tail()
    else:
        return res

def int_series(p:LazySeries, ctx:Context=None):
    if ctx == None:
        ctx = Context()
        ctx.load_book('base')
    def integrate(a, b):
        return [normalize(a/(b+Const(1)),ctx), normalize(b+Const(1),ctx)]
    return map_series(integrate, p)

def sign(e:Expr, ctx:Context = None):
    if ctx == None:
        ctx = Context()
        ctx.load_book('base')
    if ctx.check_condition(Op('>', e, Const(0))):
        return 1
    if ctx.check_condition(Op('<', e, Const(0))):
        return -1
    if ctx.check_condition(Op('=', e, Const(0))) or normalize(e) == Const(0):
        return 0
    return 99

def add_series(f:LazySeries, g:LazySeries, ctx:Context = None):
    if ctx == None:
        ctx = Context()
        ctx.load_book('base')

    if f == None:
        return g
    elif g == None:
        return f
    else:
        assert f.var == g.var
        x = f.var
        s = sign(Op('-', g.head_power, f.head_power))
        if s == 1:
            return make_series(f.head, add_series, [[f.tail,[]], g], x)
        elif s == -1:
            return make_series(g.head, add_series, [f, [g.tail,[]]], x)
        elif s == 0:
            return make_series([normalize(f.head_coff + g.head_coff,ctx),\
                                f.head_power], add_series, [[f.tail,[]],[g.tail,[]]], x)
        else:
            assert False, "sign oracle cannot compute the sign of "+str(g.head_power)+'-'+str(f.head_power)

def sinx(p):
    return make_series([Const(1), Const(1)], int_series, [[int_series, [[scale_series, [Const(-1), [sinx, [p]]]]]]], p.var)

def mult_series(f:LazySeries, g:LazySeries, ctx:Context=None):
    if(ctx == None):
        ctx = Context()
        ctx.load_book('base')
    if f == None:
        return None
    elif g == None:
        return None
    else:
        assert f.var == g.var, "different variable"
        p = make_series([normalize(f.head_coff*g.head_coff, ctx), normalize(f.head_power + g.head_power, ctx)],
                            add_series,
                            [[add_series, [
                                    [scale_series,[
                                        f.head_coff,
                                        [shift_series, [f.head_power, [g.tail, []]]]]
                                    ],
                                    [scale_series,[
                                        g.head_coff,
                                        [shift_series,[ g.head_power, [f.tail, []]]]]
                                    ]]
                               ],
                               [mult_series,
                                [[f.tail,[]], [g.tail, []]]]
                             ],
                            f.var)
        return p

def exp_series(s:LazySeries, ctx:Context = None):
    if ctx == None:
        ctx = Context()
        ctx.load_book('base')
    if ctx.check_condition(Op('>', s.head_power, Const(0))):
        s0 = Const(0)
    else:
        s0 = s.head_coff
    return make_series([Fun('exp', s0), Const(0)],
                       int_series, [
                            [mult_series,[[exp_series, [s]],
                            [diff_series, [s]]]]
                       ],s.var)

def sin_series(s:LazySeries, ctx:Context = None):
    if ctx == None:
        ctx = Context()
        ctx.load_book('base')
    if ctx.check_condition(Op('>', s.head_power, Const(0))):
        s0 = Const(0)
    elif ctx.check_condition(Op('=', s.head_power, Const(0))):
        s0 = s.head_coff
    else:
        raise NotImplementedError
    return make_series([normalize(Fun('sin', s0),ctx), Const(0)], int_series, [
        [mult_series, [[cos_series, [s]],[diff_series, [s]]]]
    ], s.var)

def cos_series(s:LazySeries, ctx:Context = None):
    if ctx == None:
        ctx = Context()
        ctx.load_book('base')
    if ctx.check_condition(Op('>', s.head_power, Const(0))):
        s0 = Const(0)
    elif ctx.check_condition(Op('=', s.head_power, Const(0))):
        s0 = s.head_coff
    else:
        raise NotImplementedError
    return make_series([normalize(Fun('cos', s0),ctx), Const(0)], int_series, [
        [mult_series, [[scale_series,[Const(-1), [sin_series, [s]]]],[diff_series, [s]]]]
    ], s.var)

def tan_series(s:LazySeries, ctx:Context = None):
    if ctx == None:
        ctx = Context()
        ctx.load_book('base')
    if ctx.check_condition(Op('>', s.head_power, Const(0))):
        s0 = Const(0)
    elif ctx.check_condition(Op('=', s.head_power, Const(0))):
        s0 = s.head_coff
    else:
        raise NotImplementedError

    if ctx.check_condition(Op('=', Fun('cos', s0), Const(0))):
        raise AssertionError('division by zero')
    p = make_series([normalize(Fun('tan', s0), ctx), Const(0)], int_series, [
                        [mult_series, [
                            [add_series, [
                                [expand_series, [Const(1), s.var]],
                                [mult_series, [
                                    [tan_series, [s]],
                                    [tan_series, [s]]
                                ]]
                            ]],
                            [diff_series, [s]]
                        ]]], s.var)
    return p

def log_series(s:LazySeries, ctx:Context = None):
    if ctx == None:
        ctx = Context()
        ctx.load_book('base')
    p = make_series([normalize(Fun('log', s.head_coff) + s.head_power * Fun('log', Var(s.var)), ctx), Const(0)],
                       int_series, [
                            [divide_series,[[diff_series, [s]], s]]
                       ],s.var)
    return p

def divide_series(f:LazySeries, g:LazySeries, ctx:Context = None):
    if ctx == None:
        ctx = Context()
        ctx.load_book('base')
    if g == None:
        assert False, 'division by zero'
    elif f == None:
        return None
    else:
        assert f.var == g.var
        p = make_series([normalize(f.head_coff/g.head_coff, ctx), normalize(f.head_power - g.head_power,ctx)], scale_series,
                        [
                            Const(1) / g.head_coff,
                            [shift_series, [
                                -g.head_power,
                                [add_series, [
                                    [f.tail, []],
                                    [scale_series, [Const(-1), [mult_series, [[g.tail, []], [divide_series, [f,g]]]]]]
                                ]]
                            ]]
                        ], f.var)
        return p

def expand_series(e: Expr, x: str, ctx:Context = None):
    if ctx == None:
        ctx = Context()
        ctx.load_book('base')
    if e.is_const() or e.is_constant() or e.is_var() and e.name != x or e.is_fun() and len(e.args) == 0 or\
        not e.contains_var(x):
        return LazySeries([e, Const(0)], None, None, x)
    elif e.is_var() and e.name == 'x':
        return LazySeries([Const(1), Const(1)], None, None, x)
    elif e.is_plus():
        return add_series(expand_series(e.args[0],x), expand_series(e.args[1],x))
    elif e.is_uminus():
        return scale_series(Const(-1), expand_series(e.args[0], x))
    elif e.is_minus():
        return add_series(expand_series(e.args[0],x), scale_series(Const(-1), expand_series(e.args[1],x)))
    elif e.is_times():
        return mult_series(expand_series(e.args[0], x), expand_series(e.args[1], x))
    elif e.is_divides():
        return divide_series(expand_series(e.args[0], x), expand_series(e.args[1], x))
    elif e.is_power():
        if e.args[0].is_var() and e.args[0].name == x and not e.args[1].contains_var(x):
            return LazySeries([Const(1), e.args[1]], None, None, x)
        elif e.args[0].is_divides() and e.args[0].args[0] == Const(1) and \
            e.args[0].args[1] == Var(x) and not e.args[1].contains_var(x):
            return LazySeries([Const(1), normalize(e.args[1] * Const(-1),ctx)], None, None, x)
        else:
            raise NotImplementedError
    elif e.is_fun():
        if e.func_name == 'exp':
            return exp_series(expand_series(e.args[0], x))
        elif e.func_name == 'log':
            return log_series(expand_series(e.args[0], x))
        elif e.func_name == 'sin':
            return sin_series(expand_series(e.args[0], x))
        elif e.func_name == 'cos':
            return cos_series(expand_series(e.args[0], x))
        elif e.func_name == 'tan':
            return tan_series(expand_series(e.args[0], x))
    raise NotImplementedError
