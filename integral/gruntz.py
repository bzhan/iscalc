from random import random
from typing import Set, Dict, Tuple

from integral.context import Context
from integral.expr import Op, Fun, Expr, Var, POS_INF, NEG_INF, Const
from integral.poly import normalize
from integral.series import expand_series

count = 0
def dummy_var():
    global count
    count = count + 1
    return Var("_d"+str(count))
class SubsSet(dict):
    """
    Stores (expr, dummy) pairs, and how to rewrite expr-s.

    Explanation
    ===========

    The gruntz algorithm needs to rewrite certain expressions in term of a new
    variable w. We cannot use subs, because it is just too smart for us. For
    example::

        > Omega=[exp(exp(_p - exp(-_p))/(1 - 1/_p)), exp(exp(_p))]
        > O2=[exp(-exp(_p) + exp(-exp(-_p))*exp(_p)/(1 - 1/_p))/_w, 1/_w]
        > e = exp(exp(_p - exp(-_p))/(1 - 1/_p)) - exp(exp(_p))
        > e.subs(Omega[0],O2[0]).subs(Omega[1],O2[1])
        -1/w + exp(exp(p)*exp(-exp(-p))/(1 - 1/p))

    is really not what we want!

    So we do it the hard way and keep track of all the things we potentially
    want to substitute by dummy variables. Consider the expression::

        exp(x - exp(-x)) + exp(x) + x.

    The mrv set is {exp(x), exp(-x), exp(x - exp(-x))}.
    We introduce corresponding dummy variables d1, d2, d3 and rewrite::

        d3 + d1 + x.

    This class first of all keeps track of the mapping expr->variable, i.e.
    will at this stage be a dictionary::

        {exp(x): d1, exp(-x): d2, exp(x - exp(-x)): d3}.

    [It turns out to be more convenient this way round.]
    But sometimes expressions in the mrv set have other expressions from the
    mrv set as subexpressions, and we need to keep track of that as well. In
    this case, d3 is really exp(x - d2), so rewrites at this stage is::

        {d3: exp(x-d2)}.

    The function rewrite uses all this information to correctly rewrite our
    expression in terms of w. In this case w can be chosen to be exp(-x),
    i.e. d2. The correct rewriting then is::

        exp(-w)/w + 1/w + x.
    """
    def __init__(self):
        self.rewrites:dict = {}

    def __repr__(self):
        return super().__repr__() + ', ' + self.rewrites.__repr__()

    def __getitem__(self, key:Expr):
        if not isinstance(key, Expr):
            raise TypeError
        if key not in self:
            self[key] = dummy_var()
        return dict.__getitem__(self, key)

    def do_subs(self, e:Expr):
        """Substitute the variables with expressions"""
        for e0, d in self.items():
            e = e.replace(d, e0)
        return e

    def meets(self, s2: 'SubsSet'):
        """Tell whether or not self and s2 have non-empty intersection"""
        return set(self.keys()).intersection(s2.keys()) != set()

    def union(self, s2:'SubsSet', exps=None) -> Tuple['SubsSet', Expr]:
        """Compute the union of self and s2, adjusting exps"""
        res = self.copy()
        tr = {}
        for e, d in s2.items():
            if e in self: # this ex in both sets
                if exps != None:
                    exps = exps.replace(d, res[e])
                tr[d] = res[e]
            else:
                res[e] = d
        for var, rewr in s2.rewrites.items():
            for a, b in tr.items():
                rewr = rewr.replace(a, b)
            res.rewrites[var] = rewr
        return res, exps

    def copy(self):
        """Create a shallow copy of SubsSet"""
        r = SubsSet()
        r.rewrites = self.rewrites.copy()
        for e, d in self.items():
            r[e] = d
        return r

    def __str__(self):
        return ', '.join(['('+ str(a)+', '+str(b)+ ')' for (a, b) in self.items()]) + '\n' + str(self.rewrites)
def rewrite(e:Expr, omega: SubsSet, x:str, w:Var, ctx:Context) -> Dict['Expr', 'Expr']:
    for i in omega:
        assert i.is_fun() and i.func_name == 'exp', 'value should be exp'

    rewrites = omega.rewrites
    omega = list(omega.items())
    g = None
    g_sig = None
    first = True
    for ex, _ in omega:
        if first:
            v = ex.size()
            g = ex
            first = False
        elif e.size() < v:
            v = ex.size()
            g = ex
    # w = 0+
    sig = inf_sign(g.args[0], x, ctx)
    tmp = g # debug
    logw = g.args[0]
    if sig == 1:
        w = Const(1)/w
        logw = -logw
    o2 = dict()
    for f, v in omega:
        c = limit_inf(Op('/', f.args[0], g.args[0]), x, ctx)
        A = Fun('exp', normalize(f.args[0] - c * g.args[0],ctx))
        o2[v] = normalize(A * w ^ c, ctx)
    for a, b in o2.items():
        e = e.replace(a, b)
    return e, logw

def compare(x:str, f:Expr, g:Expr, ctx:Context) -> str:
    if f.is_fun() and f.func_name == 'exp':
        lnf = f.args[0]
    else:
        lnf = Fun('log', f)
    if g.is_fun() and g.func_name == 'exp':
        lng = g.args[0]
    else:
        lng = Fun('log', g)
    c = limit_inf(Op('/', lnf, lng), x, ctx)
    if c == Const(0):
        return '<'
    elif c in (POS_INF, NEG_INF):
        return '>'
    else:
        return '='

def mrv_max3(f:SubsSet, fexps:Expr, g:SubsSet, gexps:SubsSet, u:SubsSet, expsboth:Expr, x:str, ctx:Context):
    if not isinstance(f, SubsSet) or not isinstance(g, SubsSet):
        raise TypeError('f or g should be an instance of SubsSet')
    if f == SubsSet(): # compare key and value
        return g, gexps
    elif g == SubsSet():
        return f, fexps
    elif f.meets(g):
        return u, expsboth

    c = compare(x, list(f.keys())[0], list(g.keys())[0], ctx)
    if c == '>':
        return f, fexps
    elif c == '<':
        return g, gexps
    else:
        if c != '=':
            raise ValueError('c should be "="')
        return u, expsboth

def mrv_max1(f:SubsSet, g:SubsSet, exps:Expr, x:str, ctx:Context):
    u, b = f.union(g, exps)
    return mrv_max3(f, g.do_subs(exps), g, f.do_subs(exps), u, b, x, ctx)

def mrv(e:Expr, x:str, ctx:Context):
    if not isinstance(e, Expr):
        raise TypeError('%s should be an instance of Expr'% e)
    if not isinstance(x, str):
        raise TypeError('%s should be an instance of str'% x)
    if not e.contains_var(x):
        return SubsSet(), e
    elif e == Var(x):
        s = SubsSet()
        return s, s[Var(x)]
    elif e.is_uminus():
        s, exps = mrv(e.args[0], x, ctx)
        return s, Op('-', exps)
    elif e.is_times() or e.is_plus() or e.is_divides() or e.is_minus():
        f, fexps = mrv(e.args[0], x, ctx)
        g, gexps = mrv(e.args[1], x, ctx)
        return mrv_max1(f, g, Op(e.op, fexps, gexps), x, ctx)
    elif e.is_power():
        if not e.args[1].contains_var(x):
            s, base_exps = mrv(e.args[0], x, ctx)
            return s, Op('^', base_exps, e.args[1])
        else:
            return mrv(Fun('exp', normalize(e.args[1] * Fun('log', e.args[0]), ctx)), x, ctx)
    elif e.is_fun() and e.func_name == 'log':
            s, exps = mrv(e.args[0], x, ctx)
            return s, Fun('log', exps)
    elif e.is_fun() and e.func_name == 'exp':
        l = limit_inf(e.args[0], x, ctx)
        if l in (POS_INF, NEG_INF):
            f = SubsSet()
            fexps = f[e]
            g, gexps = mrv(e.args[0], x, ctx)
            u = f.union(g)[0]
            u.rewrites[fexps] = Fun('exp', gexps)
            return mrv_max3(f, fexps, g, Fun('exp', gexps), u, fexps, x, ctx)
        else:
            s, exps = mrv(e.args[0], x, ctx)
            return s, Fun('exp', exps)
    else:
        print(e)
        raise NotImplementedError


def mrv_lead_term(e:Expr, x:str, ctx:Context):
    if not e.contains_var(x):
        return (e, Const(0))
    omega, exps = mrv(e, x, ctx)
    if omega == SubsSet():
        return exps, Const(0)
    if Var(x) in omega:
        omega = move_up2(omega, x)
        exps = move_up1(exps, x)

    w = dummy_var()
    ctx.add_condition(Op('>', w, Const(0)))
    f, logw = rewrite(exps, omega, x, w, ctx)
    s = expand_series(f, w.name, logw, ctx)
    s = s.head_term
    c = normalize(s.head_coff.replace(Fun('log',w), logw), ctx)
    p = s.head_power
    return (c,p)


def move_up2(s:SubsSet, x:str):
    r = SubsSet()
    for e, v in s.items():
        r[e.replace(Var(x), Fun('exp', Var(x)))] = v
    for v, e in s.rewrites.items():
        r.rewrites[v] = s.rewrites[v].replace(Var(x), Fun('exp', Var(x)))
    return r

def move_up1(e:Expr, x:str):
    return e.replace(Var(x), Fun('exp', Var(x)))

def inf_sign(e, x, ctx:Context):
    '''
    return a sign of an expression e(x) for x->oo
    e(x) > 0 for x -> oo ... 1
    e(x) = 0 for x -> oo ... 0
    e(x) < 0 for x -> oo ... -1
    '''
    from integral.limits import limit_of_expr
    if ctx.is_positive(e):
        return 1
    elif ctx.is_negative(e):
        return -1
    elif ctx.check_condition(Op('=', e, Const(0))):
        return 0
    else:
        c0, e0 = mrv_lead_term(e, x, ctx)
        res = inf_sign(c0, x)
        return res

def limit_inf(e:Expr, x:str, ctx:Context):
    e = normalize(e, ctx)
    if not e.contains_var(x):
        return e
    coff, power = mrv_lead_term(e, x, ctx)
    sig = inf_sign(power, x, ctx)
    if sig == 1:
        return Const(0)
    elif sig == -1:
        sig = inf_sign(coff, x, ctx)
        if sig == 0:
            raise ValueError('Leading term should not be 0')
        elif sig == 1:
            return POS_INF
        else:
            return NEG_INF
    elif sig == 0:
        return limit_inf(coff, x, ctx)
    else:
        raise ValueError("sign of %s is %s, it could not be evaluated"%(str(power), str(sig)))

def gruntz(e:Expr, x:str, x0:Expr, dir='+'):
    r = None
    if x0 == POS_INF:
        e0 = e
    elif x0 == NEG_INF:
        e0 = e.subst(x, -Var(x))
    else:
        if dir == '-':
            e0 = e.subst(x, x0 - Const(1) / Var(x))
        elif dir == '+':
            e0 = e.subst(x, x0 + Const(1) / Var(x))
        else:
             raise NotImplementedError("dir must be  '+' or  '-'")
    return limit_inf(e0, x)

