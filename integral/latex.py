"""Conversion from expressions to latex."""

from decimal import Decimal
from fractions import Fraction
from integral import expr


def convert_expr(e: expr.Expr, mode: str = "large") -> str:
    if expr.is_var(e):
        return e.name
    elif expr.is_const(e):
        if isinstance(e.val, (int, Decimal)):
            if e.val == Decimal("inf"):
                return "\\infty"
            elif e.val == Decimal("-inf"):
                return "-\\infty"
            else:
                return str(e.val)
        elif isinstance(e.val, Fraction):
            if e.val.denominator == 1:
                return "%d" % e.val.numerator
            elif mode == 'large':
                if e.val.numerator > 0:
                    return "\\frac{%d}{%d}" % (e.val.numerator, e.val.denominator)
                elif e.val.numerator < 0:
                    return "-\\frac{%d}{%d}" % (-e.val.numerator, e.val.denominator)
            else:
                return "%d/%d" % (e.val.numerator, e.val.denominator)
        else:
            raise NotImplementedError
    elif expr.is_inf(e):
        if e == expr.POS_INF:
            return "\\infty"
        else:
            return "-\\infty"
    elif expr.is_op(e):
        if len(e.args) == 1:
            a, = e.args
            sa = convert_expr(a, mode)
            if a.priority() < 70:
                sa = "(%s)" % sa
            return "%s%s" % (e.op, sa)
        elif len(e.args) == 2:
            x, y = e.args
            sx = convert_expr(x, mode)
            sy = convert_expr(y, mode)
            if e.op == '^':
                if expr.is_fun(x) and len(x.args) > 0 and x.func_name == 'log':
                    # Logarithmic function
                    sy = convert_expr(y, mode="short")
                    return "\%s^{%s}(%s)" % (x.func_name, sy, convert_expr(x.args[0]))
                elif expr.is_fun(x) and x.func_name in ('cos', 'sin', 'tan', 'sec', 'csc', 'cot') \
                        and y not in (expr.Const(-1), -expr.Const(1)):
                    # For trigonometric function, use special format.
                    # This should NOT be used when the exponent is -1, since this conflicts with
                    # usual notation for inverse trigonometric functions
                    sy = convert_expr(y, mode="short")
                    return "\%s^{%s}(%s)" % (x.func_name, sy, convert_expr(x.args[0]))
                elif expr.is_const(x) and x.val < 0:
                    return "(%s) ^ {%s}" % (sx,sy)
                elif expr.is_fun(x) and x.func_name == 'factorial':
                    return "(%s)^{%s}" % (sx,sy)
                else:
                    # Ordinary cases
                    sy = convert_expr(y, mode="short")
                    if x.priority() <= e.priority() or expr.is_uminus(x) or expr.is_fun(x) and x.func_name == 'exp':
                        sx = "(%s)" % sx
                    sy = "{%s}" % sy
                    return "%s %s %s" % (sx, e.op, sy)
            elif e.op == '+' or e.op == '-':
                # Ordinary cases
                if x.priority() < e.priority():
                    sx = "(%s)" % sx
                if y.priority() <= e.priority():
                    sy = "(%s)" % sy
                return "%s %s %s" % (sx, e.op, sy)
            elif e.op == "*":
                if x.priority() < e.priority() or expr.is_uminus(x):
                    sx = "(%s)" % sx
                if y.priority() <= e.priority() or expr.is_uminus(y):
                    sy = "(%s)" % sy
                if mode == 'short' and expr.is_const(x) and isinstance(x.val, Fraction) and \
                    x.val.denominator != 1:
                    # If left side is a fraction, add dot to reduce ambiguity
                    return "%s\\cdot %s" % (sx, sy)
                elif x.is_constant() and y.is_constant():
                    if expr.is_fun(y):
                        return "%s %s"%(sx, sy)
                    # 2*1 = 2· 1
                    return "%s\\cdot %s" % (sx, sy)
                elif y.is_constant() and not x.is_constant():
                    # (m/2) * 2 = m/2 · 2
                    return "%s\\cdot %s" % (sx, sy)
                else:
                    return "%s %s" % (sx, sy)
            elif e.op == "/":
                if mode == 'large':
                    return "\\frac{%s}{%s}" % (sx, sy)
                else:
                    if x.priority() < e.priority():
                        sx = "(%s)" % sx
                    if y.priority() <= e.priority():
                        sy = "(%s)" % sy
                    return "%s/%s" % (sx, sy)
            elif e.op in ("=", "<", ">"):
                return "%s %s %s" % (sx, e.op, sy)
            elif e.op == '<=':
                return "%s \\le %s" % (sx, sy)
            elif e.op == ">=":
                return "%s \\ge %s" % (sx, sy)
            elif e.op == "!=":
                return "%s \\neq %s" % (sx, sy)
            elif e.op == "%":
                return "%s\\ \\mathrm{mod}\\ %s" % (sx, sy)
            else:
                raise NotImplementedError
        else:
            raise NotImplementedError
    elif expr.is_fun(e):
        if len(e.args) == 0:
            if e.func_name in ['pi', 'E']:
                return "\\%s" % e.func_name
            else:
                return "%s" % e.func_name
        elif len(e.args) == 1:
            x, = e.args
            sx = convert_expr(x, mode)
            if e.func_name == "exp":
                if e.args[0] == expr.Const(1):
                    return "e"
                else:
                    sx = convert_expr(x, mode="short")
                    return "e^{%s}" % sx
            elif e.func_name == "sqrt":
                return "\\sqrt{%s}" % sx
            elif e.func_name == "abs":
                return "\\left| %s \\right|" % sx
            elif e.func_name == "atan":
                if not expr.is_var(x):
                    sx = "(" + sx + ")"
                return "\\tan^{-1}{%s}" % sx
            elif e.func_name == "asin":
                if not expr.is_var(x):
                    sx = "(" + sx + ")"
                return "\\sin^{-1}{%s}" % sx
            elif e.func_name == "acos":
                if not expr.is_var(x):
                    sx = "(" + sx + ")"
                return "\\cos^{-1}{%s}" % sx
            elif e.func_name == "acot":
                if not expr.is_var(x):
                    sx = "(" + sx + ")"
                return "\\cot^{-1}{%s}" % sx
            elif e.func_name == "acsc":
                if not expr.is_var(x):
                    sx = "(" + sx + ")"
                return "\\csc^{-1}{%s}" % sx
            elif e.func_name == "asec":
                if not expr.is_var(x):
                    sx = "(" + sx + ")"
                return "\\sec^{-1}{%s}" % sx
            elif e.func_name in ('log', 'sin', 'cos', 'tan', 'cot', 'csc', 'sec', 'sinh', 'cosh', 'tanh'):
                if not expr.is_var(x):
                    sx = "(" + sx + ")"
                return "\\%s{%s}" % (e.func_name, sx)
            elif e.func_name == 'factorial':
                if not expr.is_var(x):
                    sx = "(" + sx + ")"
                return "%s!" % sx
            elif e.func_name == 'Gamma':
                return "\\Gamma{(%s)}" % sx
            elif e.func_name == 'zeta':
                return "\\zeta{(%s)}" % sx
            elif e.func_name == 'isInt':
                return "%s \\in\\mathbb{Z}" % sx
            elif e.func_name == 'converges':
                return "%s\\quad\\mathrm{converges}" % sx
            elif e.func_name == "T":
                return "%s^{\\text{T}}" % sx
            elif e.func_name == "norm":
                return "\\|%s\\|" % sx
            elif e.func_name == 'unit_matrix':
                return "\\mathbf{1}_{%s \\times %s}" % (sx, sx)
            elif e.func_name == 'inv':
                return "%s ^ {-1}" % sx
            elif e.func_name == 'hat':
                if expr.is_var(x):
                    return "\hat{%s}" % sx
                else:
                    return "hat({%s})" % sx
            elif e.func_name == 'floor':
                return "\\lfloor %s \\rfloor" % sx
            else:
                return "%s{(%s)}" % (e.func_name, sx)
        elif len(e.args) == 2:
            x, y = e.args
            sx, sy = convert_expr(x, mode), convert_expr(y, mode)
            if e.func_name == "binom":
                return "\\binom{%s}{%s}" % (sx, sy)
            elif e.func_name in ('Li'):
                return "\\operatorname{%s}(%s,%s)" % (e.func_name, sx, sy)
            elif e.func_name == 'zero_matrix':
                return "\\mathbf{0}_{%s \\times %s}"%(sx, sy)
            elif e.func_name == 'nthc':
                return "%s_{%s}" % (sx, sy)
            elif e.func_name == 'nthr':
                return "%s_{%s}" % (sx, sy)
            elif e.func_name == 'rcon':
                m1, m2 = e.args
                if expr.is_fun(m1) and expr.is_fun(m2) and m1.func_name == 'ccon'\
                        and m1.func_name == m2.func_name:
                    a, b = convert_expr(m1.args[0], mode), convert_expr(m1.args[1], mode)
                    c, d = convert_expr(m2.args[0], mode), convert_expr(m2.args[1], mode)
                    s = "\\left[\\begin{array}{c:c}"
                    s += a + " & " + b + "\\\\"
                    s += " \\hdashline "
                    s += c + " & " + d + "\\\\"
                    s += "\\end{array}\\right]"
                    return s
                elif expr.is_var(m1) and expr.is_var(m2):
                    s = "\\left[\\begin{array}{c}"
                    s += m1.name + "\\\\"
                    s += " \\hdashline "
                    s += m2.name + "\\\\"
                    s += "\\end{array}\\right]"
                    return s
                else:
                    raise NotImplementedError(str(e))
            else:
                return "%s(%s,%s)" % (e.func_name, sx, sy)
        elif len(e.args) == 3:
            x, y, z = e.args
            sx, sy, sz = convert_expr(x, mode), convert_expr(y, mode), convert_expr(z, mode)
            if e.func_name == 'nth':
                if z == expr.Const(0):
                    return "%s_{%s}" % (sx, sy)
                return "%s_{%s,%s}" % (sx, sy, sz)
            elif e.func_name == 'choose_col':
                return "%s[:,%s:%s]" % (sx, sy, sz)
            elif e.func_name == 'choose_row':
                return "%s[%s:%s,:]" % (sx, sy, sz)
            else:
                return "%s(%s,%s,%s)" % (e.func_name, sx, sy, sz)
        elif len(e.args) > 2:
            s = "%s{(" % (e.func_name)
            for x in e.args:
                s += "%s," % (convert_expr(x, mode))
            s = s[:-1] + ")}"
            return s
        else:
            raise NotImplementedError
    elif expr.is_integral(e):
        lower = convert_expr(e.lower, mode='short')
        upper = convert_expr(e.upper, mode='short')
        body = convert_expr(e.body, mode)
        return "\\int_{%s}^{%s} %s \\,d%s" % (lower, upper, body, e.var)
    elif expr.is_evalat(e):
        lower = convert_expr(e.lower, mode='short')
        upper = convert_expr(e.upper, mode='short')
        body = convert_expr(e.body, mode)
        return "\\left. %s \\right\\vert_{%s=%s}^{%s}" % (body, e.var, lower, upper)
    elif expr.is_limit(e):
        lim = convert_expr(e.lim, mode="short")
        body = convert_expr(e.body, mode)
        if e.body.ty == expr.OP and len(e.body.args) > 1:
            return "\\lim\\limits_{%s\\to %s} (\,%s\,)" % (e.var, lim, body)
        else:
            return "\\lim\\limits_{%s\\to %s} %s" % (e.var, lim, body)
    elif expr.is_deriv(e):
        if expr.is_op(e.body) and e.body.op in ('+', '-'):
            return "\\frac{d}{d%s} (%s)" % (e.var, convert_expr(e.body, mode))
        else:
            return "\\frac{d}{d%s} %s" % (e.var, convert_expr(e.body, mode))
    elif expr.is_indefinite_integral(e):
        body = convert_expr(e.body, mode)
        return "\\int %s \\,d%s" % (body, e.var)
    elif expr.is_skolem_func(e):
        if not e.dependent_vars:
            return e.name
        else:
            return e.name+'('+', '.join([str(arg) for arg in list(e.dependent_vars)])+')'
    elif expr.is_summation(e):
        lower = convert_expr(e.lower, mode)
        upper = convert_expr(e.upper, mode)
        body = convert_expr(e.body, mode)
        return "\\sum_{%s=%s}^{%s}{%s}" % (e.index_var, lower, upper, body)
    elif expr.is_product(e):
        lower = convert_expr(e.lower, mode)
        upper = convert_expr(e.upper, mode)
        body = convert_expr(e.body, mode)
        return "\\prod_{%s=%s}^{%s}{%s}" % (e.index_var, lower, upper, body)
    elif expr.is_matrix(e):
        res = "\\begin{bmatrix}"
        res += "\\\\".join(["&".join([convert_expr(item) for item in rv]) for rv in e.data])
        res += "\\end{bmatrix}"
        return res
    else:
        print(type(e), ":", e, flush=True)
        raise NotImplementedError

def convert_type(name:str, t: expr.Type) -> str:
    if expr.is_matrix_type(t):
        ele_type_str = convert_type(None, t.eleType)
        if t.col == expr.Const(1):
            shape_str = convert_expr(t.row)
        else:
            shape_str = convert_expr(t.row) + " \\times " + convert_expr(t.col)
        return "\\text{" + name + "} \\in " + ele_type_str + "^{" + shape_str+"}"
    elif t == expr.RealType:
        suffix = "\\mathbb{R}"
        if name is None:
            return suffix
        else:
            return "\\text{" + name + "} \\in " + suffix
    elif t == expr.IntType:
        suffix = "\\mathbb{Z}"
        if name is None:
            return suffix
        else:
            return "\\text{" + name + "} \\in " + suffix
    else:
        raise NotImplementedError(f"this type {str(t)} can not be translated into latex format")
