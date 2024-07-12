"""Parsing"""

from typing import Dict, Optional, Tuple, List
from lark import Lark, Token, Transformer, v_args, exceptions
from decimal import Decimal
from fractions import Fraction

from integral import expr
from integral.expr import Expr, type_le
from integral.fixes import Fixes, Info

grammar = r"""
    ?atom: CNAME -> var_expr
        | "?" CNAME  -> symbol_expr
        | INT -> int_expr
        | DECIMAL -> decimal_expr
        | "D" CNAME "." expr -> deriv_expr
        | "pi" -> pi_expr
        | "G" -> g_expr
        | "inf" -> pos_inf_expr
        | "oo" -> pos_inf_expr
        | "-inf" -> neg_inf_expr
        | "-oo" -> neg_inf_expr
        | CNAME "(" expr ("," expr)* ")" -> fun_expr
        | "(" expr ")"
        | "\|" expr "\|" -> abs_expr 
        | "INT" CNAME ":[" expr "," expr "]." expr -> integral_expr
        | "INT" CNAME "." expr -> indefinite_integral_expr
        | "INT" CNAME "[" CNAME ("," CNAME)* "]" "." expr -> indefinite_integral_skolem_expr
        | "[" expr "]_" CNAME "=" expr "," expr -> eval_at_expr
        | "LIM" "{" CNAME "->" expr "}" "." expr -> limit_inf_expr
        | "LIM" "{" CNAME "->" expr "-}" "."  expr -> limit_l_expr
        | "LIM" "{" CNAME "->" expr "+}" "."  expr -> limit_r_expr
        | "[" expr ("," expr)* "]" -> vector_expr
        | "$" CNAME -> type0_expr
        | "$" CNAME "(" expr ("," expr)* ")" -> type_expr

    ?uminus: "-" uminus -> uminus_expr | atom  // priority 80

    ?pow: pow "^" uminus -> pow_expr          // priority 75
        | "-" atom "^" uminus -> uminus_pow_expr
        | uminus

    ?times: times "*" pow -> times_expr        // priority 70
        | times "/" pow -> divides_expr 
        | times "%" pow -> modulo_expr
        | pow

    ?plus: plus "+" times -> plus_expr         // priority 65
        | plus "-" times -> minus_expr | times

    ?compare: plus "=" plus -> eq_expr              // priority 50
        | plus "!=" plus -> not_eq_expr
        | plus ">" plus -> greater_expr
        | plus "<" plus -> less_expr
        | plus ">=" plus -> greater_eq_expr
        | plus "<=" plus -> less_eq_expr
        | plus

    ?expr: compare

    ?calculate_action: "calculate" expr -> calculate_action

    ?atomic_rule: "substitute" CNAME "for" expr -> substitute_rule
        | "inverse" "substitute" expr "for" CNAME "creating" CNAME -> inverse_substitute_rule
        | "apply" "integral" "identity" -> integral_identity_rule
        | "integrate" "by" "parts" "with" "u" "=" expr "," "v" "=" expr -> integrate_by_parts_rule
        | "split" "region" "at" expr -> split_region_rule
        | "rewrite" expr "to" expr -> equation_rule
        | "expand" "polynomial" -> expand_polynomial_rule
        | "simplify" -> full_simplify_rule

    ?rule: atomic_rule

    ?action: calculate_action
        | rule -> rule_action

    %import common.CNAME
    %import common.WS
    %import common.INT
    %import common.DECIMAL

    %ignore WS
"""


@v_args(inline=True)
class ExprTransformer(Transformer):
    def __init__(self):
        self.fixes: Fixes = None

    def var_expr(self, s):
        fixes = self.fixes
        s = str(s)
        if fixes is not None and s in fixes:
            for info in fixes[s]:
                if info.is_var() or info.is_binding_var():
                    return expr.Var(s, type=info.get_type())
        return expr.Var(s)

    def symbol_expr(self, s):
        return expr.Symbol(str(s), [expr.VAR, expr.CONST, expr.OP, expr.FUN])

    def int_expr(self, n):
        return expr.Const(int(n))

    def decimal_expr(self, n):
        return expr.Const(Decimal(n))

    def plus_expr(self, a, b):
        return expr.Op("+", a, b)

    def minus_expr(self, a, b):
        return expr.Op("-", a, b)

    def times_expr(self, a, b):
        return expr.Op("*", a, b)

    def divides_expr(self, a, b):
        if a.ty == expr.CONST and b.ty == expr.CONST:
            return expr.Const(Fraction(a.val) / Fraction(b.val))
        else:
            return expr.Op("/", a, b)

    def modulo_expr(self, a, b):
        if a.ty == expr.CONST and b.ty == expr.CONST and isinstance(a.val, int) and isinstance(b.val, int):
            return expr.Const(a.val % b.val)
        else:
            return expr.Op("%", a, b)

    def pow_expr(self, a, b):
        return expr.Op("^", a, b)

    def eq_expr(self, a, b):
        return expr.Op("=", a, b)

    def not_eq_expr(self, a, b):
        return expr.Op("!=", a, b)

    def less_expr(self, a, b):
        return expr.Op("<", a, b)

    def greater_expr(self, a, b):
        return expr.Op(">", a, b)

    def less_eq_expr(self, a, b):
        return expr.Op("<=", a, b)

    def greater_eq_expr(self, a, b):
        return expr.Op(">=", a, b)

    def uminus_expr(self, a):
        if expr.is_const(a) and a.val > 0:
            return expr.Const(-a.val)
        else:
            return expr.Op("-", a)

    def uminus_pow_expr(self, a, b):
        return expr.Op("-", expr.Op("^", a, b))

    def pi_expr(self):
        return expr.pi

    def g_expr(self):
        return expr.G

    def pos_inf_expr(self):
        return expr.Inf(Decimal("inf"))

    def neg_inf_expr(self):
        return expr.Inf(Decimal("-inf"))

    def fun_expr(self, func_name, *args):
        if func_name == 'SKOLEM_CONST':
            return expr.SkolemFunc(str(args[0]), tuple())
        elif func_name == 'SKOLEM_FUNC':
            return expr.SkolemFunc(str(args[0].func_name), tuple(arg for arg in args[0].args))
        elif func_name == 'SUM':
            e = expr.Summation(str(args[0]), *args[1:])
            return e
        elif func_name == 'MUL':
            e = expr.Product(str(args[0]), *args[1:])
            return e
        s = str(func_name)
        fixes = self.fixes
        if fixes is not None and s in fixes:
            for info in self.fixes[s]:
                if not info.is_func():
                    continue
                t = info.get_type()
                inst = dict()
                flag = True
                if t.args_num == len(args):
                    for a, b in zip([arg.type for arg in args], t.get_args_type()):
                        if not type_le(a, b):
                            flag = False
                            break
                if flag:
                    for i, param_name in enumerate(info.get_args_name()):
                        inst[param_name] = args[i]
                    t_pat = expr.type_to_pattern(t.get_return_type())
                    func_type_args = t.get_args_type()
                    func_type_args.append(t_pat.inst_pat(inst))
                    res = expr.FunType(*func_type_args)
                    return expr.Fun((s, res), *args)
                for i, param_name in enumerate(info.get_args_name()):
                    inst[param_name] = args[i]
                if expr.is_fun_type(t) and t.args_num == len(args):
                    # pattern match
                    t_pat = expr.type_to_pattern(t)
                    tmp = expr.FunType(*[arg.type for arg in args])
                    tmp_pat = expr.FunType(*[arg for arg in t_pat.get_args_type()])
                    tmp_inst = expr.type_match(tmp, tmp_pat)
                    if tmp_inst is not None:
                        inst.update(tmp_inst)
                        return expr.Fun((s, t_pat.inst_pat(inst)), *args)
            raise NotImplementedError(
                s + ":" + ",".join(str(arg.type) for arg in args) + ":" + ",".join(str(arg) for arg in args))
        else:
            return expr.Fun(s, *args)

    def abs_expr(self, expr):
        return expr.Fun("abs", expr)

    def deriv_expr(self, var, body):
        return expr.Deriv(str(var), body)

    def integral_expr(self, var, lower, upper, body):
        return expr.Integral(str(var), lower, upper, body)

    def indefinite_integral_expr(self, var, body):
        return expr.IndefiniteIntegral(str(var), body, tuple())

    def indefinite_integral_skolem_expr(self, *args):
        var = args[0]
        skolem_args = tuple(str(arg) for arg in args[1:-1])
        body = args[-1]
        return expr.IndefiniteIntegral(str(var), body, skolem_args)

    def eval_at_expr(self, body, var, lower, upper):
        return expr.EvalAt(var, lower, upper, body)

    def limit_inf_expr(self, var, lim, body):
        var_type = expr.RealType
        var = str(var)
        if self.fixes != None and var in self.fixes:
            for info in self.fixes[var]:
                if info.is_binding_var():
                    var_type = info.get_type()
        return expr.Limit(var, lim, body, var_type=var_type)

    def limit_l_expr(self, var, lim, body):
        return expr.Limit(str(var), lim, body, "-")

    def limit_r_expr(self, var, lim, body):
        return expr.Limit(str(var), lim, body, "+")

    def vector_expr(self, *args):
        data = []
        for arg in args:
            if isinstance(arg, expr.Matrix):
                data.append(arg.data)
            else:
                data.append(arg)
        return expr.Matrix(tuple(data))

    def type0_expr(self, name) -> expr.Type:
        return expr.Type(str(name))

    def type_expr(self, name, *args) -> expr.Type:
        return expr.Type(str(name), *args)
    
    def calculate_action(self, expr: Expr):
        from integral import action
        return action.CalculateAction(expr)
    
    def substitute_rule(self, var_name: Token, expr: Expr):
        from integral import rules
        return rules.Substitution(str(var_name), expr)

    def inverse_substitute_rule(self, expr: Expr, old_var: Token, var_name: Token):
        from integral import rules
        return rules.SubstitutionInverse(str(var_name), str(old_var), expr)

    def integral_identity_rule(self):
        from integral import rules
        return rules.DefiniteIntegralIdentity()
    
    def integrate_by_parts_rule(self, u_expr: Expr, v_expr: Expr):
        from integral import rules
        return rules.IntegrationByParts(u_expr, v_expr)

    def split_region_rule(self, expr: Expr):
        from integral import rules
        return rules.SplitRegion(expr)
    
    def equation_rule(self, old_expr: Expr, new_expr: Expr):
        from integral import rules
        return rules.Equation(old_expr, new_expr)

    def expand_polynomial_rule(self):
        from integral import rules
        return rules.ExpandPolynomial()

    def full_simplify_rule(self):
        from integral import rules
        return rules.Simplify()

    def rule_action(self, rule):
        from integral import action
        return action.RuleAction(rule)


transformer = ExprTransformer()
expr_parser = Lark(grammar, start="expr", parser="lalr", transformer=transformer)
action_parser = Lark(grammar, start="action", parser="lalr", transformer=transformer)


def parse_expr(s: str, *, fixes: Fixes = None) -> Expr:
    """Parse an integral expression."""
    try:
        transformer.fixes = fixes
        res = expr_parser.parse(s)
        transformer.fixes = None
        return res
    except (exceptions.UnexpectedCharacters, exceptions.UnexpectedToken) as e:
        print("When parsing:", s)
        raise e

def parse_action(s: str):
    return action_parser.parse(s)

def parse_raw_fixes(raw_fixes):
    fixes = Fixes()
    for name, info in raw_fixes:
        symbol_type = info['symbol_type']
        type = parse_expr(info['type'], fixes=fixes)
        args_name = info['args_name'] if 'args_name' in info else None
        info = Info.get_instance(symbol_type, type, args_name)
        fixes[name] = info
    return fixes


def parse_fixes(item, key='fixes'):
    if key not in item:
        return Fixes()
    return parse_raw_fixes(item[key])
