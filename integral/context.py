"""Context of integral calculations"""

from typing import Optional, List, Dict, Union, Callable
import os
import json

from integral import expr
from integral.expr import Expr, Eq, Op, Const, expr_to_pattern, Matrix
from integral import parser
from integral.conditions import Conditions

dirname = os.path.dirname(__file__)

class Identity:
    def __init__(self, expr: Union[str, Expr], *,
                 conds: Optional[Conditions] = None, simp_level: int = 1, category: str = "", split_cond=None):
        if isinstance(expr, str):
            expr = parser.parse_expr(expr)
        self.expr = expr
        if conds is None:
            conds = Conditions()
        self.conds = conds
        self.simp_level = simp_level
        self.category = category
        self.split_cond = split_cond

    def __eq__(self, other:"Identity"):
        return isinstance(other, Identity) and\
        self.expr == other.expr and \
        self.conds == other.conds and \
        self.simp_level == other.simp_level and \
        self.category == other.category and \
        self.split_cond == other.split_cond

    @property
    def lhs(self):
        return self.expr.lhs

    @property
    def rhs(self):
        return self.expr.rhs

    def __str__(self):
        if self.category != "":
            return "%s  [%s] (%s)" % (self.expr, self.conds, self.category)
        else:
            if self.split_cond is None:
                return "%s  [%s]" % (self.expr, self.conds)
            else:
                return "%s [%s] {%s}" % (self.expr, self.conds, self.split_cond)
        
    def __repr__(self):
        return str(self)


class Context:
    """Maintains the current context of calculation.
    
    Information kept in context include the following:
    
    - List of function definitions

    - List of existing identities (for indefinite integrals, definite integrals,
      trigonometric identities, etc).
      
    - Assumptions for the current computation.
    
    - List of variable substitutions.

    """
    def __init__(self, parent: Optional["Context"] = None):

        # Parent context
        self.parent = parent

        # List of definitions
        self.definitions: List[Identity] = list()

        # List of indefinite integral identities
        self.indefinite_integrals: List[Identity] = list()

        # List of definite integral identities
        self.definite_integrals: List[Identity] = list()

        # List of series expansions
        self.series_expansions: List[Identity] = list()

        # List of series evaluations
        self.series_evaluations: List[Identity] = list()

        # List of other identities (trigonometric, etc)
        self.other_identities: List[Identity] = list()

        # List of simplification rules
        self.simp_identities: List[Identity] = list()

        # List of tables of function values
        self.function_tables: Dict[str, Dict[Expr, Expr]] = dict()

        # List of inequalities
        self.inequalities: List[Identity] = list()

        # Lemmas
        self.lemmas: List[Identity] = list()

        # Inductive hypothesis
        self.induct_hyps: List[Identity] = list()

        # List of assumptions
        self.conds: Conditions = Conditions()

        # List of substitutions
        self.substs: Dict[str, Expr] = dict()

        # List of fixes
        self.fixes: Dict[str, expr.Type] = dict()

        # List of identities of summation split
        self.summation_split_identities: List[Identity] = list()

    def __str__(self):
        res = ""
        res += "Definitions\n"
        for identity in self.get_definitions():
            res += str(identity) + "\n"
        res += "Indefinite integrals\n"
        for identity in self.get_indefinite_integrals():
            res += str(identity) + "\n"
        res += "Definite integrals\n"
        for identity in self.get_definite_integrals():
            res += str(identity) + "\n"
        res += "Series expansions\n"
        for identity in self.get_series_expansions():
            res += str(identity) + "\n"
        res += "Series evaluations\n"
        for identity in self.get_series_evaluations():
            res += str(identity) + "\n"
        res += "Other identities\n"
        for identity in self.get_other_identities():
            res += str(identity) + "\n"
        res += "Simplification rules\n"
        for identity in self.get_simp_identities():
            res += str(identity) + "\n"
        res += "Function tables\n"
        for funcname in self.get_function_tables():
            res += "  table for %s\n" % funcname
        res += "Inequalities\n"
        for identity in self.get_inequalities():
            res += str(identity) + "\n"
        res += "Lemmas\n"
        for identity in self.get_lemmas():
            res += str(identity) + "\n"
        res += "Inductive hypothesis\n"
        for identity in self.get_induct_hyps():
            res += str(identity) + "\n"
        res += "Conditions\n"
        for cond in self.get_conds().data:
            res += str(cond) + "\n"


        return res
    
    def get_definitions(self) -> List[Identity]:
        res = self.parent.get_definitions() if self.parent is not None else []
        res.extend(self.definitions)
        return res

    def get_summation_split_identities(self) -> List[Identity]:
        res = self.parent.get_summation_split_identities() if self.parent is not None else []
        res.extend(self.summation_split_identities)
        return res

    def get_indefinite_integrals(self) -> List[Identity]:
        res = self.parent.get_indefinite_integrals() if self.parent is not None else []
        res.extend(self.indefinite_integrals)
        return res
    
    def get_definite_integrals(self) -> List[Identity]:
        res = self.parent.get_definite_integrals() if self.parent is not None else []
        res.extend(self.definite_integrals)
        return res

    def get_series_expansions(self) -> List[Identity]:
        res = self.parent.get_series_expansions() if self.parent is not None else []
        res.extend(self.series_expansions)
        return res

    def get_series_evaluations(self) -> List[Identity]:
        res = self.parent.get_series_evaluations() if self.parent is not None else []
        res.extend(self.series_evaluations)
        return res

    def get_other_identities(self) -> List[Identity]:
        res = self.parent.get_other_identities() if self.parent is not None else []
        res.extend(self.other_identities)
        return res
    
    def get_simp_identities(self) -> List[Identity]:
        res = self.parent.get_simp_identities() if self.parent is not None else []
        res.extend(self.simp_identities)
        return res

    def get_function_tables(self) -> Dict[str, Dict[Expr, Expr]]:
        res = self.parent.get_function_tables() if self.parent is not None else dict()
        res.update(self.function_tables)
        return res
    
    def get_inequalities(self) -> List[Identity]:
        res = self.parent.get_inequalities() if self.parent is not None else []
        res.extend(self.inequalities)
        return res

    def get_lemmas(self) -> List[Identity]:
        res = self.parent.get_lemmas() if self.parent is not None else []
        res.extend(self.lemmas)
        return res

    def get_induct_hyps(self) -> List[Identity]:
        res = self.parent.get_induct_hyps() if self.parent is not None else []
        res.extend(self.induct_hyps)
        return res

    def get_conds(self) -> Conditions:
        res = self.parent.get_conds() if self.parent is not None else Conditions()
        for cond in self.conds.data:
            res.add_condition(cond)
        return res

    def get_fixes(self) -> Dict[str, expr.Type]:
        res = dict()
        p = self
        while p != None:
            d = p.fixes
            for k,v in d.items():
                if k not in res:
                    res[k] = v
            p = p.parent
        return res

    def get_eq_conds(self) -> Conditions:
        res = self.parent.get_conds() if self.parent is not None else Conditions()
        for cond in self.conds.data:
            if cond.is_equals():
                res.add_condition(cond)
        return res

    def get_substs(self) -> Dict[str, Expr]:
        res = self.parent.get_substs() if self.parent is not None else dict()
        for var, expr in self.substs.items():
            res[var] = expr
        return res

    def add_definition(self, eq: Expr, conds:Conditions):
        if not eq.is_equals():
            raise TypeError

        symb_e = expr_to_pattern(eq)
        symb_conds = [expr_to_pattern(cond) for cond in conds.data]
        self.definitions.append(Identity(symb_e, conds=Conditions(symb_conds)))

    def add_indefinite_integral(self, eq: Expr):
        if not (eq.is_equals() and expr.is_indefinite_integral(eq.lhs)):
            raise TypeError
        
        symb_lhs = expr_to_pattern(eq.lhs)
        symb_rhs = expr_to_pattern(eq.rhs)
        self.indefinite_integrals.append(Identity(Eq(symb_lhs, symb_rhs)))

    def add_definite_integral(self, eq: Expr, conds: Conditions):
        if not (eq.is_equals() and expr.is_integral(eq.lhs)):
            raise TypeError
        
        symb_lhs = expr_to_pattern(eq.lhs)
        symb_rhs = expr_to_pattern(eq.rhs)
        self.definite_integrals.append(Identity(Eq(symb_lhs, symb_rhs), conds=conds))

    def add_series_expansion(self, eq: Expr):
        if not (eq.is_equals() and not expr.is_summation(eq.lhs) and expr.is_summation(eq.rhs)):
            raise TypeError
        
        symb_lhs = expr_to_pattern(eq.lhs)
        symb_rhs = expr_to_pattern(eq.rhs)
        self.series_expansions.append(Identity(Eq(symb_lhs, symb_rhs)))

    def add_series_evaluation(self, eq: Expr):
        if not (eq.is_equals() and expr.is_summation(eq.lhs) and not expr.is_summation(eq.rhs)):
            raise TypeError
        
        symb_lhs = expr_to_pattern(eq.lhs)
        symb_rhs = expr_to_pattern(eq.rhs)
        self.series_evaluations.append(Identity(Eq(symb_lhs, symb_rhs)))

    def add_other_identities(self, eq: Expr, category: str, \
                             attributes: Optional[List[str]] = None, conds: Conditions = None):
        if not eq.is_equals():
            raise TypeError
        
        symb_lhs = expr_to_pattern(eq.lhs)
        symb_rhs = expr_to_pattern(eq.rhs)
        symb_conds = [expr_to_pattern(cond) for cond in conds.data] if conds != None else []
        self.other_identities.append(Identity(Eq(symb_lhs, symb_rhs), category=category, conds=Conditions(symb_conds)))
        if attributes is not None and 'bidirectional' in attributes:
            self.other_identities.append(Identity(Eq(symb_rhs, symb_lhs), category=category, conds=Conditions(symb_conds)))

    def add_simp_identity(self, eq: Expr, conds: Conditions):
        if not eq.is_equals():
            raise TypeError
        
        symb_lhs = expr_to_pattern(eq.lhs)
        symb_rhs = expr_to_pattern(eq.rhs)
        symb_conds = [expr_to_pattern(cond) for cond in conds.data]
        self.simp_identities.append(Identity(Eq(symb_lhs, symb_rhs), conds=Conditions(conds)))

    def add_function_table(self, funcname: str, table: Dict[str, str]):
        self.function_tables[funcname] = dict()
        for input, output in table.items():
            input = parser.parse_expr(input)
            output = parser.parse_expr(output)
            self.function_tables[funcname][input] = output

    def add_inequality(self, e: Expr, conds: Conditions):
        symb_e = expr_to_pattern(e)
        symb_conds = [expr_to_pattern(cond) for cond in conds.data]
        self.inequalities.append(Identity(symb_e, conds=Conditions(symb_conds)))

    def add_lemma(self, e: Union[Expr, str], conds: Conditions):
        if isinstance(e, str):
            e = parser.parse_expr(e)
        tmp = Identity(e, conds=conds)
        if tmp not in self.lemmas:
            self.lemmas.append(tmp)

    def add_summation_split_identities(self, e: Expr, conds: Conditions, split_cond: Expr):
        symb_lhs = expr_to_pattern(e.lhs)
        symb_rhs = expr_to_pattern(e.rhs)
        symb_split_cond = expr_to_pattern(split_cond)
        symb_conds = [expr_to_pattern(cond) for cond in conds.data]
        tmp = Identity(Eq(symb_lhs, symb_rhs), conds = Conditions(symb_conds), split_cond=symb_split_cond)
        if tmp not in self.summation_split_identities:
            self.summation_split_identities.append(tmp)

    def add_induct_hyp(self, e: Union[Expr, str]):
        if isinstance(e, str):
            e = parser.parse_expr(e)

        # Note: no conversion to symbols for inductive hypothesis        
        self.induct_hyps.append(Identity(e))

    def add_condition(self, cond: Union[Expr, str]):
        if isinstance(cond, str):
            cond = parser.parse_expr(cond)
        if cond not in self.conds.data:
            self.conds.add_condition(cond)

    def extend_condition(self, conds: Conditions):
        for cond in conds.data:
            self.add_condition(cond)

    def add_fix(self, k: str, v: expr.Type):
        self.fixes[k] = v

    def extend_fixes(self, fixes: Dict[str, expr.Type]):
        for k, v in fixes.items():
            self.add_fix(k, v)

    def add_subst(self, var: str, expr: Expr):
        self.substs[var] = expr

    def extend_substs(self, substs: Dict[str, Expr]):
        for var, expr in substs.items():
            self.substs[var] = expr

    def extend_by_item(self, item):
        if item['type'] == 'axiom' or item['type'] == 'problem':
            e = parser.parse_expr(item['expr'])
            if e.is_equals() and expr.is_indefinite_integral(e.lhs):
                self.add_indefinite_integral(e)
            elif e.is_equals() and expr.is_integral(e.lhs):
                conds = Conditions()
                if 'conds' in item:
                    for cond in item['conds']:
                        conds.add_condition(parser.parse_expr(cond))
                self.add_definite_integral(e, conds)
            elif 'category' in item and item['category'] == 'summation-split':
                conds = Conditions()
                if 'conds' in item:
                    for c in item['conds']:
                        conds.add_condition(parser.parse_expr(c))
                split_cond = parser.parse_expr(item['split-cond'])
                self.add_summation_split_identities(e, conds, split_cond)
            elif e.is_equals() and not expr.is_summation(e.lhs) and expr.is_summation(e.rhs):
                self.add_series_expansion(e)
                if item['type'] == 'problem':
                    conds = Conditions()
                    if 'conds' in item:
                        for c in item['conds']:
                            conds.add_condition(parser.parse_expr(c))
                    self.add_lemma(e, conds)
            elif e.is_equals() and expr.is_summation(e.lhs) and not expr.is_summation(e.rhs):
                if item['type'] == 'problem':
                    conds = Conditions()
                    if 'conds' in item:
                        for c in item['conds']:
                            conds.add_condition(parser.parse_expr(c))
                    self.add_lemma(e, conds)
                else:
                    self.add_series_evaluation(e)
            elif e.is_equals() and 'category' in item:
                conds = Conditions()
                if 'conds' in item:
                    for c in item['conds']:
                        conds.add_condition(parser.parse_expr(c))
                self.add_other_identities(e, item['category'], item.get('attributes'), conds)
            elif e.is_equals() and item['type'] == 'problem':
                conds = Conditions()
                if 'conds' in item:
                    for c in item['conds']:
                        conds.add_condition(parser.parse_expr(c))
                self.add_lemma(e, conds)
        if 'attributes' in item and 'simplify' in item['attributes']:
            e = parser.parse_expr(item['expr'])
            conds = Conditions()
            if 'conds' in item:
                for cond in item['conds']:
                    conds.add_condition(parser.parse_expr(cond))
            self.add_simp_identity(e, conds)
        if 'attributes' in item and 'inequality' in item['attributes']:
            e = parser.parse_expr(item['expr'])
            conds = Conditions()
            if 'conds' in item:
                for cond in item['conds']:
                    conds.add_condition(parser.parse_expr(cond))
            self.add_inequality(e, conds)
        if item['type'] == 'definition':
            e = parser.parse_expr(item['expr'])
            conds = Conditions()
            if 'conds' in item:
                for cond in item['conds']:
                    conds.add_condition(parser.parse_expr(cond))
            self.add_definition(e, conds)
            if 'func_type' in item and expr.is_fun(e.lhs):
                self.fixes[e.lhs.func_name] = parser.parse_expr(item['func_type'])
        if item['type'] == 'table':
            self.add_function_table(item['name'], item['table'])

    def load_book(self, book_name: str, *, upto: Optional[str] = None):
        assert isinstance(book_name, str)

        filename = os.path.join(dirname, "../examples/" + book_name + '.json')
        with open(filename, 'r', encoding='utf-8') as f:
            info = json.load(f)

        # Load imported books
        if 'imports' in info:
            for book_name in info['imports']:
                self.load_book(book_name)

        # Load content
        if 'content' in info:
            for item in info['content']:
                if upto is not None and "path" in item and item['path'] == upto:
                    break
                self.extend_by_item(item)

    def check_condition(self, e: Expr) -> bool:
        """Check the given condition under the extra conditions"""
        from integral import condprover
        f = condprover.check_condition(e, self)
        if f:
            return True
        if expr.is_op(e) and e.op in ('>', '<', '!=', '>=', '<='):
            match e.op:
                case '>':
                    f = condprover.check_condition(Op('<', e.args[1], e.args[0]), self)
                case '<':
                    f = condprover.check_condition(Op('>', e.args[1], e.args[0]), self)
                case '>=':
                    f = condprover.check_condition(Op('<=', e.args[1], e.args[0]), self)
                case '<=':
                    f = condprover.check_condition(Op('>=', e.args[1], e.args[0]), self)
                case '!=':
                    f = condprover.check_condition(Op('!=', e.args[1], e.args[0]), self)
        return f

    def check_all_condtions(self, goal:Expr, conds:Conditions):
        goal_vars = goal.get_vars(with_bd=True)
        ctx = Context(self)
        def rec(e):
            if expr.is_limit(e) and e.lim == expr.POS_INF:
                b = e.body
                # LIM {n->oo}. SUM(i, 0, n, body)
                if expr.is_summation(b) and expr.is_var(b.upper) and b.upper.name == e.var:
                    cond = Op('>=', b.upper, b.lower)
                    ctx.add_condition(cond)
            elif expr.is_op(e):
                for arg in e.args:
                    rec(arg)
        # expand conditions from goal
        rec(goal)
        for e in conds.data:
            if e.get_vars().intersection(goal_vars) == set():
                continue
            if not ctx.check_condition(e):
                return False
        return True

    def is_positive(self, e: Expr) -> bool:
        return self.check_condition(Op(">", e, Const(0)))
    
    def is_negative(self, e: Expr) -> bool:
        return self.check_condition(Op("<", e, Const(0)))

    def is_nonzero(self, e: Expr) -> bool:
        return self.check_condition(Op("!=", e, Const(0)))

    def is_not_negative(self, e: Expr) -> bool:
        return self.check_condition(Op(">=", e, Const(0)))

    def is_not_positive(self, e: Expr) -> bool:
        return self.check_condition(Op("<=", e, Const(0)))

    def is_greater(self, e1: Expr, e2: Expr) -> bool:
        return self.check_condition(Op(">", e1, e2))

    def is_less(self, e1: Expr, e2: Expr) -> bool:
        return self.check_condition(Op("<", e1, e2))

    def is_greater_eq(self, e1: Expr, e2: Expr) -> bool:
        return self.check_condition(Op(">=", e1, e2))

    def is_less_eq(self, e1: Expr, e2: Expr) -> bool:
        return self.check_condition(Op("<=", e1, e2))

    def is_not_equal(self, e1: Expr, e2: Expr) -> bool:
        return self.check_condition(Op("!=", e1, e2))


def body_conds(e: Expr, ctx: Context) -> Context:
    """Return the conditions in the body."""
    ctx2 = Context(ctx)
    if expr.is_integral(e):
        if e.lower != expr.NEG_INF:
            ctx2.add_condition(Op(">", expr.Var(e.var, type=e.var_type), e.lower))
        if e.upper != expr.POS_INF:
            ctx2.add_condition(Op("<", expr.Var(e.var, type=e.var_type), e.upper))
    elif expr.is_indefinite_integral(e):
        pass
    elif expr.is_limit(e):
        if e.lim == expr.POS_INF:
            ctx2.add_condition(expr.Op(">", expr.Var(e.var, type=e.var_type), Const(0)))
    elif expr.is_summation(e) or expr.is_product(e):
        ctx2.add_condition(expr.Op(">=", expr.Var(e.index_var, type=e.index_var_type), e.lower))
        if e.upper != expr.POS_INF:
            ctx2.add_condition(expr.Op("<=", expr.Var(e.index_var, type=e.index_var_type), e.upper))
            ctx2.add_condition(expr.Op(">=", e.upper - expr.Var(e.index_var, type=e.index_var_type), Const(0)))
        ctx2.add_condition(expr.Fun("isInt", expr.Var(e.index_var, type=e.index_var_type)))
    else:
        raise TypeError
    return ctx2

def apply_subterm(e: Expr, f: Callable[[Expr, Context], Expr], ctx: Context) -> Expr:
    def rec(e: Expr, ctx: Context):
        if expr.is_var(e) or expr.is_const(e) or expr.is_inf(e) or expr.is_skolem_func(e):
            return f(e, ctx)
        elif expr.is_op(e):
            args = [rec(arg, ctx) for arg in e.args]
            return f(expr.Op(e.op, *args), ctx)
        elif expr.is_fun(e):
            args = [rec(arg, ctx) for arg in e.args]
            return f(expr.Fun((e.func_name, e.func_type), *args), ctx)
        elif expr.is_deriv(e):
            return f(expr.Deriv(e.var, rec(e.body, ctx)), ctx)
        elif expr.is_integral(e):
            lower = rec(e.lower, ctx)
            upper = rec(e.upper, ctx)
            body = rec(e.body, body_conds(e, ctx))
            return f(expr.Integral(e.var, lower, upper, body), ctx)
        elif expr.is_evalat(e):
            lower = rec(e.lower, ctx)
            upper = rec(e.upper, ctx)
            body = rec(e.body, ctx)
            return f(expr.EvalAt(e.var, lower, upper, body), ctx)
        elif expr.is_limit(e):
            return f(expr.Limit(e.var, rec(e.lim, ctx), rec(e.body, body_conds(e, ctx))), ctx)
        elif expr.is_indefinite_integral(e):
            return f(expr.IndefiniteIntegral(e.var, rec(e.body, ctx), e.skolem_args), ctx)
        elif expr.is_summation(e):
            lower = rec(e.lower, ctx)
            upper = rec(e.upper, ctx)
            body = rec(e.body, body_conds(e, ctx))
            return f(expr.Summation(e.index_var, lower, upper, body), ctx)
        elif expr.is_product(e):
            lower = rec(e.lower, ctx)
            upper = rec(e.upper, ctx)
            body = rec(e.body, body_conds(e, ctx))
            return f(expr.Product(e.index_var, lower, upper, body), ctx)
        elif expr.is_matrix(e):
            return f(Matrix([[rec(item, ctx) for item in row] for row in e.data], e.type), ctx)
        elif expr.is_symbol(e):
            return e
        else:
            raise NotImplementedError
    return rec(e, ctx)
