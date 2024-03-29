"""State of computation"""

from typing import List, Optional, Union

from integral.expr import Expr, Var, Const
from integral import rules, expr
from integral.rules import Rule, check_wellformed
from integral.conditions import Conditions
from integral.context import Context
from integral import latex
from integral import parser
from integral.poly import normalize


class Label:
    def __init__(self, data):
        self.data = []
        if isinstance(data, str):
            split = data.split(".")
            for n in split:
                if n == '':
                    continue
                assert int(n) >= 1, "Label: non-positive value"
                self.data.append(int(n) - 1)
        elif isinstance(data, list):
            assert all(n >= 0 for n in data), "Label: negative value"
            self.data = list(data)
        else:
            raise AssertionError("Label: unexpected type")

    @property
    def head(self):
        return self.data[0]

    @property
    def tail(self):
        return Label(self.data[1:])

    def empty(self):
        return len(self.data) == 0

    def __str__(self):
        res = ""
        for n in self.data:
            res += str(n + 1) + "."
        return res


class StateItem:
    """Items in a state of computation"""
    ctx: Context

    def export(self):
        """Obtain the JSON representation of the item."""
        raise NotImplementedError

    def export_book(self):
        """Obtain the JSON representation of the item in the book file."""
        raise NotImplementedError

    def get_by_label(self, label: Label) -> "StateItem":
        """Return the object at the given label."""
        raise NotImplementedError

    def get_facts(self):
        """Return the list of facts in this item."""
        return []

    def clear(self):
        """Clear itself."""
        pass

    def is_finished(self):
        """Whether the proof in the item is finished. Default to true."""
        return True


class FuncDef(StateItem):
    """Introduce a new function definition."""
    def __init__(self, parent: "CompFile", ctx: Context, eq: Expr, conds: Optional[Conditions] = None):
        if not eq.is_equals():
            raise AssertionError("FuncDef: input should be an equation")

        self.parent = parent
        self.ctx = ctx

        self.eq = eq
        if self.eq.lhs.is_fun():
            self.symb = self.eq.lhs.func_name
            self.args = self.eq.lhs.args
        elif self.eq.lhs.is_var():
            self.symb = self.eq.lhs.name
            self.args = []
        else:
            raise AssertionError("FuncDef: left side of equation must be variable or function")
        self.body = self.eq.rhs

        if any(not arg.is_var() for arg in self.args) or len(self.args) != len(set(self.args)):
            raise AssertionError("FuncDef: arguments should be distinct variables")

        if conds is None:
            conds = Conditions()
        self.conds = conds

    def __str__(self):
        res = "Definition\n"
        res += "  %s\n" % self.eq
        return res

    def __eq__(self, other):
        return isinstance(other, FuncDef) and self.eq == other.eq and self.conds == other.conds

    def export(self):
        res = {
            "type": "FuncDef",
            "eq": str(self.eq),
            "latex_lhs": latex.convert_expr(self.eq.lhs),
            "latex_eq": latex.convert_expr(self.eq)
        }
        if self.conds.data:
            res["conds"] = self.conds.export()
        return res

    def export_book(self):
        p = self.parent
        while (not isinstance(p, CompFile)):
            p = p.parent
        res = {
            "type": "definition",
            "expr": str(self.eq),
            "path": p.name
        }
        if self.conds.data:
            res["conds"] = [str(cond) for cond in self.conds.data]
        return res

    def get_by_label(self, label: Label):
        if not label.empty():
            raise AssertionError("get_by_label: invalid label")
        return self

    def get_facts(self):
        return [self.eq]


class Goal(StateItem):
    """Goal to be proved."""
    def __init__(self, parent, ctx: Context, goal: Expr, conds: Optional[Conditions] = None):
        self.parent = parent
        self.goal = goal
        if conds is None:
            conds = Conditions()
        self.conds = conds
        self.proof = None
        self.ctx = Context(ctx)
        self.ctx.extend_condition(self.conds)
        self.proof_obligations = check_wellformed(goal, self.ctx)
        self.wellformed = (len(self.proof_obligations) == 0)

    def __str__(self):
        if self.is_finished():
            res = "Goal (finished)\n"
        else:
            res = "Goal\n"
        res += "  %s\n" % self.goal
        if self.proof is not None:
            res += str(self.proof)
        return res

    def __eq__(self, other):
        return isinstance(other, Goal) and self.goal == other.goal and self.conds == other.conds and \
               self.proof == other.proof

    def is_finished(self):
        return self.proof is not None and self.proof.is_finished()

    def clear(self):
        self.proof = None

    def export(self):
        res = {
            "type": "Goal",
            "goal": str(self.goal),
            "latex_goal": latex.convert_expr(self.goal),
            "finished": self.is_finished(),
        }
        if self.proof:
            res['proof'] = self.proof.export()
        if self.conds.data:
            res['conds'] = self.conds.export()
        if not self.wellformed:
            res['wellformed'] = False
            res['obligations'] = [p.export() for p in self.proof_obligations]
        return res

    def export_book(self):
        p = self.parent
        while (not isinstance(p, CompFile)):
            p = p.parent
        res = {
            "type": "problem",
            "expr": str(self.goal),
            "path": p.name
        }
        if self.conds.data:
            res["conds"] = [str(cond) for cond in self.conds.data]
        return res

    def proof_by_rewrite_goal(self, *, begin: "Goal"):
        self.proof = RewriteGoalProof(self, self.goal, begin=begin)
        return self.proof

    def proof_by_calculation(self):
        self.proof = CalculationProof(self, self.goal)
        return self.proof

    def proof_by_induction(self, induct_var: str, start: int = 0):
        self.proof = InductionProof(self, self.goal, induct_var, start=start)
        return self.proof

    def proof_by_case(self, cond_str: str):
        e1 = parser.parse_expr(cond_str)
        self.proof = CaseProof(self, self.goal, split_cond=e1)
        return self.proof

    def get_by_label(self, label: Label):
        if label.empty():
            return self
        else:
            if self.proof is None:
                raise AssertionError("get_by_label: goal %s has no proof" % str(self.goal))
            return self.proof.get_by_label(label)

    def get_facts(self):
        return [self.goal]

    def get_induct_hyp_goal(self):
        from integral import context
        res = self.ctx.get_induct_hyps()
        if len(res) != None:
            e = res[0]
            if isinstance(e, context.Identity):
                return Goal(self, self.ctx, expr.Op("=", e.lhs, e.rhs), self.conds)
        raise NotImplementedError

class CalculationStep(StateItem):
    """A step in the calculation."""
    def __init__(self, parent: "Calculation", rule: Rule, res: Expr, id: int):
        self.parent = parent
        self.rule = rule
        self.res = res
        self.id = id
        self.ctx = parent.ctx

    def __str__(self):
        return "%s (%s)" % (self.res, self.rule)

    def __eq__(self, other):
        return isinstance(other, CalculationStep) and self.rule == other.rule and self.res == other.res

    def export(self):
        return {
            "type": "CalculationStep",
            "rule": self.rule.export(),
            "res": str(self.res),
            "latex_res": latex.convert_expr(self.res)
        }

    def clear(self):
        self.parent.clear(id=self.id)

    def perform_rule(self, rule: Rule):
        self.parent.perform_rule(rule, self.id)

    def perform_rules(self, calc_rules: tuple[Rule]):
        self.parent.perform_rules(calc_rules, self.id)


class Calculation(StateItem):
    """Calculation starting from an expression.

    start: starting expression.
    conds: (optional) a list of conditions under which the calculation
        is carried out.

    """
    def __init__(self, parent, ctx: Context, start: Expr, *,
                 connection_symbol='=', conds: Optional[Conditions] = None):
        self.parent = parent
        self.start = start
        self.steps: List[CalculationStep] = []
        if conds is None:
            conds = Conditions()
        self.conds = conds
        self.connection_symbol = connection_symbol
        if conds is None:
            self.ctx = ctx
        else:
            self.ctx = Context(ctx)
            self.ctx.extend_condition(self.conds)

    def __str__(self):
        res = "  " + str(self.start) + "\n"
        for step in self.steps:
            res += self.connection_symbol + " %s\n" % step
        return res

    def export(self):
        res = {
            "type": "Calculation",
            "start": str(self.start),
            "latex_start": latex.convert_expr(self.start),
            "steps": [step.export() for step in self.steps]
        }
        if self.conds.data:
            res["conds"] = self.conds.export()
        return res

    def clear(self, id: int = 0):
        self.steps = self.steps[:id]

    def add_step(self, step: CalculationStep):
        """Add the given step to the computation."""
        self.steps.append(step)

    @property
    def last_expr(self) -> Expr:
        """Last expression of the calculation."""
        if self.steps:
            return self.steps[-1].res
        else:
            return self.start

    def perform_rule(self, rule: Rule, id: Optional[int] = None):
        """Perform the given rule on the current expression."""
        if id is not None:
            # Cut off later steps
            self.steps = self.steps[:id + 1]
        else:
            id = len(self.steps) - 1

        e = self.last_expr
        ctx = Context(self.ctx)
        for step in self.steps:
            for var, subst_e in step.rule.get_substs().items():
                ctx.add_subst(var, subst_e)
                ctx.add_condition(expr.Op("=", expr.Var(var), subst_e))
        new_e = rule.eval(e, ctx)
        self.add_step(CalculationStep(self, rule, new_e, id + 1))

    def perform_rules(self, calc_rules: tuple[Rule], id: Optional[int] = None):
        for rule in calc_rules:
            self.perform_rule(rule)

    def get_by_label(self, label: Label) -> "StateItem":
        if label.empty():
            return self
        elif label.tail.empty():
            return self.steps[label.head]
        else:
            raise AssertionError("get_by_label: invalid label")


class CalculationProof(StateItem):
    """Proof for an equation by calculation.

    The proof consists of calculation of left and right sides.

    """
    def __init__(self, parent, goal: Expr):
        self.parent = parent
        self.goal = goal
        self.ctx = parent.ctx
        self.calcs = []

        if goal.is_compare():
            self.predicate = goal.op
            self.calcs.append(Calculation(self, self.ctx, self.goal.args[0]))
            self.calcs.append(Calculation(self, self.ctx, self.goal.args[1]))
        elif goal.is_fun() and goal.func_name == "converges":
            self.predicate = goal.func_name
            self.calcs.append(Calculation(self, self.ctx, self.goal.args[0]))
        else:
            raise AssertionError("CalculationProof: unknown form of goal.")

    def __str__(self):
        if self.is_finished():
            res = "Proof by calculation (finished)\n"
        else:
            res = "Proof by calculation\n"
        for calc in self.calcs:
            if calc.steps:
                res += str(calc)
        return res

    @property
    def lhs_calc(self) -> Calculation:
        assert self.goal.is_compare()
        return self.calcs[0]

    @property
    def rhs_calc(self) -> Calculation:
        assert self.goal.is_compare()
        return self.calcs[1]

    @property
    def arg_calc(self) -> Calculation:
        assert self.goal.is_fun()
        return self.calcs[0]

    def is_finished(self):
        if self.predicate == '=':
            return self.lhs_calc.last_expr == self.rhs_calc.last_expr
        elif self.predicate == '>':
            return self.ctx.is_greater(self.lhs_calc.last_expr, self.rhs_calc.last_expr)
        elif self.predicate == '<':
            return self.ctx.is_less(self.lhs_calc.last_expr, self.rhs_calc.last_expr)
        elif self.predicate == '<=':
            return self.ctx.is_less_eq(self.lhs_calc.last_expr, self.rhs_calc.last_expr)
        elif self.predicate == '>=':
            return self.ctx.is_greater_eq(self.lhs_calc.last_expr, self.rhs_calc.last_expr)
        elif self.predicate == '!=':
            return self.ctx.is_not_equal(self.lhs_calc.last_expr, self.rhs_calc.last_expr)
        elif self.predicate == 'converges':
            return rules.check_converge(self.arg_calc.last_expr, self.ctx)
        raise NotImplementedError

    def export(self):
        return {
            "type": "CalculationProof",
            "goal": str(self.goal),
            "latex_goal": latex.convert_expr(self.goal),
            "finished": self.is_finished(),
            "calcs": [calc.export() for calc in self.calcs]
        }

    def clear(self):
        for calc in self.calcs:
            calc.clear()

    def get_by_label(self, label: Label):
        if label.empty():
            return self
        elif label.head < len(self.calcs):
            return self.calcs[label.head].get_by_label(label.tail)
        else:
            raise AssertionError("get_by_label: invalid label")

class InductionProof(StateItem):
    """Proof for an equation by induction on natural numbers.

    This breaks the equation goal into two goals, corresponding to the
    base case and inductive case.

    """
    def __init__(self, parent, goal: Expr, induct_var: str, *, start: Union[int, Expr] = 0):
        if not goal.is_equals():
            print(str(goal))
            raise AssertionError("InductionProof: currently only support equation goals.")

        self.parent = parent
        self.goal = goal
        self.induct_var = induct_var
        self.ctx = parent.ctx

        if isinstance(start, int):
            self.start = Const(start)
        elif isinstance(start, Expr):
            self.start = start
        else:
            raise NotImplementedError

        # Base case: n = start
        eq0 = normalize(goal.subst(induct_var, self.start), self.ctx)
        self.base_case = Goal(self, self.ctx, eq0)

        # Inductive case:
        eqI = normalize(goal.subst(induct_var, Var(induct_var) + 1), self.ctx)
        ctx = Context(self.ctx)
        ctx.add_induct_hyp(self.goal)
        self.induct_case = Goal(self, ctx, eqI)

    def __str__(self):
        if self.is_finished():
            res = "Proof by induction on %s (finished)\n" % self.induct_var
        else:
            res = "Proof by induction on %s\n" % self.induct_var
        res += "Base case: %s\n" % self.base_case.goal
        res += str(self.base_case)
        res += "Induct case: %s\n" % self.induct_case.goal
        res += str(self.induct_case)
        return res

    def is_finished(self):
        return self.base_case.is_finished() and self.induct_case.is_finished()

    def export(self):
        return {
            "type": "InductionProof",
            "goal": str(self.goal),
            "latex_goal": latex.convert_expr(self.goal),
            "induct_var": self.induct_var,
            "base_case": self.base_case.export(),
            "induct_case": self.induct_case.export(),
            "finished": self.is_finished()
        }

    def clear(self):
        self.base_case.clear()
        self.induct_case.clear()

    def get_by_label(self, label: Label):
        if label.empty():
            return self
        elif label.head == 0:
            return self.base_case.get_by_label(label.tail)
        elif label.head == 1:
            return self.induct_case.get_by_label(label.tail)
        else:
            raise AssertionError("get_by_label: invalid label")

class CaseProof(StateItem):
    """Prove an equation by cases.
    
    If split_cond is a condition, the two cases correspond to split_cond
    being true and false, respectively.

    If split_cond is an expression a, the three cases correspond to
    a > 0, a = 0, and a < 0.
    
    """
    def __init__(self, parent, goal: Expr, *, split_cond: Expr):
        self.parent = parent
        self.goal = goal
        self.ctx = parent.ctx
        self.split_cond = split_cond
        self.split_type = ""
        self.cases: List[Goal] = []

        if split_cond.is_compare():
            self.split_type = "two-way"
            # Case 1:
            conds1 = Conditions()
            conds1.add_condition(split_cond)
            self.cases.append(Goal(self, self.ctx, goal, conds=conds1))

            # Case 2:
            conds2 = Conditions()
            conds2.add_condition(expr.neg_expr(split_cond))
            self.cases.append(Goal(self, self.ctx, goal, conds=conds2))

        else:
            self.split_type = "three-way"
            # Case 1:
            conds1 = Conditions()
            conds1.add_condition(expr.Op("<", split_cond, Const(0)))
            self.cases.append(Goal(self, self.ctx, goal, conds=conds1))

            # Case 2:
            conds2 = Conditions()
            conds2.add_condition(expr.Op("=", split_cond, Const(0)))
            self.cases.append(Goal(self, self.ctx, goal, conds=conds2))

            # Case 3:
            conds3 = Conditions()
            conds3.add_condition(expr.Op(">", split_cond, Const(0)))
            self.cases.append(Goal(self, self.ctx, goal, conds=conds3))

    def __str__(self):
        if self.is_finished():
            res = "Proof by cases (finished)\n"
        else:
            res = "Proof by cases\n"
        for i, case in enumerate(self.cases):
            res += "case%d: %s for %s\n" % (i + 1, case.goal, case.conds)
            res += str(case)
        return res

    def is_finished(self):
        for case in self.cases:
            if not case.is_finished():
                return False
        return True

    def export(self):
        return {
            "type": "CaseProof",
            "goal": str(self.goal),
            "latex_goal": latex.convert_expr(self.goal),
            "cases": [case.export() for case in self.cases],
            "split_cond": str(self.split_cond),
            "latex_split_cond": latex.convert_expr(self.split_cond),
            "finished": self.is_finished()
        }

    def clear(self):
        for case in self.cases:
            case.clear()

    def get_by_label(self, label: Label):
        if label.empty():
            return self
        elif label.head < len(self.cases):
            return self.cases[label.head].get_by_label(label.tail)
        else:
            raise AssertionError("get_by_label: invalid label")

class RewriteGoalProof(StateItem):
    """Prove an equation by transforming an initial equation.
    """
    def __init__(self, parent, goal: Expr, *, begin: Goal):
        if not goal.is_equals():
            raise AssertionError("RewriteGoalProof: goal is not an equality.")

        self.parent = parent
        self.goal = goal
        self.ctx = parent.ctx
        self.begin = Calculation(parent, self.ctx, begin.goal, conds=begin.conds, connection_symbol = '==>')

    def is_finished(self):
        f1 = normalize(self.begin.last_expr.lhs, self.ctx) == normalize(self.goal.lhs, self.ctx)
        f2 = normalize(self.begin.last_expr.rhs, self.ctx) == normalize(self.goal.rhs, self.ctx)
        return f1 and f2

    def export(self):
        return {
            "type": "RewriteGoalProof",
            "goal": str(self.goal),
            "latex_goal": latex.convert_expr(self.goal),
            "start": self.begin.export(),
            "finished": self.is_finished()
        }

    def clear(self):
        self.begin.clear()

    def __str__(self):
        if self.is_finished():
            res = "Proof by rewriting equation (finished)\n"
        else:
            res = "Proof by rewriting equation\n"

        res += str(self.begin)
        return res

    def get_by_label(self, label: Label):
        if label.empty() or len(label.data) == 1:
            return self
        elif not label.tail.empty():
            return self.begin.steps[label.tail.head]
        else:
            raise AssertionError("get_by_label: invalid label")


class CompFile:
    """Represent a file containing multiple StateItem objects.
    
    ctx - initial context of the file.
    name - name of the file.

    """
    def __init__(self, ctx: Union[Context, str], name: str):
        if isinstance(ctx, str):
            self.ctx = Context()
            self.ctx.load_book(ctx, upto=name)
        else:
            self.ctx = ctx
        self.name: str = name
        self.content: List[StateItem] = []

    def __str__(self):
        res = "File %s\n" % self.name
        for st in self.content:
            res += str(st)
        return res

    def get_context(self, index: int = -1) -> Context:
        """Obtain the context up to the particular index (exclusive).
        
        If index = -1, return the context after processing all the content.
        
        """
        ctx = Context(self.ctx)
        for item in (self.content if index == -1 else self.content[:index]):
            if isinstance(item, FuncDef):
                ctx.add_definition(item.eq)
                ctx.add_lemma(item.eq, item.conds)
            elif isinstance(item, Goal):
                ctx.add_lemma(item.goal, item.conds)
                ctx.extend_by_item(item.export_book())
        return ctx

    def add_definition(self, funcdef: Union[str, Expr], *, conds: List[Union[str, Expr]] = None) -> FuncDef:
        """Add a function definition.
        
        funcdef: statement of the definition.
        conds: list of conditions for the definition. This is ignored if input
               is already of type FuncDef.
        
        """
        if conds is not None:
            for i in range(len(conds)):
                if isinstance(conds[i], str):
                    conds[i] = parser.parse_expr(conds[i])
        else:
            conds = []

        ctx = self.get_context()
        if isinstance(funcdef, str):
            self.content.append(FuncDef(self, ctx, parser.parse_expr(funcdef), Conditions(conds)))
        elif isinstance(funcdef, Expr):
            self.content.append(FuncDef(self, ctx, funcdef, Conditions(conds)))
        else:
            raise NotImplementedError
        return self.content[-1]

    def add_calculation(self, calc: Union[str, Expr], *, conds: List[Union[str, Expr]] = None) -> Calculation:
        """Add a calculation."""
        ctx = self.get_context()
        if conds is not None:
            for i in range(len(conds)):
                if isinstance(conds[i], str):
                    conds[i] = parser.parse_expr(conds[i])
        else:
            conds = []
        conds = Conditions(conds)
        if isinstance(calc, str):
            self.content.append(Calculation(self, ctx, parser.parse_expr(calc), conds=conds))
        elif isinstance(calc, Expr):
            self.content.append(Calculation(self, ctx, calc, conds=conds))
        else:
            raise NotImplementedError
        return self.content[-1]

    def add_goal(self, goal: Union[str, Expr, Goal], *, conds: List[Union[str, Expr]] = None) -> Goal:
        """Add a goal.

        goal: statement of the goal.
        conds: list of conditions for the goal. This is ignored if input goal
               is already of type Goal.

        """
        if isinstance(goal, Goal):
            self.content.append(goal)
            return self.content[-1]
        if conds is not None:
            for i in range(len(conds)):
                if isinstance(conds[i], str):
                    conds[i] = parser.parse_expr(conds[i])
        else:
            conds = []

        if isinstance(goal, str):
            goal = parser.parse_expr(goal)
        assert isinstance(goal, Expr)

        conds = Conditions(conds)
        ctx = self.get_context()
        self.content.append(Goal(self, ctx, goal, conds))
        return self.content[-1]

    def add_item(self, item: StateItem):
        """Add item of arbitrary type"""
        self.content.append(item)

    def export(self):
        self.name = self.name
        return {
            "name": self.name,
            "content": [item.export() for item in self.content]
        }


def parse_rule(item) -> Rule:
    if 'loc' in item:
        if item['loc'] == 'subterms':
            del item['loc']
            return rules.OnSubterm(parse_rule(item))
        else:
            loc = item['loc']
            del item['loc']
            if loc == '' or loc == '.':
                return parse_rule(item)
            else:
                return rules.OnLocation(parse_rule(item), loc)
    elif item['name'] == 'ExpandDefinition':
        func_name = item['func_name']
        return rules.ExpandDefinition(func_name=func_name)
    elif item['name'] == 'FoldDefinition':
        func_name = item['func_name']
        return rules.FoldDefinition(func_name=func_name)
    elif item['name'] == 'DerivIntExchange':
        return rules.DerivIntExchange()
    elif item['name'] == 'FullSimplify':
        return rules.FullSimplify()
    elif item['name'] == 'ElimInfInterval':
        a = Const(0)
        if 'a' in item:
            a = parser.parse_expr(item['a'])
        return rules.ElimInfInterval(a)
    elif item['name'] == 'Substitution':
        var_name = item['var_name']
        var_subst = parser.parse_expr(item['var_subst'])
        return rules.Substitution(var_name, var_subst)
    elif item['name'] == 'SubstitutionInverse':
        var_name = item['var_name']
        var_subst = parser.parse_expr(item['var_subst'])
        return rules.SubstitutionInverse(var_name, var_subst)
    elif item['name'] == 'IntegrationByParts':
        u = parser.parse_expr(item['u'])
        v = parser.parse_expr(item['v'])
        return rules.IntegrationByParts(u, v)
    elif item['name'] == 'Equation':
        new_expr = parser.parse_expr(item['new_expr'])
        old_expr = parser.parse_expr(item['old_expr']) if ('old_expr' in item) else None
        return rules.Equation(old_expr, new_expr)
    elif item['name'] == 'ApplyEquation':
        eq = parser.parse_expr(item['eq'])
        return rules.ApplyEquation(eq)
    elif item['name'] == 'ExpandPolynomial':
        return rules.ExpandPolynomial()
    elif item['name'] == 'SplitRegion':
        c = parser.parse_expr(item['c'])
        return rules.SplitRegion(c)
    elif item['name'] == 'IntegrateByEquation':
        lhs = parser.parse_expr(item['lhs'])
        return rules.IntegrateByEquation(lhs)
    elif item['name'] == 'LHopital':
        return rules.LHopital()
    elif item['name'] == 'ApplyInductHyp':
        return rules.ApplyInductHyp()
    elif item['name'] == 'DerivativeSimplify':
        return rules.DerivativeSimplify()
    elif item['name'] == 'IntegrateBothSide':
        return rules.IntegralEquation()
    elif item['name'] == 'LimitEquation':
        var = item['var']
        lim = parser.parse_expr(item['lim'])
        return rules.LimitEquation(var, lim)
    elif item['name'] == 'IntSumExchange':
        return rules.IntSumExchange()
    elif item['name'] == 'DerivEquation':
        var = item['var']
        return rules.DerivEquation(var)
    elif item['name'] == 'SolveEquation':
        solve_for = parser.parse_expr(item['solve_for'])
        return rules.SolveEquation(solve_for)
    elif item['name'] == 'VarSubsOfEquation':
        subst = item['subst']
        return rules.VarSubsOfEquation(subst)
    elif item['name'] == 'ApplyIdentity':
        source = parser.parse_expr(item['source'])
        target = parser.parse_expr(item['target'])
        return rules.ApplyIdentity(source, target)
    elif item['name'] == 'IndefiniteIntegralIdentity':
        return rules.IndefiniteIntegralIdentity()
    elif item['name'] == 'DefiniteIntegralIdentity':
        return rules.DefiniteIntegralIdentity()
    elif item['name'] == 'SeriesExpansionIdentity':
        index_var = item['index_var']
        old_expr = None
        if 'old_expr' in item:
            old_expr = parser.parse_expr(item['old_expr'])
        return rules.SeriesExpansionIdentity(old_expr=old_expr, index_var=index_var)
    elif item['name'] == 'SeriesEvaluationIdentity':
        return rules.SeriesEvaluationIdentity()
    elif item['name'] == 'ReplaceSubstitution':
        return rules.ReplaceSubstitution()
    elif item['name'] == 'ChangeSummationIndex':
        e = parser.parse_expr(item['new_lower'])
        return rules.ChangeSummationIndex(e)
    elif item['name'] == 'SummationEquation':
        idx_v = item['index_var']
        lower = parser.parse_expr(item['lower'])
        upper = parser.parse_expr(item['upper'])
        return rules.SummationEquation(idx_v, lower, upper)
    elif item['name'] == 'FunEquation':
        func_name = item['func_name']
        return rules.FunEquation(func_name)
    elif item['name'] == 'PartialFractionDecomposition':
        return rules.PartialFractionDecomposition()
    else:
        print(item['name'], flush=True)
        raise NotImplementedError

def parse_step(parent: Calculation, item, id: int) -> CalculationStep:
    if item['type'] != 'CalculationStep':
        raise AssertionError('parse_step')

    rule = parse_rule(item['rule'])
    res = parser.parse_expr(item['res'])
    step = CalculationStep(parent, rule, res, id)
    return step

def parse_conds(item) -> Conditions:
    res = Conditions()
    if 'conds' in item:
        for subitem in item['conds']:
            res.add_condition(parser.parse_expr(subitem['cond']))
    return res

def parse_item(parent, item) -> StateItem:
    if item['type'] == 'FuncDef':
        conds = parse_conds(item)
        eq = parser.parse_expr(item['eq'])
        ctx = parent.get_context() if isinstance(parent, CompFile) else parent.ctx
        return FuncDef(parent, ctx, eq, conds=conds)
    elif item['type'] == 'Goal':
        goal = parser.parse_expr(item['goal'])
        conds = parse_conds(item)
        ctx = parent.get_context() if isinstance(parent, CompFile) else parent.ctx
        res = Goal(parent, ctx, goal, conds=conds)
        if 'proof' in item:
            res.proof = parse_item(res, item['proof'])
        if 'wellformed' in item:
            res.wellformed = item['wellformed']
            if not res.wellformed and 'obligations' in item:
                res.proof_obligations = list()
                for obligation in item['obligations']:
                    branches = list()
                    for b in obligation['branches']:
                        tmp = list()
                        for e in b['exprs']:
                            tmp.append(parser.parse_expr(e))
                        branches.append(rules.ProofObligationBranch(tmp))
                    c = parse_conds(obligation)
                    res.proof_obligations.append(rules.ProofObligation(branches, c))
        return res
    elif item['type'] == 'CalculationProof':
        goal = parser.parse_expr(item['goal'])
        res = CalculationProof(parent, goal)
        for i, calc_item in enumerate(item['calcs']):
            res.calcs[i] = parse_item(res, calc_item)
        return res
    elif item['type'] == 'Calculation':
        start = parser.parse_expr(item['start'])
        ctx = parent.get_context() if isinstance(parent, CompFile) else parent.ctx
        conds = parse_conds(item)
        res = Calculation(parent, ctx, start, conds=conds)
        for i, step in enumerate(item['steps']):
            res.add_step(parse_step(res, step, i))
        return res
    elif item['type'] == 'InductionProof':
        goal = parser.parse_expr(item['goal'])
        induct_var = item['induct_var']
        res = InductionProof(parent, goal, induct_var)
        res.base_case = parse_item(res, item['base_case'])
        res.induct_case = parse_item(res, item['induct_case'])
        res.induct_case.ctx.add_induct_hyp(goal)
        return res
    elif item['type'] == 'CaseProof':
        goal = parser.parse_expr(item['goal'])
        split_cond = parser.parse_expr(item['split_cond'])
        res = CaseProof(parent, goal, split_cond=split_cond)
        assert len(res.cases) == len(item['cases'])
        for i, case in enumerate(item['cases']):
            res.cases[i] = parse_item(res, case)
        return res
    elif item['type'] == 'RewriteGoalProof':
        goal = parser.parse_expr(item['goal'])
        begin_goal = parser.parse_expr(item['start']['start'])
        begin_conds = parse_conds(item['start'])
        res = RewriteGoalProof(parent, goal=goal, begin=Goal(parent, parent.ctx, begin_goal, begin_conds))
        for i, step in enumerate(item['start']['steps']):
            res.begin.add_step(parse_step(res.begin, step, i))
        return res
    else:
        print(item['type'])
        raise NotImplementedError

def get_next_step_label(step: Union[Calculation, CalculationStep], label: Label) -> Label:
    if isinstance(step, Calculation):
        return Label(label.data + [0])
    elif isinstance(step, CalculationStep):
        return Label(label.data[:-1] + [label.data[-1] + 1])
    elif isinstance(step, RewriteGoalProof):
        return Label(label.data + [0])
    else:
        raise NotImplementedError

import os,json
dirname = os.path.dirname(__file__)
def edit_book(label:str, book_name:str, data:dict):
    pos = label.split(".")[:-1]
    book_path = os.path.join(dirname, "../examples/" + book_name + '.json')
    with open(book_path, 'r', encoding='utf-8') as f:
        book_content = json.load(f)
    if len(pos) == 0:
        book_content['content'].append(data)
    else:
        pos = [int(i) - 1 for i in pos]
        pos.reverse()

        def rec(content, locs, d):
            res = content
            if len(locs) == 0:
                res.append(d)
            else:
                p = locs.pop()
                res[p]['content'] = rec(content[p]['content'], locs, d)
            return res

        book_content['content'] = rec(book_content['content'], pos, data)
    with open(book_path, 'w', encoding='utf-8') as f:
        json.dump(book_content, f, indent=4, ensure_ascii=False, sort_keys=True)


def edit_problem_file(book_name: str, name: str, imported: dict):
    file = CompFile(book_name, name)
    file_path = os.path.join(dirname, "../examples/" + name + '.json')
    if os.path.exists(file_path):
        with open(file_path, 'r', encoding='utf-8') as f:
            problem = json.load(f)
        for item in problem['content']:
            file.add_item(parse_item(file, item))
    if imported['type'] == 'goal':
        file.add_goal(imported['goal'], conds=imported['conds'])
    elif imported['type'] == 'definition':
        file.add_definition(imported['eq'], conds=imported['conds'])
    with open(file_path, 'w', encoding='utf-8') as f:
        json.dump(file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)
