"""State of computation"""
import copy
from typing import Dict, List, Optional, Union, Tuple

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
        elif isinstance(data, Label):
            self.data = data.data
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

    def __eq__(self, other):
        return isinstance(other,Label) and self.data == other.data

    def append(self, i: int) -> "Location":
        return Label(self.data + [i,])

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
        if expr.is_fun(self.eq.lhs):
            self.symb = self.eq.lhs.func_name
            self.args = self.eq.lhs.args
        elif expr.is_var(self.eq.lhs):
            self.symb = self.eq.lhs.name
            self.args = []
        else:
            raise AssertionError("FuncDef: left side of equation must be variable or function")
        self.body = self.eq.rhs

        if any (not expr.is_var(arg) for arg in self.args) or len(self.args) != len(set(self.args)):
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
    def __init__(self, parent:Union['CompFile', StateItem], ctx: Context, goal: Expr, *,
                 fixes: Optional[Dict[str, expr.Type]] = None,
                 conds: Optional[Conditions] = None):
        self.parent = parent

        # Statement to be proved
        self.goal = goal

        # Mapping from variables to their types
        self.fixes: Dict[str, expr.Type] = dict()
        if fixes is not None:
            self.fixes = fixes

        # List of assumptions for the goal
        if conds is None:
            conds = Conditions()
        self.conds = conds

        self.proof = None
        self.ctx = Context(ctx)

        self.ctx.extend_condition(self.conds)
        self.ctx.extend_fixes(self.fixes)

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
        if not isinstance(other, Goal):
            return False
        return self.proof == other.proof

    def is_finished(self):
        # all conds are satisfied under context of proof
        if self.proof == None:
            return False
        if isinstance(self.proof, RewriteGoalProof):
            proof_has_conds = len(self.proof.begin.ctx.get_conds().data) > 0
            goal_has_conds = len(self.ctx.get_conds().data) > 0
            if not goal_has_conds and proof_has_conds:
                proof_cond_vars = set()
                for cond in self.proof.begin.ctx.get_conds().data:
                    cond:Expr
                    proof_cond_vars = proof_cond_vars.union(cond.get_vars())
                goal_vars = self.goal.get_vars()
                return goal_vars.intersection(proof_cond_vars) == set()
            elif not goal_has_conds and not proof_has_conds:
                return self.proof.is_finished()
            elif goal_has_conds and proof_has_conds:
                return self.proof.is_finished() and self.ctx.check_all_condtions(self.goal, self.proof.begin.ctx.get_conds())
            else:
                return self.proof.is_finished()
        else:
            return self.proof.is_finished()


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
        if len(self.fixes.items()) > 0:
            d = list()
            for a, b in self.fixes.items():
                d.append((a, str(b)))
            res['fixes'] = d
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
        if len(self.fixes.items()) > 0:
            d = list()
            for a, b in self.fixes.items():
                d.append((a, str(b)))
            res['fixes'] = d
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

    def proof_by_case(self, split_cond: Expr):
        self.proof = CaseProof(self, self.goal, split_cond=split_cond)
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


class CalculationStep(StateItem):
    """A step in the calculation."""
    def __init__(self, parent: "Calculation", rule: Rule, res: Expr, id: int):
        self.parent = parent
        self.rule = rule
        self.res = res
        self.id = id
        self.ctx = Context(parent.ctx)

    def __str__(self):
        return "%s (%s)" % (self.res, self.rule)

    def __eq__(self, other):
        if not isinstance(other, CalculationStep):
            return False
        return self.rule.name == other.rule.name and str(self.res) == str(other.res)

    def export(self):
        return {
            "type": "CalculationStep",
            "rule": self.rule.export(),
            "res": str(self.res),
            "latex_res": latex.convert_expr(self.res),
            'fixes': [[a, str(b)] for a, b in self.ctx.fixes.items()],
            'dead_vars': [a for a in self.ctx.dead_vars]
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
                 connection_symbol='=', conds: Optional[Conditions] = None,
                 fixes:Tuple[Dict[str, expr.Type], Dict[str, expr.Type]]=None):
        self.parent = parent
        self.start = start
        self.steps: List[CalculationStep] = []
        if conds is None:
            conds = Conditions()
        self.conds = conds
        self.connection_symbol = connection_symbol
        self.ctx = Context(ctx)
        if conds is not None:
            self.ctx.extend_condition(self.conds)
        if fixes is not None:
            self.ctx.extend_fixes(fixes[0])
            self.ctx.dead_vars.update(fixes[1])

    def __eq__(self, other):
        if not isinstance(other, Calculation):
            return False
        return self.steps == other.steps

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
            "steps": [step.export() for step in self.steps],
            'fixes': [[a, str(b)] for a, b in self.ctx.fixes.items()],
            'dead_vars': [a for a in self.ctx.dead_vars]
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
        ctx = Context(self.ctx, self.ctx.d + 1)
        for step in self.steps:
            for var, subst_e in step.rule.get_substs().items():
                ctx.add_subst(var, subst_e)
                ctx.add_condition(expr.Op("=", expr.Var(var), subst_e))
        new_e = rule.eval(e, ctx)
        step = CalculationStep(self, rule, new_e, id + 1)

        # update fixes and dead_vars of calculation
        remove_vars = e.get_vars(with_bd=True).difference(new_e.get_vars(with_bd=True))
        tmp = dict()
        goal_fixes = self.ctx.parent.get_fixes()
        for v in remove_vars:
            if v in goal_fixes:
                tmp[v] = None
            if v in self.ctx.fixes:
                del self.ctx.fixes[v]
        self.ctx.dead_vars.update(tmp)
        step.ctx.fixes = copy.deepcopy(self.ctx.fixes)
        step.ctx.dead_vars = copy.deepcopy(self.ctx.dead_vars)
        self.add_step(step)

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

    def parse_expr(self, s: str) -> Expr:
        return parser.parse_expr(s, fixes=self.ctx.get_fixes())


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
        elif expr.is_fun(goal) and goal.func_name == "converges":
            self.predicate = goal.func_name
            self.calcs.append(Calculation(self, self.ctx, self.goal.args[0]))
        else:
            raise AssertionError("CalculationProof: unknown form of goal.")
    def __eq__(self, other):
        if not isinstance(other, CalculationProof):
            return False
        return self.calcs == other.calcs and self.goal == other.goal

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
        assert expr.is_fun(self.goal)
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
            raise AssertionError("InductionProof: currently only support equation goals.")

        self.parent = parent
        self.goal = goal
        self.induct_var = induct_var
        self.ctx = parent.ctx

        if isinstance(start, int):
            self.start = Const(start, type=expr.IntType)
        elif isinstance(start, Expr):
            self.start = start
        else:
            raise NotImplementedError

        # Base case: n = start
        eq0 = normalize(goal.subst(induct_var, self.start), self.ctx)

        self.base_case = Goal(self, self.ctx, eq0)

        # Inductive case:
        eqI = normalize(goal.subst(induct_var, Var(induct_var, type=expr.IntType) + Const(1)), self.ctx)
        # induct_conds = Conditions([normalize(cond.subst(induct_var, Var(induct_var, type=expr.IntType) - Const(1)), self.ctx) for cond in parent.conds.data])

        self.ctx.add_induct_hyp(self.goal)
        self.induct_case = Goal(self, self.ctx, eqI)

    def __eq__(self, other):
        if not isinstance(other, InductionProof):
            return False
        return self.start == other.start and self.induct_case == other.induct_case and \
                self.base_case == other.base_case

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
            'start': str(self.start),
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

    def __eq__(self, other):
        if not isinstance(other, CaseProof):
            return False
        return self.goal == other.goal and self.split_type == other.split_type and \
                self.split_cond == other.split_cond and self.cases == other.cases

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
        file = begin
        while not isinstance(file, CompFile):
            file = file.parent
        self.begin_label = file.get_item_label(begin)
        ctx = file.get_context(len(file.content)-1)
        ctx.extend_fixes(begin.fixes)
        ctx.extend_condition(parent.conds)
        ctx.extend_condition(begin.conds)
        self.begin = Calculation(self, ctx, begin.goal, connection_symbol = '==>')

    def __eq__(self, other):
        if not isinstance(other, RewriteGoalProof):
            return False
        return self.goal == other.goal and self.begin_label == other.begin_label and \
                self.begin == other.begin

    def is_finished(self):
        f1 = normalize(self.begin.last_expr.lhs, self.ctx) == normalize(self.goal.lhs, self.ctx)
        f2 = normalize(self.begin.last_expr.rhs, self.ctx) == normalize(self.goal.rhs, self.ctx)
        return f1 and f2

    def export(self):
        res = {
            "type": "RewriteGoalProof",
            "goal": str(self.goal),
            "latex_goal": latex.convert_expr(self.goal),
            "start": self.begin.export(),
            "finished": self.is_finished(),
            "begin_label": str(self.begin_label)
        }
        return res


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

    def __eq__(self, other):
        return isinstance(other, CompFile) and \
            self.name == other.name and self.content == other.content

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
                ctx.add_definition(item.eq, item.conds)
                ctx.add_lemma(item.eq, item.conds)
            elif isinstance(item, Goal):
                ctx.add_lemma(item.goal, item.conds)
                ctx.extend_by_item(item.export_book())
        return ctx

    def add_definition(self, funcdef: Union[str, Expr], *,fixes=None, conds: List[Union[str, Expr]] = None, range_type:expr.Type=expr.RealType) -> FuncDef:
        """Add a function definition.
        
        funcdef: statement of the definition.
        conds: list of conditions for the definition. This is ignored if input
               is already of type FuncDef.
        
        """
        if fixes == None:
            fixes = dict()
        if conds is not None:
            for i in range(len(conds)):
                if isinstance(conds[i], str):
                    conds[i] = parser.parse_expr(conds[i], fixes = fixes)
        else:
            conds = []

        ctx = self.get_context()
        if isinstance(funcdef, str):
            funcdef = parser.parse_expr(funcdef, fixes = fixes)
        if isinstance(funcdef, Expr):
            if funcdef.is_equals():
                self.content.append(FuncDef(self, ctx, funcdef, Conditions(conds)))
                self.ctx.fixes[funcdef.lhs.func_name] = range_type
            else:
                raise NotImplementedError
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

    def add_goal(self, goal: Union[str, Expr, Goal], *,
                 fixes: Optional[List[Tuple[str, expr.Type]]] = None,
                 conds: Optional[List[Union[str, Expr]]] = None) -> Goal:
        """Add a goal.

        goal: statement of the goal.
        fixes: list of fixed variables
        conds: list of conditions for the goal. This is ignored if input goal
               is already of type Goal.

        """

        if isinstance(goal, Goal):
            self.content.append(goal)
            return self.content[-1]

        # Process fixes
        if fixes is None:
            fixes = dict()

        if conds is not None:
            for i in range(len(conds)):
                if isinstance(conds[i], str):
                    conds[i] = parser.parse_expr(conds[i], fixes=fixes)
        else:
            conds = []

        # Parse goal statement
        if isinstance(goal, str):
            goal = parser.parse_expr(goal, fixes=fixes)
        assert isinstance(goal, Expr)

        conds = Conditions(conds)
        ctx = self.get_context()
        self.content.append(Goal(self, ctx, goal, fixes=fixes, conds=conds))
        return self.content[-1]

    def add_item(self, item: StateItem):
        """Add item of arbitrary type"""
        self.content.append(item)

    def get_item_label(self, item: StateItem):
        res = None
        def rec(root:Union[CompFile, StateItem], loc:Label):
            nonlocal res, item
            if res != None:
                return
            if root == item:
                res = Label(loc)
            elif isinstance(root, CompFile):
                for idx, st in enumerate(self.content):
                    rec(st, loc.append(idx))
            elif isinstance(root, Goal):
                rec(root.proof, loc.append(0))
            elif isinstance(root, RewriteGoalProof):
                rec(root.begin, loc.append(0))
            elif isinstance(root, CalculationProof):
                rec(root.calcs[0], loc.append(0))
                rec(root.calcs[1], loc.append(1))
            elif isinstance(root, InductionProof):
                rec(root.base_case, loc.append(0))
                rec(root.induct_case, loc.append(1))
            elif isinstance(root, CaseProof):
                for i, c in enumerate(root.cases):
                    rec(c, loc.append(i))
            elif isinstance(root, FuncDef) or isinstance(root, CalculationStep):
                pass
            elif isinstance(root, Calculation):
                for i, step in enumerate(root.steps):
                    rec(root.steps[i], loc.append(i))
            else:
                print(type(root))
                raise NotImplementedError
        rec(self, Label(""))
        return res

    def get_by_label(self, label: Label):
        def rec(root:Union[CompFile, StateItem], loc:Label):
            if loc == Label(""):
                return root
            if isinstance(root, CompFile):
                return rec(root.content[loc.head], loc.tail)
            elif isinstance(root, Goal):
                return rec(root.proof, loc.tail)
            else:
                raise NotImplementedError
        return rec(self, label)
    def export(self):
        self.name = self.name
        return {
            "name": self.name,
            "content": [item.export() for item in self.content]
        }

def parse_rule(item, parent) -> Rule:
    ctx = parent.ctx
    fixes = ctx.get_fixes()
    if 'loc' in item:
        if item['loc'] == 'subterms':
            del item['loc']
            return rules.OnSubterm(parse_rule(item, parent))
        else:
            loc = item['loc']
            del item['loc']
            if loc == '' or loc == '.':
                return parse_rule(item, parent)
            else:
                return rules.OnLocation(parse_rule(item, parent), loc)
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
            a = parser.parse_expr(item['a'], fixes=fixes)
        return rules.ElimInfInterval(a)
    elif item['name'] == 'Substitution':
        var_name = item['var_name']
        var_subst = parser.parse_expr(item['var_subst'], fixes=fixes)
        return rules.Substitution(var_name, var_subst)
    elif item['name'] == 'SubstitutionInverse':
        var_name = item['var_name']
        var_subst = parser.parse_expr(item['var_subst'], fixes=fixes)
        return rules.SubstitutionInverse(var_name, var_subst)
    elif item['name'] == 'IntegrationByParts':
        u = parser.parse_expr(item['u'], fixes=fixes)
        v = parser.parse_expr(item['v'], fixes=fixes)
        return rules.IntegrationByParts(u, v)
    elif item['name'] == 'Equation':
        new_expr = parser.parse_expr(item['new_expr'], fixes=fixes)
        old_expr = parser.parse_expr(item['old_expr'], fixes=fixes) if ('old_expr' in item) else None
        return rules.Equation(old_expr, new_expr)
    elif item['name'] == 'ApplyEquation':
        eq_fixes = dict()
        if 'eq_fixes' in item:
            raw_fixes = item['eq_fixes']
            for s, t in raw_fixes:
                eq_fixes[s] = parser.parse_expr(t, fixes=eq_fixes)
        eq = parser.parse_expr(item['eq'], fixes=eq_fixes)
        source = parser.parse_expr(item['source'], fixes=fixes)
        return rules.ApplyEquation(eq, source)
    elif item['name'] == 'ExpandPolynomial':
        return rules.ExpandPolynomial()
    elif item['name'] == 'SplitRegion':
        c = parser.parse_expr(item['c'], fixes=fixes)
        return rules.SplitRegion(c)
    elif item['name'] == 'IntegrateByEquation':
        lhs = parser.parse_expr(item['lhs'], fixes=fixes)
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
        lim = parser.parse_expr(item['lim'], fixes=fixes)
        return rules.LimitEquation(var, lim)
    elif item['name'] == 'IntSumExchange':
        return rules.IntSumExchange()
    elif item['name'] == 'DerivEquation':
        var = item['var']
        return rules.DerivEquation(var)
    elif item['name'] == 'SolveEquation':
        solve_for = parser.parse_expr(item['solve_for'], fixes=fixes)
        return rules.SolveEquation(solve_for)
    elif item['name'] == 'VarSubsOfEquation':
        subst = item['subst']
        return rules.VarSubsOfEquation(subst)
    elif item['name'] == 'ApplyIdentity':
        source = parser.parse_expr(item['source'], fixes=fixes)
        target = parser.parse_expr(item['target'], fixes=fixes)
        return rules.ApplyIdentity(source, target)
    elif item['name'] == 'IndefiniteIntegralIdentity':
        return rules.IndefiniteIntegralIdentity()
    elif item['name'] == 'DefiniteIntegralIdentity':
        return rules.DefiniteIntegralIdentity()
    elif item['name'] == 'SeriesExpansionIdentity':
        index_var = item['index_var']
        old_expr = None
        if 'old_expr' in item:
            old_expr = parser.parse_expr(item['old_expr'], fixes=fixes)
        return rules.SeriesExpansionIdentity(old_expr=old_expr, index_var=index_var)
    elif item['name'] == 'SeriesEvaluationIdentity':
        return rules.SeriesEvaluationIdentity()
    elif item['name'] == 'ReplaceSubstitution':
        return rules.ReplaceSubstitution()
    elif item['name'] == 'ChangeSummationIndex':
        e = parser.parse_expr(item['new_lower'], fixes=fixes)
        return rules.ChangeSummationIndex(e)
    elif item['name'] == 'SummationEquation':
        idx_v = item['index_var']
        lower = parser.parse_expr(item['lower'], fixes=fixes)
        upper = parser.parse_expr(item['upper'], fixes=fixes)
        return rules.SummationEquation(idx_v, lower, upper)
    elif item['name'] == 'FunEquation':
        func_name = item['func_name']
        return rules.FunEquation(func_name)
    elif item['name'] == 'PartialFractionDecomposition':
        return rules.PartialFractionDecomposition()
    elif item['name'] == "ExpandMatFunc":
        return rules.ExpandMatFunc()
    elif item['name'] == 'SplitSummation':
        ctx = parent.ctx
        cond = parser.parse_expr(item['cond'], fixes=ctx.get_fixes())
        return rules.SplitSummation(cond)
    else:
        print(item['name'], flush=True)
        raise NotImplementedError

def parse_step(parent: Calculation, item, id: int) -> CalculationStep:
    if item['type'] != 'CalculationStep':
        raise AssertionError('parse_step')
    all_fixes = parent.ctx.get_fixes()
    step_fixes = dict()
    for k, v in item['fixes']:
        all_fixes[k] = parser.parse_expr(v, fixes = all_fixes)
        step_fixes[k] = parser.parse_expr(v, fixes=all_fixes)
    step_dead_vars = dict([[k, None] for k in item['dead_vars']])
    parent.ctx.fixes = step_fixes
    parent.ctx.dead_vars = step_dead_vars
    rule = parse_rule(item['rule'], parent)
    res = parent.parse_expr(item['res'])
    step = CalculationStep(parent, rule, res, id)
    step.ctx.fixes = copy.deepcopy(step_fixes)
    step.ctx.dead_vars = copy.deepcopy(step_dead_vars)

    return step

def parse_conds(item, fixes=None) -> Conditions:
    if fixes is None:
        fixes = dict()
    res = Conditions()
    if 'conds' in item:
        for subitem in item['conds']:
            res.add_condition(parser.parse_expr(subitem['cond'], fixes = fixes))
    return res

def parse_item(parent, item, begin_ctx = None) -> StateItem:
    if item['type'] == 'FuncDef':
        conds = parse_conds(item)
        eq = parser.parse_expr(item['eq'])
        ctx = parent.get_context() if isinstance(parent, CompFile) else parent.ctx
        return FuncDef(parent, ctx, eq, conds=conds)
    elif item['type'] == 'Goal':
        ctx = parent.get_context() if isinstance(parent, CompFile) else parent.ctx
        fixes = dict()
        all_fixes = ctx.get_fixes()
        fixes = dict()
        if 'fixes' in item:
            for s, t in item['fixes']:
                all_fixes[s] = parser.parse_expr(t, fixes=all_fixes)
                fixes[s] = parser.parse_expr(t, fixes=all_fixes)
        goal = parser.parse_expr(item['goal'], fixes=all_fixes)
        conds = parse_conds(item, fixes=all_fixes)
        res = Goal(parent, ctx, goal, conds=conds, fixes=fixes)
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
                            tmp.append(parser.parse_expr(e, fixes=fixes))
                        branches.append(rules.ProofObligationBranch(tmp))
                    c = parse_conds(obligation, fixes = fixes)
                    res.proof_obligations.append(rules.ProofObligation(branches, c))
        return res
    elif item['type'] == 'CalculationProof':
        fixes = parent.ctx.get_fixes()
        goal = parser.parse_expr(item['goal'], fixes=fixes)
        res = CalculationProof(parent, goal)
        for i, calc_item in enumerate(item['calcs']):
            res.calcs[i] = parse_item(res, calc_item)
        return res
    elif item['type'] == 'Calculation':
        ctx = parent.get_context() if isinstance(parent, CompFile) else parent.ctx
        if begin_ctx != None:
            ctx = begin_ctx
        fixes = ctx.get_fixes()
        start = parser.parse_expr(item['start'], fixes=fixes)
        conds = parse_conds(item, fixes=fixes)
        res = Calculation(parent, ctx, start, conds=conds)
        for i, step in enumerate(item['steps']):
            res.add_step(parse_step(res, step, i))
        res_fixes = dict()
        for k,v in item['fixes']:
            fixes[k] = parser.parse_expr(v, fixes = fixes)
            res_fixes[k]  = parser.parse_expr(v, fixes = fixes)
        res.ctx.fixes = res_fixes
        res.ctx.dead_vars = dict([[a, None] for a in item['dead_vars']])
        return res
    elif item['type'] == 'InductionProof':
        ctx = parent.ctx
        fixes = ctx.get_fixes()
        goal = parser.parse_expr(item['goal'], fixes=fixes)
        induct_var = item['induct_var']
        res = InductionProof(parent, goal, induct_var)
        res.base_case = parse_item(res, item['base_case'])
        res.induct_case.ctx.add_induct_hyp(goal)
        res.start = parser.parse_expr(item['start'])
        res.induct_case = parse_item(res, item['induct_case'])
        return res
    elif item['type'] == 'CaseProof':
        ctx = parent.ctx
        fixes = ctx.get_fixes()
        goal = parser.parse_expr(item['goal'], fixes=fixes)
        split_cond = parser.parse_expr(item['split_cond'], fixes=fixes)
        res = CaseProof(parent, goal, split_cond=split_cond)
        assert len(res.cases) == len(item['cases'])
        for i, case in enumerate(item['cases']):
            res.cases[i] = parse_item(res, case)
        return res
    elif item['type'] == 'RewriteGoalProof':
        fixes = parent.ctx.get_fixes()
        goal = parser.parse_expr(item['goal'], fixes=fixes)
        p = parent
        while not isinstance(p, CompFile):
            p = p.parent
        label = Label(item['begin_label'])
        begin_goal = p.get_by_label(label)
        res = RewriteGoalProof(parent, goal, begin=begin_goal)
        begin_ctx = p.get_context(len(p.content)-1)
        begin_ctx.extend_fixes(begin_goal.fixes)
        begin_ctx.extend_condition(parent.conds)
        begin_ctx.extend_condition(begin_goal.conds)
        res.begin = parse_item(begin_goal, item['start'], begin_ctx = begin_goal.ctx)
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
