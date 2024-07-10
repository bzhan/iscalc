"""Definition of internal language for actions."""


from integral.expr import Expr
from integral.rules import Rule
from integral.context import Context
from integral.compstate import CompFile, CalculationStep, Calculation
from integral import poly

class Action:
    """Base class for actions."""
    pass


class CalculateAction(Action):
    """Start a calculation."""
    def __init__(self, expr: Expr):
        self.expr = expr

    def __str__(self):
        return "calculate %s" % self.expr
    

class RuleAction(Action):
    """Apply rule."""
    def __init__(self, rule: Rule):
        self.rule = rule

    def __str__(self):
        return str(self.rule)
    

"""State machine for processing the actions."""


class StateException(Exception):
    """Exception resulting from applying action to a state."""
    def __init__(self, msg: str):
        self.msg = msg

    def __str__(self):
        return self.msg


class State:
    """Base class for states."""
    def process_action(self, action: Action) -> "State":
        """Apply the given action, return new state."""
        pass

    def is_finished(self) -> bool:
        """Determine whether the given state is in finished form."""
        pass


class InitialState(State):
    """Initial state."""
    def __init__(self, ctx: Context):
        self.ctx = ctx

    def process_action(self, action: Action) -> State:
        if isinstance(action, CalculateAction):
            calc = Calculation(None, self.ctx, action.expr)
            return CalculateState(self.ctx, calc)
        elif isinstance(action, RuleAction):
            raise StateException("Cannot apply rule when at initial state.")
        else:
            raise StateException("Unknown action type %s" % type(action))
        
    def is_finished(self) -> bool:
        return False

    def __str__(self) -> Expr:
        return "(initial)"

class CalculateState(State):
    """State when performing a calculation."""
    def __init__(self, ctx: Context, calc: Calculation):
        self.ctx = ctx
        self.calc = calc

    def process_action(self, action: Action) -> State:
        if isinstance(action, CalculateAction):
            raise StateException("Cannot start a new calculation within a calculation.")
        elif isinstance(action, RuleAction):
            self.calc.perform_rule(action.rule)
            return self
        else:
            raise StateException("Unknown action type %s" % type(action))

    def is_finished(self) -> bool:
        if not self.calc.steps:
            return False

        res = self.calc.steps[-1].res
        return res.is_evaluable() and poly.normalize(res, self.ctx) == res

    def __str__(self) -> Expr:
        return "(calculate)\n%s" % self.calc
