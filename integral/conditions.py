"""Conditions"""

from typing import List, Union

from integral.expr import Expr
from integral import latex
from integral import parser


class Conditions:
    """A condition is represented by a list of boolean expressions."""
    def __init__(self, conds: Union["Conditions", List[Union[str, Expr]]] = None):
        self.data: List[Expr] = list()
        if isinstance(conds, Conditions):
            self.data.extend(conds.data)
        elif conds is not None:
            for cond in conds:
                if isinstance(cond, str):
                    self.data.append(parser.parse_expr(cond))
                elif isinstance(cond, Expr):
                    self.data.append(cond)
                else:
                    raise TypeError

    def __hash__(self):
        return hash(tuple(self.data))

    def __str__(self):
        return ", ".join(str(cond) for cond in self.data)

    def add_condition(self, cond: Expr):
        assert isinstance(cond, Expr)
        self.data.append(cond)

    def __eq__(self, other):
        return isinstance(other, Conditions) and self.data == other.data

    def export(self):
        res = list()
        for cond in self.data:
            res.append({
                "cond": str(cond),
                "latex_cond": latex.convert_expr(cond)
            })
        return res
