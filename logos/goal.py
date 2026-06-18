from __future__ import annotations
from dataclasses import dataclass
from logos.expr import Expr


@dataclass
class Goal:
    context: dict[str, Expr]
    statement: Expr

    def with_hyp(self, name: str, hyp: Expr) -> "Goal":
        return Goal({**self.context, name: hyp}, self.statement)

    def with_statement(self, stmt: Expr) -> "Goal":
        return Goal(dict(self.context), stmt)
