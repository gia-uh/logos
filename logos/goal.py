from __future__ import annotations
from dataclasses import dataclass
from logos.expr import Expr
from logos.kernel import Context
from logos.registry import get_all_axioms


@dataclass
class Goal:
    context: dict[str, Expr]
    statement: Expr

    def with_hyp(self, name: str, hyp: Expr) -> "Goal":
        return Goal({**self.context, name: hyp}, self.statement)

    def with_statement(self, stmt: Expr) -> "Goal":
        return Goal(dict(self.context), stmt)

    def make_context(self) -> Context:
        return Context(axioms=get_all_axioms(), hyps=dict(self.context))
