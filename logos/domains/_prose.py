"""Render propositional expressions with vocabulary supplied by a domain."""
from collections.abc import Callable

from logos.expr import And, Expr, Implies, Lit, Not, Or


def sentence(expr: Expr, phrase: Callable[[Expr], str | None]) -> str:
    """Compose a sentence, letting the domain supply atoms and exact idioms."""
    def scoped(child: Expr) -> str:
        text = clause(child)
        return f"({text})" if isinstance(child, (And, Or, Not, Implies)) else text

    def clause(node: Expr) -> str:
        custom = phrase(node)
        if custom is not None:
            return custom
        match node:
            case Lit(value) if value is False:
                return "a contradiction holds"
            case Not(operand):
                return f"it is false that {scoped(operand)}"
            case And(left, right):
                return f"{scoped(left)} and {scoped(right)}"
            case Or(left, right):
                return f"{scoped(left)} or {scoped(right)} (or both)"
            case Implies(left, right):
                return f"if {scoped(left)}, then {scoped(right)}"
        raise ValueError(f"no English rendering for {type(node).__name__}")

    text = clause(expr)
    return text[0].upper() + text[1:] + "."
