"""Core strict-order laws over integers.

The checker owns these four laws, so a proof that cites one needs no custom
axiom. Each law is universally quantified over integer terms:

``lt_irrefl``  ``a < a`` is false.
``lt_trans``  ``a < b`` and ``b < c`` imply ``a < c``.
``lt_add``    ``a < b`` implies ``a + c < b + c``.
``lt_neq``    ``a < b`` implies ``a != b``.

This module only describes the schemas for tactics and tests. The Rust
checker recomputes every instance from the law ID and its integer arguments.
"""
from __future__ import annotations

from logos.expr import Add, Eq, Expr, Implies, Lt, Not

_LAWS = {
    "lt_irrefl": 1,
    "lt_trans": 3,
    "lt_add": 3,
    "lt_neq": 2,
}

ORDER_LAWS = tuple(_LAWS)


def order_law(law: str, args: tuple[Expr, ...]) -> Expr:
    """Return the full proposition asserted by ``law`` at ``args``."""
    if law not in _LAWS:
        raise ValueError(f"unknown order law {law!r}; expected one of {ORDER_LAWS}")
    if len(args) != _LAWS[law]:
        raise ValueError(
            f"order law {law!r} takes {_LAWS[law]} integer arguments, got {len(args)}"
        )
    if law == "lt_irrefl":
        (a,) = args
        return Not(Lt(a, a))
    if law == "lt_trans":
        a, b, c = args
        return Implies(Lt(a, b), Implies(Lt(b, c), Lt(a, c)))
    if law == "lt_add":
        a, b, c = args
        return Implies(Lt(a, b), Lt(Add(a, c), Add(b, c)))
    a, b = args
    return Implies(Lt(a, b), Not(Eq(a, b)))


def split_implications(expr: Expr) -> tuple[list[Expr], Expr]:
    """Return the antecedents and the consequent of an implication chain."""
    premises = []
    while isinstance(expr, Implies):
        premises.append(expr.antecedent)
        expr = expr.consequent
    return premises, expr
