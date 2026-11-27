"""Core integer order and positivity laws.

The checker owns these laws, so a proof that cites one needs no custom
axiom. Each law is universally quantified over integer terms:

``lt_irrefl``  ``a < a`` is false.
``lt_trans``  ``a < b`` and ``b < c`` imply ``a < c``.
``lt_add``    ``a < b`` implies ``a + c < b + c``.
``lt_neq``    ``a < b`` implies ``a != b``.
``mul_pos``   ``0 < a`` and ``0 < b`` imply ``0 < a * b``.
``mul_eq_one``  ``a * b = 1`` implies ``a = 1`` or ``a = -1``.
``lt_succ_fwd``  ``a < b + 1`` implies ``not (b < a)``.
``lt_succ_rev``  ``not (b < a)`` implies ``a < b + 1``.
``eq_of_not_lt_not_lt``  ``not (a < b)`` and ``not (b < a)`` imply ``a = b``.
``lt_decidable``  ``a < b`` or ``not (a < b)``.

This module only describes the schemas for tactics and tests. The Rust
checker recomputes every instance from the law ID and its integer arguments.
"""
from __future__ import annotations

from logos.expr import Add, Eq, Expr, Implies, Lit, Lt, Not, Or

_LAWS = {
    "lt_irrefl": 1,
    "lt_trans": 3,
    "lt_add": 3,
    "lt_neq": 2,
    "mul_pos": 2,
    "mul_eq_one": 2,
    "lt_succ_fwd": 2,
    "lt_succ_rev": 2,
    "eq_of_not_lt_not_lt": 2,
    "lt_decidable": 2,
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
    if law == "lt_neq":
        a, b = args
        return Implies(Lt(a, b), Not(Eq(a, b)))
    if law == "mul_pos":
        a, b = args
        return Implies(Lt(Lit(0), a), Implies(Lt(Lit(0), b), Lt(Lit(0), a * b)))
    if law == "mul_eq_one":
        a, b = args
        return Implies(Eq(a * b, Lit(1)), Or(Eq(a, Lit(1)), Eq(a, Lit(-1))))
    if law == "lt_succ_fwd":
        a, b = args
        return Implies(Lt(a, b + 1), Not(Lt(b, a)))
    if law == "lt_succ_rev":
        a, b = args
        return Implies(Not(Lt(b, a)), Lt(a, b + 1))
    if law == "eq_of_not_lt_not_lt":
        a, b = args
        return Implies(Not(Lt(a, b)), Implies(Not(Lt(b, a)), Eq(a, b)))
    a, b = args
    return Or(Lt(a, b), Not(Lt(a, b)))


def split_implications(expr: Expr) -> tuple[list[Expr], Expr]:
    """Return the antecedents and the consequent of an implication chain."""
    premises = []
    while isinstance(expr, Implies):
        premises.append(expr.antecedent)
        expr = expr.consequent
    return premises, expr
