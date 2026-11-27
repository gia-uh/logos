"""Finite integer sequences as a core Logos sort.

A sequence value is immutable. ``length(xs)`` is its number of elements and
``nth(xs, i)`` is the integer at index ``i``. Reads are total in the logic;
the program certificate must prove every read that the executable evaluates is
inside ``[0, length(xs))``.
"""
from __future__ import annotations

from logos.expr import Expr, ExistsNode, ForallNode, Len, Lit, Nth, Sorted, Var


class SeqType:
    """The sort of finite integer sequences."""

    def __repr__(self) -> str:
        return "seq"


Seq = SeqType()


def seq_var(name: str) -> Var:
    return Var(name, Seq)


def length(xs: Expr) -> Len:
    return Len(xs)


def nth(xs: Expr, index) -> Nth:
    return Nth(xs, index if isinstance(index, Expr) else Lit(index))


def sorted(xs: Expr) -> Sorted:
    """The checker-owned sortedness predicate over a sequence."""
    return Sorted(xs)


def in_bounds(xs: Expr, index: Expr) -> Expr:
    return (Lit(0) <= index) & (index < length(xs))


def absent(xs: Expr, target: Expr) -> Expr:
    """Every in-range index holds something other than ``target``."""
    i = Var("i", int)
    body = (Lit(0) <= i) >> ((i < length(xs)) >> ~(nth(xs, i) == target))
    return ForallNode(i, body)


def occurrence(xs: Expr, target: Expr) -> Expr:
    """Some in-range index holds ``target``."""
    i = Var("i", int)
    body = (Lit(0) <= i) & (i < length(xs)) & (nth(xs, i) == target)
    return ExistsNode(i, body)
