"""Authoring diagnostics spell inequalities the way the book writes them."""
from __future__ import annotations

from logos import Int, exists
from logos.authoring import format_expr
from logos.expr import Add, Lit, Lt, Mul, Var


def test_a_strict_inequality_with_a_product():
    k = Var("k", int)
    assert format_expr(Lt(Lit(0), Mul(Add(k, Lit(1)), Lit(2)))) == "0 < (k + 1) * 2"


def test_a_conjunction_nests_an_existential():
    d = Var("d", int)
    body = Lt(Lit(1), d) & exists(Int, lambda j: d == j + j)
    assert format_expr(body) == "1 < d & exists j:Int. d = j + j"
