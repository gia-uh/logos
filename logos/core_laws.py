"""Schemas for the checker-owned core laws beyond polynomial equality.

The Rust checker owns every schema here and recomputes the conclusion from the
law ID and its typed arguments. This module only lets tactics build the exact
same expressions and lets tests state them explicitly.
"""
from __future__ import annotations

from logos.expr import (
    Add, And, Div, Eq, Expr, ForallNode, Implies, Le, Len, Lit, Lt, Neg, Not,
    Nth, Or, Sorted, Var,
)

_INT = "int"
_SEQ = "seq"


def _eq(a, b): return Eq(a, b)
def _le(a, b): return Le(a, b)
def _lt(a, b): return Lt(a, b)
def _not(a): return Not(a)
def _and(a, b): return And(a, b)
def _or(a, b): return Or(a, b)
def _imp(a, b): return Implies(a, b)
def _add(a, b): return Add(a, b)
def _mul(a, b): return Mul(a, b)
def _neg(a): return Neg(a)
def _len(a): return Len(a)
def _nth(a, i): return Nth(a, i)
def _sorted(a): return Sorted(a)
def _div(a, b): return Div(a, b)
def _int(n): return Lit(n)
def _half(a, b): return Div(Add(a, b), Lit(2))


def _i(name="_i"):
    return Var(name, int)


def _forall_i(body: Expr) -> Expr:
    return ForallNode(_i(), body)


def _sorted_elim(xs, i, j):
    return _imp(
        _sorted(xs),
        _imp(
            _le(_int(0), i),
            _imp(
                _le(i, j),
                _imp(_lt(j, _len(xs)), _le(_nth(xs, i), _nth(xs, j))),
            ),
        ),
    )


def _sorted_lower(xs, i, mid, target):
    return _imp(
        _sorted(xs),
        _imp(
            _le(_int(0), i),
            _imp(
                _le(i, mid),
                _imp(
                    _lt(mid, _len(xs)),
                    _imp(_lt(_nth(xs, mid), target), _lt(_nth(xs, i), target)),
                ),
            ),
        ),
    )


def _sorted_upper(xs, mid, i, target):
    return _imp(
        _sorted(xs),
        _imp(
            _le(_int(0), mid),
            _imp(
                _le(mid, i),
                _imp(
                    _lt(i, _len(xs)),
                    _imp(_lt(target, _nth(xs, mid)), _lt(target, _nth(xs, i))),
                ),
            ),
        ),
    )


def _sorted_gap(xs, low, high, target):
    # Fresh inner names keep Python-name substitution from capturing the
    # caller's index variable; the checker sees only de Bruijn indices.
    index = Var("_seq_gap_i", int)
    lower = ForallNode(
        index,
        Implies(
            Le(Lit(0), index),
            Implies(
                Lt(index, low),
                Lt(Nth(xs, index), target),
            ),
        ),
    )
    upper = ForallNode(
        index,
        Implies(
            Le(high, index),
            Implies(
                Lt(index, Len(xs)),
                Lt(target, Nth(xs, index)),
            ),
        ),
    )
    absent = ForallNode(
        index,
        Implies(
            Le(Lit(0), index),
            Implies(
                Lt(index, Len(xs)),
                Not(Eq(Nth(xs, index), target)),
            ),
        ),
    )
    return Implies(
        Sorted(xs),
        Implies(
            Le(Lit(0), low),
            Implies(
                Le(low, high),
                Implies(
                    Le(high, Len(xs)),
                    Implies(
                        lower,
                        Implies(upper, Implies(Le(high, low), absent)),
                    ),
                ),
            ),
        ),
    )


# id -> (argument sorts, builder)
LAWS = {
    "lt_irrefl": ((_INT,), lambda a: _not(_lt(a, a))),
    "lt_trans": ((_INT, _INT, _INT), lambda a, b, c: _imp(_lt(a, b), _imp(_lt(b, c), _lt(a, c)))),
    "lt_add": ((_INT, _INT, _INT), lambda a, b, c: _imp(_lt(a, b), _lt(_add(a, c), _add(b, c)))),
    "lt_neq": ((_INT, _INT), lambda a, b: _imp(_lt(a, b), _not(_eq(a, b)))),
    "le_refl": ((_INT,), lambda a: _le(a, a)),
    "le_trans": ((_INT, _INT, _INT), lambda a, b, c: _imp(_le(a, b), _imp(_le(b, c), _le(a, c)))),
    "le_antisymm": ((_INT, _INT), lambda a, b: _imp(_le(a, b), _imp(_le(b, a), _eq(a, b)))),
    "le_lt_trans": ((_INT, _INT, _INT), lambda a, b, c: _imp(_le(a, b), _imp(_lt(b, c), _lt(a, c)))),
    "lt_le_trans": ((_INT, _INT, _INT), lambda a, b, c: _imp(_lt(a, b), _imp(_le(b, c), _lt(a, c)))),
    "le_total": ((_INT, _INT), lambda a, b: _or(_le(a, b), _le(b, a))),
    "lt_trichotomy": ((_INT, _INT), lambda a, b: _or(_lt(a, b), _or(_eq(a, b), _lt(b, a)))),
    "lt_to_le": ((_INT, _INT), lambda a, b: _imp(_lt(a, b), _le(a, b))),
    "lt_succ_le": ((_INT, _INT), lambda a, b: _imp(_lt(a, b), _le(_add(a, _int(1)), b))),
    "lt_add_one_le": ((_INT, _INT), lambda a, b: _imp(_lt(a, _add(b, _int(1))), _le(a, b))),
    "le_add": ((_INT, _INT, _INT), lambda a, b, c: _imp(_le(a, b), _le(_add(a, c), _add(b, c)))),
    "not_lt_le": ((_INT, _INT), lambda a, b: _imp(_not(_lt(a, b)), _le(b, a))),
    "eq_symm": ((_INT, _INT), lambda a, b: _imp(_eq(a, b), _eq(b, a))),
    "half_lower": ((_INT, _INT), lambda a, b: _imp(_le(_int(0), a), _imp(_lt(a, b), _le(a, _half(a, b))))),
    "half_upper": ((_INT, _INT), lambda a, b: _imp(_le(_int(0), a), _imp(_lt(a, b), _lt(_half(a, b), b)))),
    "length_nonneg": ((_SEQ,), lambda xs: _le(_int(0), _len(xs))),
    "sorted_elim": ((_SEQ, _INT, _INT), _sorted_elim),
    "sorted_lower": ((_SEQ, _INT, _INT, _INT), _sorted_lower),
    "sorted_upper": ((_SEQ, _INT, _INT, _INT), _sorted_upper),
    "sorted_gap": ((_SEQ, _INT, _INT, _INT), _sorted_gap),
}

ORDER_LAWS = tuple(LAWS)


def law_sorts(law: str) -> tuple[str, ...]:
    if law not in LAWS:
        raise ValueError(f"unknown core law {law!r}; expected one of {ORDER_LAWS}")
    return LAWS[law][0]


def law_statement(law: str, args: tuple[Expr, ...]) -> Expr:
    if law not in LAWS:
        raise ValueError(f"unknown core law {law!r}; expected one of {ORDER_LAWS}")
    sorts, build = LAWS[law]
    if len(args) != len(sorts):
        raise ValueError(f"core law {law!r} takes {len(sorts)} arguments, got {len(args)}")
    return build(*args)
