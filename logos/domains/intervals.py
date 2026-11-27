"""A checked theory of closed integer intervals.

``contains(lo, hi, x)`` and ``overlaps(a_lo, a_hi, b_lo, b_hi)`` are transparent
definitions, so the checker may unfold them during conversion. The lemmas are
ordinary Logos theorems: their proofs use the authoring tactics and the Rust
checker rechecks the exported evidence. ``interval`` is a goal-level tactic that
unfolds an overlap goal and builds a checked linear certificate from the order
facts in the local context.

The module is the worked extension in the English Developer Guide. It assumes
only the existing integer fragment; it adds no core law and no proof-format tag.
"""
from __future__ import annotations

from fractions import Fraction

import logos
from logos import Int
from logos.authoring import format_expr, unfold
from logos.expr import And, Eq, Le, Lt
from logos.goal import Goal
from logos.kernel import AndElimL, AndElimR, AndIntro, Have, HypRef, Linear
from logos.proofs import farkas
from logos.runner import TacticFailed

# --8<-- [start:contains]
@logos.definition
def contains(lo: Int, hi: Int, x: Int):
    """The closed interval [lo, hi] contains x."""
    return (lo <= x) & (x <= hi)
# --8<-- [end:contains]


# --8<-- [start:overlaps]
@logos.definition
def overlaps(a_lo: Int, a_hi: Int, b_lo: Int, b_hi: Int):
    """The closed intervals [a_lo, a_hi] and [b_lo, b_hi] share a point."""
    return (a_lo <= b_hi) & (b_lo <= a_hi)
# --8<-- [end:overlaps]


# --8<-- [start:tactic]
def _fraction_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _orders(expression, proof, name):
    """Yield the order conjuncts of a fact, with evidence for each one."""
    expression = unfold(expression)
    if isinstance(expression, And):
        yield from _orders(expression.left, AndElimL(proof), name + "l")
        yield from _orders(expression.right, AndElimR(proof), name + "r")
    elif isinstance(expression, (Le, Lt, Eq)):
        yield name, expression, proof


def interval(goal: Goal):
    """Close an overlap goal with a checked linear certificate.

    The tactic unfolds the goal, flattens every order conjunct in the local
    context, and asks the exact Farkas routine for each side of the overlap.
    A side it cannot derive raises ``TacticFailed`` with that side in the
    message; it never returns unchecked evidence.
    """
    statement = unfold(goal.statement)
    if not isinstance(statement, And):
        raise TacticFailed(
            f"interval: expected an overlap after unfolding, got {format_expr(statement)}"
        )
    facts = []
    for index, (binder, proposition) in enumerate(goal.context.items()):
        facts.extend(_orders(proposition, HypRef(binder), f"__interval_{index}"))

    def close(side):
        labels = farkas(unfold(side), [(name, expression) for name, expression, _ in facts])
        if labels is None:
            raise TacticFailed(f"interval: no linear certificate for {format_expr(side)}")
        proof = Linear(
            side,
            tuple((name, _fraction_text(value)) for name, value in labels.items()),
        )
        for name, expression, subproof in reversed(facts):
            proof = Have(name, expression, subproof, proof)
        return proof

    return AndIntro(close(statement.left), close(statement.right))
# --8<-- [end:tactic]


# --8<-- [start:overlap_self]
@logos.theorem
def overlap_self(lo: Int, hi: Int):
    """A nonempty interval overlaps itself."""
    return (lo <= hi) >> overlaps(lo, hi, lo, hi)

@overlap_self.proof
def prove_overlap_self(p, lo, hi):
    """Both sides of the overlap are the same non-strict bound."""
    nonempty = p.assume(lo <= hi)
    return p.and_intro(nonempty, nonempty)
# --8<-- [end:overlap_self]


# --8<-- [start:overlap_comm]
@logos.theorem
def overlap_comm(a_lo: Int, a_hi: Int, b_lo: Int, b_hi: Int):
    """Overlap is symmetric."""
    return overlaps(a_lo, a_hi, b_lo, b_hi) >> overlaps(b_lo, b_hi, a_lo, a_hi)

@overlap_comm.proof
def prove_overlap_comm(p, a_lo, a_hi, b_lo, b_hi):
    """Swap the two conjuncts."""
    shared = p.assume(overlaps(a_lo, a_hi, b_lo, b_hi))
    return p.and_intro(shared.right(), shared.left())
# --8<-- [end:overlap_comm]


# --8<-- [start:common_point]
@logos.theorem
def common_point_overlaps(a_lo: Int, a_hi: Int, b_lo: Int, b_hi: Int, x: Int):
    """A point contained in both intervals witnesses an overlap."""
    return (contains(a_lo, a_hi, x) & contains(b_lo, b_hi, x)) >> overlaps(
        a_lo, a_hi, b_lo, b_hi
    )

@common_point_overlaps.proof
def prove_common_point_overlaps(p, a_lo, a_hi, b_lo, b_hi, x):
    """Chain the two containment bounds through x."""
    both = p.assume(contains(a_lo, a_hi, x) & contains(b_lo, b_hi, x))
    left, right = both.left(), both.right()
    first = p.linear(a_lo <= b_hi, using=[left.left(), right.right()])
    second = p.linear(b_lo <= a_hi, using=[right.left(), left.right()])
    return p.and_intro(first, second)
# --8<-- [end:common_point]


# --8<-- [start:disjoint]
@logos.theorem
def disjoint_no_common_point(a_lo: Int, a_hi: Int, b_lo: Int, b_hi: Int, x: Int):
    """An interval entirely to the left shares no point with one to its right."""
    return (a_hi < b_lo) >> (contains(a_lo, a_hi, x) >> ~contains(b_lo, b_hi, x))

@disjoint_no_common_point.proof
def prove_disjoint_no_common_point(p, a_lo, a_hi, b_lo, b_hi, x):
    """A common point would force a_hi < b_lo <= x <= a_hi."""
    before = p.assume(a_hi < b_lo)
    inside_left = p.assume(contains(a_lo, a_hi, x))
    with p.negate() as suppose:
        inside_right = suppose.assumption
        suppose.finish(p.linear(
            False,
            using=[before, inside_left.right(), inside_right.left()],
        ))
    return suppose.result
# --8<-- [end:disjoint]


THEOREMS = (
    overlap_self,
    overlap_comm,
    common_point_overlaps,
    disjoint_no_common_point,
)


# --8<-- [start:check_all]
def check_all():
    """Check every lemma with the installed Rust verifier."""
    for theorem in THEOREMS:
        logos.check(theorem)
    return THEOREMS
# --8<-- [end:check_all]
