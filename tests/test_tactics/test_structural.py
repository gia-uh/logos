# tests/test_tactics/test_structural.py
import pytest
from logos.expr import Var, Lit, And, Or, Implies, Forall, Exists, ExistsNode
from logos.goal import Goal
from logos.kernel import (
    infer, Context, Refl, HypRef, AndIntro,
    ForallIntro, ImpliesIntro,
)
from logos.helpers import structural_eq
from logos.runner import run, TacticFailed
from logos.registry import register_axiom, clear_axioms
from logos.tactics.structural import intro, assumption, exact, split, left, right, witness


def test_intro_forall(x, y):
    goal = Goal({}, Forall(x, x == x))
    proof = run(goal, [intro("x"), exact(Refl(Var("x", int)))])
    stmt = infer(proof, Context({}, {}))
    assert structural_eq(stmt, Forall(x, x == x))


def test_intro_implies(x):
    hyp = x > Lit(0)
    goal = Goal({}, hyp >> hyp)
    proof = run(goal, [intro("h"), assumption()])
    stmt = infer(proof, Context({}, {}))
    assert structural_eq(stmt, hyp >> hyp)


def test_assumption(x):
    hyp = x > Lit(0)
    goal = Goal({"h": hyp}, hyp)
    proof = run(goal, [assumption()])
    stmt = infer(proof, Context({}, {"h": hyp}))
    assert structural_eq(stmt, hyp)


def test_split(x, y):
    goal = Goal({"hx": x > Lit(0), "hy": y > Lit(0)},
                (x > Lit(0)) & (y > Lit(0)))
    proof = run(goal, [split(), [assumption()], [assumption()]])
    ctx = Context({}, {"hx": x > Lit(0), "hy": y > Lit(0)})
    stmt = infer(proof, ctx)
    assert structural_eq(stmt, (x > Lit(0)) & (y > Lit(0)))


def test_left(x):
    goal = Goal({"h": x > Lit(0)}, (x > Lit(0)) | (x < Lit(0)))
    proof = run(goal, [left(x < Lit(0)), assumption()])
    ctx = Context({}, {"h": x > Lit(0)})
    stmt = infer(proof, ctx)
    assert structural_eq(stmt, (x > Lit(0)) | (x < Lit(0)))


def test_witness(x):
    x_val = Var("x", int)
    goal = Goal({"h": Lit(5) > Lit(0)}, Exists(x_val, x_val > Lit(0)))
    proof = run(goal, [witness(Lit(5)), assumption()])
    ctx = Context({}, {"h": Lit(5) > Lit(0)})
    stmt = infer(proof, ctx)
    # should prove Exists(x, x > 0)
    assert isinstance(stmt, ExistsNode)


def test_exact(x):
    goal = Goal({}, x == x)
    proof = run(goal, [exact(Refl(x))])
    stmt = infer(proof, Context({}, {}))
    assert structural_eq(stmt, x == x)


def test_assumption_not_found(x):
    hyp = x > Lit(0)
    goal = Goal({}, hyp)
    with pytest.raises(TacticFailed, match="assumption"):
        run(goal, [assumption()])


def test_intro_fails_on_non_quantifier(x):
    goal = Goal({}, x == x)
    with pytest.raises(TacticFailed, match="intro"):
        run(goal, [intro("h")])


def test_split_fails_on_non_and(x):
    goal = Goal({}, x == x)
    with pytest.raises(TacticFailed, match="split"):
        run(goal, [split()])


def test_intro_multi(x, y):
    """intro can peel off multiple Forall layers in one call."""
    goal = Goal({}, Forall(x, Forall(y, x == x)))
    proof = run(goal, [intro("x", "y"), exact(Refl(Var("x", int)))])
    stmt = infer(proof, Context({}, {}))
    assert structural_eq(stmt, Forall(x, Forall(y, x == x)))
