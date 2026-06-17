# tests/test_tactics/test_combinators.py
import pytest
from logos.expr import Var, Lit, And
from logos.goal import Goal
from logos.kernel import Refl, infer, Context
from logos.helpers import structural_eq
from logos.runner import run, TacticFailed
from logos.tactics.combinators import then, first, try_, repeat, all_goals
from logos.tactics.rewrite import refl
from logos.tactics.structural import split, assumption, intro


def test_then_sequences(x):
    goal = Goal({}, (x > Lit(0)) >> (x > Lit(0)))
    proof = run(goal, [then(intro("h"), assumption())])
    ctx = Context({}, {})
    assert structural_eq(infer(proof, ctx), (x > Lit(0)) >> (x > Lit(0)))


def test_first_succeeds_on_first(x):
    goal = Goal({}, x == x)
    proof = run(goal, [first(refl(), assumption())])   # refl() succeeds first


def test_first_falls_through(x):
    hyp = x > Lit(0)
    goal = Goal({"h": hyp}, hyp)
    # refl() fails, assumption() succeeds
    proof = run(goal, [first(refl(), assumption())])


def test_try_succeeds_silently_on_fail(x, y):
    hyp = x > Lit(0)
    goal = Goal({"h": hyp}, hyp)
    # try_(refl()) fails on x == x goal (wait, no — we need x == x for refl)
    # try_(failing_tactic) should not raise; goal remains open
    # So chain with assumption():
    proof = run(goal, [try_(refl()), assumption()])


def test_all_goals_applies_to_each(x, y):
    goal = Goal({"hx": x == x, "hy": y == y}, (x == x) & (y == y))
    proof = run(goal, [split(), all_goals(assumption())])
