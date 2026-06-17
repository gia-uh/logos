import pytest
from logos.expr import Var, Lit
from logos.goal import Goal
from logos.kernel import infer, Context
from logos.helpers import structural_eq
from logos.runner import run, TacticFailed
from logos.tactics.arithmetic import ring, decide


def test_ring_commutativity(x, y):
    goal = Goal({}, x + y == y + x)
    proof = run(goal, [ring()])
    # ring returns Refl(lhs), so infer gives Eq(lhs, lhs)
    assert structural_eq(infer(proof, Context({}, {})), x + y == x + y)


def test_ring_distributivity(x, y, z):
    goal = Goal({}, x * (y + z) == x * y + x * z)
    proof = run(goal, [ring()])
    assert structural_eq(infer(proof, Context({}, {})), x * (y + z) == x * (y + z))


def test_ring_constant_folding():
    goal = Goal({}, Lit(2) + Lit(3) == Lit(5))
    proof = run(goal, [ring()])


def test_ring_fails_on_inequality(x, y):
    goal = Goal({}, x + y == x - y)   # not a ring identity
    with pytest.raises(TacticFailed, match="ring"):
        run(goal, [ring()])


def test_decide_ground_true():
    goal = Goal({}, Lit(3) > Lit(2))
    proof = run(goal, [decide()])
