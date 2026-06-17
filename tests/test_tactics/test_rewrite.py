import pytest
from logos.expr import Var, Lit, Add
from logos.goal import Goal
from logos.kernel import infer, Context
from logos.helpers import structural_eq
from logos.runner import run
from logos.tactics.rewrite import refl, eval_, norm_num


def test_refl_closes_eq_goal(x):
    goal = Goal({}, x == x)
    proof = run(goal, [refl()])
    ctx = Context({}, {})
    assert structural_eq(infer(proof, ctx), x == x)


def test_refl_fails_on_non_eq(x, y):
    from logos.runner import TacticFailed
    goal = Goal({}, x == y)   # x != y structurally
    with pytest.raises(TacticFailed, match="refl"):
        run(goal, [refl()])


def test_eval_ground():
    goal = Goal({}, Lit(2) + Lit(3) == Lit(5))
    proof = run(goal, [eval_()])
    ctx = Context({}, {})
    # eval_ normalizes both sides to Lit(5) and closes via Refl(Lit(5))
    assert structural_eq(infer(proof, ctx), Lit(5) == Lit(5))


def test_norm_num():
    goal = Goal({}, Lit(6) == Lit(2) * Lit(3))
    proof = run(goal, [norm_num()])
    ctx = Context({}, {})
    # norm_num normalizes both sides to Lit(6) and closes via Refl(Lit(6))
    assert structural_eq(infer(proof, ctx), Lit(6) == Lit(6))
