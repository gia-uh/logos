# tests/test_runner.py
import pytest
from logos.expr import Var, Lit
from logos.goal import Goal
from logos.kernel import Refl, AndIntro, ProofTerm
from logos.runner import run, TacticFailed, TrailingTactics
from logos.helpers import structural_eq

def closing_tactic(goal: Goal) -> ProofTerm:
    """Dummy: always returns Refl for test purposes."""
    return Refl(goal.statement.left)   # assumes Eq goal

def transforming_tactic(goal: Goal):
    """Transforms goal to a simpler form (1 subgoal)."""
    new_goal = Goal(goal.context, goal.statement)
    return [new_goal], lambda proofs: proofs[0]

def splitting_tactic(goal: Goal):
    """Splits into 2 subgoals (mirrors AndIntro)."""
    match goal.statement:
        case _ if hasattr(goal.statement, "left") and hasattr(goal.statement, "right"):
            l_goal = Goal(goal.context, goal.statement.left)
            r_goal = Goal(goal.context, goal.statement.right)
            return [l_goal, r_goal], lambda ps: AndIntro(ps[0], ps[1])

def test_atomic_closes_goal(x):
    goal = Goal({}, x == x)
    proof = run(goal, [closing_tactic])
    assert isinstance(proof, ProofTerm)

def test_transforming_tactic(x):
    goal = Goal({}, x == x)
    proof = run(goal, [transforming_tactic, closing_tactic])
    assert isinstance(proof, ProofTerm)

def test_splitting_with_nested_lists(x, y):
    from logos.expr import And
    goal = Goal({}, (x == x) & (y == y))
    proof = run(goal, [
        splitting_tactic,
        [closing_tactic],   # handles x == x
        [closing_tactic],   # handles y == y
    ])
    assert isinstance(proof, ProofTerm)

def test_no_tactics_raises(x):
    goal = Goal({}, x == x)
    with pytest.raises(TacticFailed, match="no tactics"):
        run(goal, [])

def test_extra_tactics_raises(x):
    goal = Goal({}, x == x)
    with pytest.raises(TrailingTactics) as raised:
        run(goal, [closing_tactic, closing_tactic])
    assert raised.value.remaining == 1
    assert "already closed" in str(raised.value)


def test_extra_tactics_after_nested_list_raises(x):
    goal = Goal({}, x == x)
    with pytest.raises(TrailingTactics) as raised:
        run(goal, [[closing_tactic], closing_tactic])
    assert raised.value.remaining == 1
    assert "already closed" in str(raised.value)


def test_extra_tactics_after_all_goals_raises(x, y):
    from logos.expr import And
    from logos.tactics.combinators import all_goals
    from logos.tactics.structural import assumption, split

    goal = Goal({"hx": x == x, "hy": y == y}, (x == x) & (y == y))
    with pytest.raises(TrailingTactics) as raised:
        run(goal, [split(), all_goals(assumption()), assumption()])
    assert raised.value.remaining == 1
