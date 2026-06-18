import pytest
from logos.expr import Var, Lit
from logos.goal import Goal


def test_goal_with_hyp(x, y):
    g = Goal({}, x > Lit(0))
    g2 = g.with_hyp("h", y > Lit(0))
    assert "h" in g2.context


def test_goal_with_statement(x, y):
    g = Goal({"h": x > Lit(0)}, x > Lit(0))
    g2 = g.with_statement(y > Lit(0))
    assert "h" in g2.context
    from logos.helpers import structural_eq
    assert structural_eq(g2.statement, y > Lit(0))


def test_goal_context_isolated(x, y):
    """with_hyp returns a new Goal without mutating the original."""
    g = Goal({}, x > Lit(0))
    g2 = g.with_hyp("h", y > Lit(0))
    assert "h" not in g.context
    assert "h" in g2.context
