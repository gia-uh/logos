import pytest
from logos.expr import Var, Lit
from logos.registry import register_axiom, get_all_axioms, clear_axioms
from logos.goal import Goal
from logos.kernel import Context


def test_register_axiom(x):
    clear_axioms()
    stmt = x > Lit(0)
    register_axiom("pos_x", stmt)
    assert "pos_x" in get_all_axioms()


def test_duplicate_axiom(x):
    clear_axioms()
    register_axiom("pos_x", x > Lit(0))
    with pytest.raises(ValueError, match="already registered"):
        register_axiom("pos_x", x > Lit(0))


def test_goal_with_hyp(x, y):
    g = Goal({}, x > Lit(0))
    g2 = g.with_hyp("h", y > Lit(0))
    assert "h" in g2.context


def test_goal_make_context(x):
    clear_axioms()
    register_axiom("ax1", x == x)
    g = Goal({"h": x > Lit(0)}, x > Lit(0))
    ctx = g.make_context()
    assert "ax1" in ctx.axioms
    assert "h" in ctx.hyps
