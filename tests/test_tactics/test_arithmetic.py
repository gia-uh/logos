import pytest
import logos
from logos.expr import Var, Lit
from logos.goal import Goal
from logos.runner import run, TacticFailed
from logos.tactics.arithmetic import ring, decide, linarith


def test_ring_commutativity(x, y):
    proof = logos.prove(x + y == y + x, [ring()])
    assert logos.check(proof).certified


def test_ring_distributivity(x, y, z):
    proof = logos.prove(x * (y + z) == x * y + x * z, [ring()])
    assert logos.check(proof).certified


def test_ring_constant_folding():
    proof = logos.prove(Lit(2) + Lit(3) == Lit(5), [ring()])
    assert logos.check(proof).certified


def test_ring_collects_signed_coefficients_after_factor_reordering(x):
    proof = logos.prove((x * (2*x)) * -3 == -6 * x**2, [ring()])
    assert logos.check(proof).certified


def test_portable_integer_literal_beyond_python_decimal_string_limit():
    number = 10**4999
    proof = logos.prove(Lit(number) + 1 == Lit(number + 1), [ring()])
    assert logos.check(proof).certified


def test_ring_fails_on_inequality(x, y):
    goal = Goal({}, x + y == x - y)   # not a ring identity
    with pytest.raises(TacticFailed, match="ring"):
        run(goal, [ring()])


def test_decide_ground_true():
    goal = Goal({}, Lit(3) > Lit(2))
    proof = run(goal, [decide()])


def test_linarith_simple(x, y):
    # From x > 0 and y > x, prove y > 0
    goal = Goal({"h1": x > Lit(0), "h2": y > x}, y > Lit(0))
    proof = run(goal, [linarith()])


def test_linarith_combination(x, y):
    # From x > 2, prove x > 1
    goal = Goal({"h": x > Lit(2)}, x > Lit(1))
    proof = run(goal, [linarith()])


def test_linarith_fails_when_not_provable(x):
    goal = Goal({"h": x > Lit(0)}, x > Lit(5))  # x>0 doesn't imply x>5
    with pytest.raises(TacticFailed):
        run(goal, [linarith()])
