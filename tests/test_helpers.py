# tests/test_helpers.py
from logos.expr import Var, Lit, Add, Mul, Eq, ForallNode, Forall
from logos.helpers import structural_eq, substitute, free_vars

def test_structural_eq_same(x, y):
    assert structural_eq(x + y, x + y)

def test_structural_eq_different_order(x, y):
    # x+y and y+x are structurally different
    assert not structural_eq(x + y, y + x)

def test_structural_eq_lit():
    assert structural_eq(Lit(1), Lit(1))
    assert not structural_eq(Lit(1), Lit(2))

def test_structural_eq_nested(x, y):
    e1 = (x + y) == (y + x)
    e2 = (x + y) == (y + x)
    assert structural_eq(e1, e2)

def test_substitute_var(x, y):
    expr = x + y
    result = substitute(expr, x, Lit(5))
    assert structural_eq(result, Lit(5) + y)

def test_substitute_no_capture(x, y):
    # substitute does not substitute inside a Forall binding the same var
    z = Var("z", int)
    expr = Forall(x, x + y)
    result = substitute(expr, x, Lit(5))
    # x is bound in the Forall, so substitution should not penetrate
    assert structural_eq(result, expr)

def test_free_vars(x, y):
    expr = x + y
    assert free_vars(expr) == {"x", "y"}

def test_free_vars_bound(x, y):
    expr = Forall(x, x + y)
    assert free_vars(expr) == {"y"}   # x is bound
