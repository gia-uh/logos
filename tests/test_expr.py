import pytest
from logos.expr import Var, Lit, Add, Mul, Eq as LogosEq, Gt, And, Or, Not, Implies, Forall, Neg

def test_var_creation():
    x = Var("x", int)
    assert x.name == "x"
    assert x.type is int

def test_arithmetic_operators(x, y):
    assert isinstance(x + y, Add)
    assert isinstance(x + 1, Add)   # literal auto-lift
    assert isinstance(1 + x, Add)   # __radd__
    assert isinstance(-x, Neg)
    assert isinstance(x * 2, Mul)

def test_comparison_returns_expr(x, y):
    result = x == y
    assert isinstance(result, LogosEq)   # NOT Python bool
    assert isinstance(x > 0, Gt)

def test_logical_connectives(x, y):
    assert isinstance((x > 0) & (y > 0), And)
    assert isinstance((x > 0) | (y > 0), Or)
    assert isinstance(~(x > 0), Not)
    assert isinstance((x > 0) >> (y > 0), Implies)

def test_bool_guard(x):
    with pytest.raises(TypeError, match="Expr cannot be used as a Python bool"):
        bool(x > 0)

def test_literal_autolift(x):
    expr = x + 1
    assert isinstance(expr.right, Lit)
    assert expr.right.value == 1

def test_forall_nested(x, y):
    from logos.expr import ForallNode
    stmt = Forall(x, y, x + y == y + x)
    assert isinstance(stmt, ForallNode)
    assert isinstance(stmt.body, ForallNode)

def test_hash_is_identity(x):
    y = Var("x", int)  # same name, different object
    assert hash(x) != hash(y)  # identity-based
    s = {x, y}
    assert len(s) == 2
