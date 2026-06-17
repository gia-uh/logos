import pytest
from logos.expr import Var, Lit, Add, App
from logos.helpers import structural_eq
from logos.registry import clear_axioms, get_all_axioms
from logos.define import define, extern, get_definition

def test_define_creates_axiom():
    clear_axioms()

    @define
    def double(x: Var) -> "Expr":
        return x + x

    axioms = get_all_axioms()
    assert "double" in axioms

def test_define_python_mode():
    @define
    def triple(x: Var) -> "Expr":
        return x + x + x

    # With a real Python int, evaluates normally
    assert triple(5) == 15

def test_define_symbolic_mode(x):
    @define
    def double2(x: Var) -> "Expr":
        return x + x

    result = double2(x)
    assert isinstance(result, App)
    assert result.func_name == "double2"

def test_get_definition_returns_body(x):
    @define
    def quad(x: Var) -> "Expr":
        return x * Lit(4)

    params, body = get_definition("quad")
    assert len(params) == 1
    assert structural_eq(body, params[0] * Lit(4))

def test_extern_creates_symbol():
    clear_axioms()
    my_fn = extern("black_box", [int], int)
    x = Var("x", int)
    result = my_fn(x)
    assert isinstance(result, App)
    assert result.func_name == "black_box"
