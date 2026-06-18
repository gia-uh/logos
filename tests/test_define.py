import pytest
from logos.expr import Var, Lit, Add, App
from logos.helpers import structural_eq
from logos.define import define, extern, get_definition, Function


def test_define_returns_function_object():
    @define
    def double(x: int):
        return x + x

    assert isinstance(double, Function)
    assert double.name == "double"


def test_define_python_mode():
    @define
    def triple(x: int):
        return x + x + x

    # With a real Python int, evaluates normally
    assert triple(5) == 15


def test_define_symbolic_mode(x):
    @define
    def double2(x: int):
        return x + x

    result = double2(x)
    assert isinstance(result, App)
    assert result.func_name == "double2"


def test_get_definition_returns_body(x):
    @define
    def quad(x: int):
        return x * Lit(4)

    params, body = get_definition("quad")
    assert len(params) == 1
    assert structural_eq(body, params[0] * Lit(4))


def test_extern_creates_symbol():
    my_fn = extern("black_box", [int], int)
    x = Var("x", int)
    result = my_fn(x)
    assert isinstance(result, App)
    assert result.func_name == "black_box"


def test_function_carries_params_body():
    @define
    def inc(n: int):
        return n + Lit(1)

    assert len(inc.params) == 1
    assert inc.params[0].name == "n"
    assert structural_eq(inc.body, inc.params[0] + Lit(1))
