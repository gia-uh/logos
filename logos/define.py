from __future__ import annotations
import inspect
from typing import Callable, Any
from logos.expr import Expr, Var, App, Forall, Eq
from logos.registry import register_axiom

# Registry: function name → (params, body_expr)
_definitions: dict[str, tuple[list[Var], Expr]] = {}


def get_definition(name: str) -> tuple[list[Var], Expr]:
    if name not in _definitions:
        raise KeyError(f"No logos definition for '{name}'")
    return _definitions[name]


def define(fn: Callable) -> Callable:
    """
    Decorator. Runs fn's body in symbolic mode (params as Var objects),
    captures the expression tree, registers a definition axiom, and returns
    a dual-mode callable.
    """
    sig = inspect.signature(fn)
    params = [
        Var(name, param.annotation if param.annotation is not inspect.Parameter.empty else object)
        for name, param in sig.parameters.items()
    ]

    # Run body in symbolic mode
    body_expr: Expr = fn(*params)
    func_name = fn.__name__

    # Store definition
    _definitions[func_name] = (params, body_expr)

    # Register definition axiom: Forall(params..., Eq(App(name, params), body))
    app_node = App(func_name, list(params))
    eq_stmt = app_node == body_expr   # builds Eq node via __eq__
    axiom_stmt = Forall(*params, eq_stmt) if params else eq_stmt
    register_axiom(func_name, axiom_stmt)

    # Return dual-mode callable
    def wrapper(*args):
        # If any arg is an Expr, return symbolic App
        if any(isinstance(a, Expr) for a in args):
            return App(func_name, list(args))
        # Otherwise, call the original Python function
        return fn(*args)

    wrapper.__name__ = func_name
    wrapper.__logos_defined__ = True
    return wrapper


def extern(name: str, arg_types: list[type], ret_type: type) -> Callable:
    """Declare an external (uninterpreted) function symbol. Returns an App builder."""
    def caller(*args):
        return App(name, list(args))
    caller.__name__ = name
    return caller


def cases(*branches: tuple[Expr, Expr]) -> Expr:
    """Build a CaseExpr from (condition, value) pairs."""
    from logos.expr import CaseExpr
    return CaseExpr(list(branches))


def if_(condition: Expr, then_val: Expr, else_val: Expr) -> Expr:
    """Ternary if expression."""
    return cases((condition, then_val), (~condition, else_val))
