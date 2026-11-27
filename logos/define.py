from __future__ import annotations
import inspect
from typing import Callable, get_type_hints
from logos.expr import Expr, Var, App, _lift
from logos.helpers import normalize_order

# Registry: function name → (params, body_expr)
_definitions: dict[str, tuple[list[Var], Expr]] = {}


def get_definition(name: str) -> tuple[list[Var], Expr]:
    if name not in _definitions:
        raise KeyError(f"No logos definition for '{name}'")
    return _definitions[name]


class Function:
    """A logos-defined function. Callable (builds App nodes) and carries its definition.

    ``recursor`` is ``(base, step, value_var)`` for a primitive-recursive
    definition on the natural numbers. The single parameter is the argument;
    ``step`` uses the argument and ``value_var`` for the previous value.
    """
    def __init__(self, name: str, params: list[Var], body: Expr | None,
                 original_fn: Callable = None, result_type: type | None = None,
                 recursor: tuple[Expr, Expr, Var] | None = None,
                 portable_id: str | None = None):
        self.name = name
        self.portable_id = portable_id
        self.params = params
        self.body = body
        self.result_type = result_type
        self._original_fn = original_fn
        self.recursor = recursor
        self.recursor = recursor
        self.__name__ = name
        self.__logos_defined__ = True

    def __call__(self, *args):
        if any(isinstance(a, Expr) for a in args):
            return App(self.name, [_lift(arg) for arg in args], self)
        if self._original_fn is not None:
            return self._original_fn(*args)
        return App(self.name, [_lift(arg) for arg in args], self)

    def __repr__(self):
        return f"Function({self.name!r})"


def define(fn: Callable) -> Function:
    """@logos.define decorator — creates a Function object."""
    sig = inspect.signature(fn)
    try:
        hints = get_type_hints(fn)
    except (NameError, TypeError):
        hints = {}
    params = [
        Var(name, hints.get(name, param.annotation if param.annotation is not inspect.Parameter.empty else object))
        for name, param in sig.parameters.items()
    ]
    body_expr: Expr = normalize_order(fn(*params))
    func_name = fn.__name__
    _definitions[func_name] = (params, body_expr)
    return Function(func_name, params, body_expr, original_fn=fn, result_type=hints.get('return'))


def recursor(name: str, base, step: Callable[[Var, Var], Expr]) -> Function:
    """Declare a primitive-recursive integer function on the naturals.

    ``base`` is the value at zero and ``step(n, previous)`` is the value at
    ``n + 1`` for ``n >= 0``. The checker owns the two defining equations; the
    function stays opaque to conversion, so proofs must cite the equations.
    """
    argument = Var("n", int)
    previous = Var("value", int)
    base_expr = _lift(base)
    step_expr = normalize_order(step(argument, previous))
    if not isinstance(step_expr, Expr):
        raise TypeError("logos.recursor: the step must return an Expr")
    return Function(
        name,
        [argument],
        None,
        result_type=int,
        recursor=(base_expr, step_expr, previous),
    )


def extern(name: str, arg_types: list[type], ret_type: type) -> Callable:
    """Declare an external (uninterpreted) function symbol."""
    symbol = Function(name, [Var(f"arg{i}", sort) for i, sort in enumerate(arg_types)],
                      None, result_type=ret_type)

    def caller(*args):
        return symbol(*args)

    caller.__name__ = name
    return caller


def definition(fn: Callable) -> Function:
    """The book spelling of :func:`define` for transparent propositions."""
    return define(fn)


def cases(*branches) -> Expr:
    from logos.expr import CaseExpr
    return CaseExpr(list(branches))


def if_(condition: Expr, then_val: Expr, else_val: Expr) -> Expr:
    return cases((condition, then_val), (~condition, else_val))
