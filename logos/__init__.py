from logos.expr import Var, Lit, Forall, Exists, Expr
from logos.define import define, extern, cases, if_
from logos.theorem import theorem, axiom, check, prove, LogosProofError, Axiom, Theorem
from logos import tactics
import logos.builtins  # ensure builtin Axiom objects are available


def var(name: str, type_: type) -> Var:
    return Var(name, type_)


def vars(names: str, type_: type) -> tuple[Var, ...]:
    return tuple(Var(n, type_) for n in names.split())


def lit(value) -> Lit:
    return Lit(value)


def forall(type_: type, *rest) -> Expr:
    """logos.forall(int, int, lambda x, y: x + y == y + x) — lambda form."""
    import inspect
    if callable(rest[-1]) and not isinstance(rest[-1], Expr):
        fn = rest[-1]
        types = (type_,) + rest[:-1]
        param_names = list(inspect.signature(fn).parameters.keys())
        vs = [Var(n, t) for n, t in zip(param_names, types)]
        body = fn(*vs)
        return Forall(*vs, body)
    raise TypeError("logos.forall: last argument must be a lambda")


def exists(type_: type, fn) -> Expr:
    import inspect
    param_names = list(inspect.signature(fn).parameters.keys())
    v = Var(param_names[0], type_)
    body = fn(v)
    return Exists(v, body)
