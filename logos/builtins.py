# logos/builtins.py
"""
Core arithmetic axioms loaded at import time.
These are AXIOMS — assumed true, not proved.
They encode standard ring laws for Python ints/floats.
"""
from logos.expr import Var, Lit, Forall
from logos.registry import register_axiom, get_all_axioms

_x = Var("__x", int)
_y = Var("__y", int)
_z = Var("__z", int)

_BUILTINS = {
    "int_add_comm":  Forall(_x, _y, _x + _y == _y + _x),
    "int_add_assoc": Forall(_x, _y, _z, (_x + _y) + _z == _x + (_y + _z)),
    "int_mul_comm":  Forall(_x, _y, _x * _y == _y * _x),
    "int_mul_assoc": Forall(_x, _y, _z, (_x * _y) * _z == _x * (_y * _z)),
    "int_distrib":   Forall(_x, _y, _z, _x * (_y + _z) == _x * _y + _x * _z),
    "int_add_zero":  Forall(_x, _x + Lit(0) == _x),
    "int_mul_one":   Forall(_x, _x * Lit(1) == _x),
    "int_mul_zero":  Forall(_x, _x * Lit(0) == Lit(0)),
    "int_sub_def":   Forall(_x, _y, _x - _y == _x + (-_y)),
    "int_neg_neg":   Forall(_x, -(-_x) == _x),
}


def _load() -> None:
    """Register all builtin axioms not already in the registry."""
    existing = get_all_axioms()
    for name, stmt in _BUILTINS.items():
        if name not in existing:
            register_axiom(name, stmt)


_load()
