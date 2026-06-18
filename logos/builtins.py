"""Core arithmetic axioms. These are Axiom objects — trusted, not proved."""
from logos.expr import Var, Lit, ForallNode
from logos.theorem import Axiom

_x = Var("__x", int)
_y = Var("__y", int)
_z = Var("__z", int)


def _fa(*args):
    """Build nested ForallNode."""
    *vs, body = args
    for v in reversed(vs):
        body = ForallNode(v, body)
    return body


int_add_comm  = Axiom(_fa(_x, _y, _x + _y == _y + _x),                          name="int_add_comm")
int_add_assoc = Axiom(_fa(_x, _y, _z, (_x + _y) + _z == _x + (_y + _z)),        name="int_add_assoc")
int_mul_comm  = Axiom(_fa(_x, _y, _x * _y == _y * _x),                          name="int_mul_comm")
int_mul_assoc = Axiom(_fa(_x, _y, _z, (_x * _y) * _z == _x * (_y * _z)),        name="int_mul_assoc")
int_distrib   = Axiom(_fa(_x, _y, _z, _x * (_y + _z) == _x * _y + _x * _z),    name="int_distrib")
int_add_zero  = Axiom(_fa(_x, _x + Lit(0) == _x),                               name="int_add_zero")
int_mul_one   = Axiom(_fa(_x, _x * Lit(1) == _x),                               name="int_mul_one")
int_mul_zero  = Axiom(_fa(_x, _x * Lit(0) == Lit(0)),                           name="int_mul_zero")
int_sub_def   = Axiom(_fa(_x, _y, _x - _y == _x + (-_y)),                       name="int_sub_def")
int_neg_neg   = Axiom(_fa(_x, -(-_x) == _x),                                    name="int_neg_neg")
