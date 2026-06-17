from __future__ import annotations
from dataclasses import dataclass
from typing import Any

class Expr:
    """Base class for all expression nodes. Operators build expression trees."""

    def __add__(self, other):      return Add(self, _lift(other))
    def __radd__(self, other):     return Add(_lift(other), self)
    def __sub__(self, other):      return Sub(self, _lift(other))
    def __rsub__(self, other):     return Sub(_lift(other), self)
    def __mul__(self, other):      return Mul(self, _lift(other))
    def __rmul__(self, other):     return Mul(_lift(other), self)
    def __floordiv__(self, other): return Div(self, _lift(other))
    def __mod__(self, other):      return Mod(self, _lift(other))
    def __neg__(self):             return Neg(self)
    def __pow__(self, other):      return Pow(self, _lift(other))
    def __eq__(self, other):       return Eq(self, _lift(other))
    def __ne__(self, other):       return Neq(self, _lift(other))
    def __lt__(self, other):       return Lt(self, _lift(other))
    def __le__(self, other):       return Le(self, _lift(other))
    def __gt__(self, other):       return Gt(self, _lift(other))
    def __ge__(self, other):       return Ge(self, _lift(other))
    def __and__(self, other):      return And(self, other)
    def __rand__(self, other):     return And(other, self)
    def __or__(self, other):       return Or(self, other)
    def __ror__(self, other):      return Or(other, self)
    def __invert__(self):          return Not(self)
    def __rshift__(self, other):   return Implies(self, other)
    def __hash__(self):            return id(self)
    def __bool__(self):
        raise TypeError(
            "Expr cannot be used as a Python bool. "
            "Use & instead of 'and', | instead of 'or', ~ instead of 'not'."
        )

def _lift(val: Any) -> Expr:
    return val if isinstance(val, Expr) else Lit(val)

@dataclass(eq=False)
class Lit(Expr):
    value: Any

@dataclass(eq=False)
class Var(Expr):
    name: str
    type: type

# Arithmetic
@dataclass(eq=False)
class Add(Expr):  left: Expr; right: Expr
@dataclass(eq=False)
class Sub(Expr):  left: Expr; right: Expr
@dataclass(eq=False)
class Mul(Expr):  left: Expr; right: Expr
@dataclass(eq=False)
class Div(Expr):  left: Expr; right: Expr
@dataclass(eq=False)
class Mod(Expr):  left: Expr; right: Expr
@dataclass(eq=False)
class Neg(Expr):  operand: Expr
@dataclass(eq=False)
class Pow(Expr):  base: Expr; exp: Expr

# Comparisons
@dataclass(eq=False)
class Eq(Expr):   left: Expr; right: Expr
@dataclass(eq=False)
class Neq(Expr):  left: Expr; right: Expr
@dataclass(eq=False)
class Lt(Expr):   left: Expr; right: Expr
@dataclass(eq=False)
class Le(Expr):   left: Expr; right: Expr
@dataclass(eq=False)
class Gt(Expr):   left: Expr; right: Expr
@dataclass(eq=False)
class Ge(Expr):   left: Expr; right: Expr

# Logical
@dataclass(eq=False)
class And(Expr):     left: Expr; right: Expr
@dataclass(eq=False)
class Or(Expr):      left: Expr; right: Expr
@dataclass(eq=False)
class Not(Expr):     operand: Expr
@dataclass(eq=False)
class Implies(Expr): antecedent: Expr; consequent: Expr

# Quantifiers (internal nodes — use Forall/Exists factories below)
@dataclass(eq=False)
class ForallNode(Expr):
    __match_args__ = ("var", "body")
    var: Var
    body: Expr

@dataclass(eq=False)
class ExistsNode(Expr):
    __match_args__ = ("var", "body")
    var: Var
    body: Expr

def Forall(*args: Var | Expr) -> Expr:
    """Forall(x, y, body) → nested ForallNode(x, ForallNode(y, body))."""
    *vars_, body = args
    result = body
    for v in reversed(vars_):
        if not isinstance(v, Var):
            raise TypeError(f"Forall: expected Var, got {type(v).__name__}")
        result = ForallNode(v, result)
    return result

def Exists(var: Var, body: Expr) -> Expr:
    return ExistsNode(var, body)

# Function application
@dataclass(eq=False)
class App(Expr):
    func_name: str
    args: list[Expr]

# Case expression (used by @logos.define bodies)
@dataclass(eq=False)
class CaseExpr(Expr):
    branches: list[tuple[Expr, Expr]]   # [(condition, value), ...]
