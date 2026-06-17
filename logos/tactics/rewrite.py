# logos/tactics/rewrite.py
from logos.expr import Expr, Lit, Var, Add, Sub, Mul, Div, Mod, Neg, Pow, Eq
from logos.goal import Goal
from logos.kernel import ProofTerm, Refl
from logos.helpers import structural_eq, substitute
from logos.runner import TacticFailed


def refl():
    def tactic(goal: Goal) -> ProofTerm:
        match goal.statement:
            case Eq(lhs, rhs) if structural_eq(lhs, rhs):
                return Refl(lhs)
            case _:
                raise TacticFailed(f"refl: goal is not `a == a`, got {goal.statement!r}")
    return tactic


def eval_():
    """Evaluate ground (variable-free) arithmetic sub-expressions, then close with Refl."""
    def tactic(goal: Goal) -> ProofTerm:
        match goal.statement:
            case Eq(lhs, rhs):
                try:
                    lhs_val = _eval_ground(lhs)
                    rhs_val = _eval_ground(rhs)
                    if lhs_val == rhs_val:
                        return Refl(Lit(lhs_val))
                    raise TacticFailed(f"eval_: {lhs_val} ≠ {rhs_val}")
                except ValueError as e:
                    raise TacticFailed(f"eval_: {e}")
            case _:
                raise TacticFailed("eval_: goal must be an equation")
    return tactic


def norm_num():
    """Normalize numeric literals and close if equal."""
    def tactic(goal: Goal) -> ProofTerm:
        match goal.statement:
            case Eq(lhs, rhs):
                try:
                    l = _eval_ground(lhs)
                    r = _eval_ground(rhs)
                    if l == r:
                        return Refl(Lit(l))
                    raise TacticFailed(f"norm_num: {l} ≠ {r}")
                except ValueError as e:
                    raise TacticFailed(f"norm_num: {e}")
            case _:
                raise TacticFailed("norm_num: goal must be an equation")
    return tactic


def _eval_ground(expr: Expr) -> int | float:
    """Evaluate a ground (no free variables) expression to a Python number."""
    match expr:
        case Lit(v) if isinstance(v, (int, float)): return v
        case Var():       raise ValueError(f"Variable {expr.name!r} in ground expression")
        case Add(l, r):   return _eval_ground(l) + _eval_ground(r)
        case Sub(l, r):   return _eval_ground(l) - _eval_ground(r)
        case Mul(l, r):   return _eval_ground(l) * _eval_ground(r)
        case Div(l, r):   return _eval_ground(l) // _eval_ground(r)
        case Mod(l, r):   return _eval_ground(l) % _eval_ground(r)
        case Neg(o):      return -_eval_ground(o)
        case Pow(b, e):   return _eval_ground(b) ** _eval_ground(e)
        case _:           raise ValueError(f"Cannot evaluate {expr!r}")


def unfold(*func_names: str):
    """Replace App(name, args) nodes with the function's definition body."""
    def tactic(goal: Goal):
        from logos.define import get_definition
        new_stmt = goal.statement
        for name in func_names:
            params, body = get_definition(name)
            new_stmt = _unfold_in(new_stmt, name, params, body)
        new_goal = goal.with_statement(new_stmt)
        return [new_goal], lambda ps: ps[0]
    return tactic


def _unfold_in(expr: Expr, fname: str, params: list[Var], body: Expr) -> Expr:
    from logos.expr import App
    match expr:
        case App(n, args) if n == fname:
            result = body
            for param, arg in zip(params, args):
                result = substitute(result, param, arg)
            return result
        case _:
            cls = type(expr)
            if not hasattr(cls, "__dataclass_fields__"):
                return expr
            fields = [getattr(expr, f) for f in cls.__dataclass_fields__]
            new_fields = [
                _unfold_in(f, fname, params, body) if isinstance(f, Expr) else f
                for f in fields
            ]
            return cls(*new_fields)


def rewrite(axiom_name: str):
    """Rewrite left-to-right using a named equation axiom."""
    def tactic(goal: Goal):
        ctx = goal.make_context()
        eq_stmt = ctx.lookup(axiom_name)
        match eq_stmt:
            case Eq(lhs, rhs):
                new_stmt = _replace_in(goal.statement, lhs, rhs)
                if structural_eq(new_stmt, goal.statement):
                    raise TacticFailed(f"rewrite '{axiom_name}': no occurrence of {lhs!r} found")
                new_goal = goal.with_statement(new_stmt)
                return [new_goal], lambda ps: ps[0]
            case _:
                raise TacticFailed(f"rewrite: '{axiom_name}' is not an equation")
    return tactic


def rewrite_rev(axiom_name: str):
    """Rewrite right-to-left using a named equation axiom."""
    def tactic(goal: Goal):
        ctx = goal.make_context()
        eq_stmt = ctx.lookup(axiom_name)
        match eq_stmt:
            case Eq(lhs, rhs):
                new_stmt = _replace_in(goal.statement, rhs, lhs)
                if structural_eq(new_stmt, goal.statement):
                    raise TacticFailed(f"rewrite_rev '{axiom_name}': no occurrence found")
                new_goal = goal.with_statement(new_stmt)
                return [new_goal], lambda ps: ps[0]
            case _:
                raise TacticFailed(f"rewrite_rev: '{axiom_name}' is not an equation")
    return tactic


def _replace_in(expr: Expr, pattern: Expr, replacement: Expr) -> Expr:
    if structural_eq(expr, pattern):
        return replacement
    cls = type(expr)
    if not hasattr(cls, "__dataclass_fields__"):
        return expr
    fields = [getattr(expr, f) for f in cls.__dataclass_fields__]
    new_fields = [
        _replace_in(f, pattern, replacement) if isinstance(f, Expr) else f
        for f in fields
    ]
    return cls(*new_fields)
