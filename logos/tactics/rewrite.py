# logos/tactics/rewrite.py
from logos.expr import Expr, Lit, Var, Add, Sub, Mul, Div, Mod, Neg, Pow, Eq, App, CaseExpr, ForallNode
from logos.goal import Goal
from logos.kernel import ProofTerm, Refl
from logos.helpers import structural_eq, substitute, try_unify, _merge_subs
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


def unfold(*refs):
    """Replace App(name, args) nodes with the function's definition body.

    Each ref can be:
    - A Function object (from @logos.define)
    - A string name (backward compat via _definitions dict)
    """
    def tactic(goal: Goal):
        new_stmt = goal.statement
        for ref in refs:
            if hasattr(ref, 'params') and hasattr(ref, 'body') and hasattr(ref, 'name'):
                # Function object
                params = ref.params
                body = ref.body
                name = ref.name
            else:
                # String name (backward compat)
                from logos.define import get_definition
                name = ref
                params, body = get_definition(name)
            new_stmt = _unfold_in(new_stmt, name, params, body)
        new_goal = goal.with_statement(new_stmt)
        return [new_goal], lambda ps: ps[0]
    return tactic


def _unfold_in(expr: Expr, fname: str, params: list, body: Expr) -> Expr:
    match expr:
        case App(n, args) if n == fname:
            subst_map = {param.name: arg for param, arg in zip(params, args)}
            return _substitute_many(body, subst_map)
        case App(n, args):
            return App(n, [_unfold_in(a, fname, params, body) for a in args])
        case CaseExpr(branches):
            return CaseExpr([(_unfold_in(c, fname, params, body), _unfold_in(v, fname, params, body))
                             for c, v in branches])
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


def _substitute_many(expr: Expr, subst_map: dict) -> Expr:
    """Apply all substitutions simultaneously (avoids sequential capture)."""
    match expr:
        case Var(name, _) if name in subst_map:
            return subst_map[name]
        case Var() | Lit():
            return expr
        case App(n, args):
            return App(n, [_substitute_many(a, subst_map) for a in args])
        case CaseExpr(branches):
            return CaseExpr([(_substitute_many(c, subst_map), _substitute_many(v, subst_map))
                             for c, v in branches])
        case _:
            cls = type(expr)
            if not hasattr(cls, "__dataclass_fields__"):
                return expr
            fields = [getattr(expr, f) for f in cls.__dataclass_fields__]
            new_fields = [
                _substitute_many(f, subst_map) if isinstance(f, Expr) else f
                for f in fields
            ]
            return cls(*new_fields)


def _resolve_stmt(ref) -> Expr:
    """Get the statement from an Axiom/Theorem object."""
    if hasattr(ref, 'statement'):
        return ref.statement
    raise TacticFailed(
        f"rewrite: expected Axiom or Theorem object, got {type(ref).__name__!r}"
    )


def rewrite(ref):
    """Rewrite left-to-right using a named equation or Axiom/Theorem object."""
    def tactic(goal: Goal):
        eq_stmt = _resolve_stmt(ref)
        flex_vars, stmt = _strip_foralls(eq_stmt)
        match stmt:
            case Eq(lhs, rhs):
                new_stmt = _replace_unify(goal.statement, lhs, rhs, flex_vars)
                if structural_eq(new_stmt, goal.statement):
                    raise TacticFailed(
                        f"rewrite '{getattr(ref, 'name', ref)}': no matching occurrence found"
                    )
                new_goal = goal.with_statement(new_stmt)
                return [new_goal], lambda ps: ps[0]
            case _:
                raise TacticFailed(
                    f"rewrite: '{getattr(ref, 'name', ref)}' is not an equation"
                )
    return tactic


def rewrite_rev(ref):
    """Rewrite right-to-left using a named equation or Axiom/Theorem object."""
    def tactic(goal: Goal):
        eq_stmt = _resolve_stmt(ref)
        flex_vars, stmt = _strip_foralls(eq_stmt)
        match stmt:
            case Eq(lhs, rhs):
                new_stmt = _replace_unify(goal.statement, rhs, lhs, flex_vars)
                if structural_eq(new_stmt, goal.statement):
                    raise TacticFailed(
                        f"rewrite_rev '{getattr(ref, 'name', ref)}': no matching occurrence found"
                    )
                new_goal = goal.with_statement(new_stmt)
                return [new_goal], lambda ps: ps[0]
            case _:
                raise TacticFailed(
                    f"rewrite_rev: '{getattr(ref, 'name', ref)}' is not an equation"
                )
    return tactic


def _strip_foralls(expr: Expr) -> tuple[set[str], Expr]:
    """Strip ForallNode binders, returning (bound_var_names, inner_expr)."""
    flex_vars: set[str] = set()
    while isinstance(expr, ForallNode):
        flex_vars.add(expr.var.name)
        expr = expr.body
    return flex_vars, expr


def _replace_unify(expr: Expr, lhs: Expr, rhs: Expr, flex_vars: set) -> Expr:
    """Replace all matches of lhs (with flex_vars unifiable) with rhs in expr."""
    sub = try_unify(lhs, expr, flex_vars)
    if sub is not None:
        return _substitute_many(rhs, sub)
    match expr:
        case App(n, args):
            return App(n, [_replace_unify(a, lhs, rhs, flex_vars) for a in args])
        case CaseExpr(branches):
            return CaseExpr([(_replace_unify(c, lhs, rhs, flex_vars), _replace_unify(v, lhs, rhs, flex_vars))
                             for c, v in branches])
        case _:
            cls = type(expr)
            if not hasattr(cls, "__dataclass_fields__"):
                return expr
            fields = [getattr(expr, f) for f in cls.__dataclass_fields__]
            new_fields = [
                _replace_unify(f, lhs, rhs, flex_vars) if isinstance(f, Expr) else f
                for f in fields
            ]
            return cls(*new_fields)
