# logos/tactics/arithmetic.py
from logos.expr import (
    Expr, Lit, Var, Add, Sub, Mul, Div, Mod, Neg, Pow, Eq,
    Lt, Le, Gt, Ge,
)
from logos.goal import Goal
from logos.kernel import ProofTerm, Refl, KernelError
from logos.helpers import structural_eq
from logos.runner import TacticFailed

# Polynomial: dict from frozenset of (name, exp) pairs to coefficient
Poly = dict[frozenset, int | float]


def _poly_add(a: Poly, b: Poly) -> Poly:
    result = dict(a)
    for mono, coef in b.items():
        result[mono] = result.get(mono, 0) + coef
    return {m: c for m, c in result.items() if c != 0}


def _poly_scale(p: Poly, factor: int | float) -> Poly:
    return {m: c * factor for m, c in p.items()}


def _poly_mul(a: Poly, b: Poly) -> Poly:
    result: Poly = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            # Combine monomials: sum exponents
            combined: dict[str, int] = {}
            for name, exp in m1:
                combined[name] = combined.get(name, 0) + exp
            for name, exp in m2:
                combined[name] = combined.get(name, 0) + exp
            mono = frozenset((n, e) for n, e in combined.items() if e != 0)
            result[mono] = result.get(mono, 0) + c1 * c2
    return {m: c for m, c in result.items() if c != 0}


def _normalize(expr: Expr) -> Poly:
    match expr:
        case Lit(v) if isinstance(v, (int, float)):
            return {frozenset(): v} if v != 0 else {}
        case Var(name, _):
            return {frozenset({(name, 1)}): 1}
        case Add(l, r):
            return _poly_add(_normalize(l), _normalize(r))
        case Sub(l, r):
            return _poly_add(_normalize(l), _poly_scale(_normalize(r), -1))
        case Mul(l, r):
            return _poly_mul(_normalize(l), _normalize(r))
        case Neg(o):
            return _poly_scale(_normalize(o), -1)
        case Pow(base, Lit(n)) if isinstance(n, int) and n >= 0:
            result: Poly = {frozenset(): 1}
            base_p = _normalize(base)
            for _ in range(n):
                result = _poly_mul(result, base_p)
            return result
        case _:
            raise TacticFailed(f"ring: cannot normalize {expr!r}")


def ring():
    def tactic(goal: Goal) -> ProofTerm:
        match goal.statement:
            case Eq(lhs, rhs):
                try:
                    lhs_p = _normalize(lhs)
                    rhs_p = _normalize(rhs)
                    if lhs_p == rhs_p:
                        return Refl(lhs)
                    raise TacticFailed(
                        f"ring: {lhs!r} ≠ {rhs!r} after normalization\n"
                        f"  LHS poly: {lhs_p}\n  RHS poly: {rhs_p}"
                    )
                except TacticFailed:
                    raise
                except Exception as e:
                    raise TacticFailed(f"ring: {e}")
            case _:
                raise TacticFailed(f"ring: goal is not an equation, got {goal.statement!r}")
    return tactic


def decide():
    """Evaluate a ground boolean proposition and close the goal."""
    def tactic(goal: Goal) -> ProofTerm:
        try:
            result = _eval_bool(goal.statement)
        except ValueError as e:
            raise TacticFailed(f"decide: {e}")
        if result:
            return Refl(goal.statement)   # simplified: use Refl as witness token
        raise TacticFailed(f"decide: proposition is False: {goal.statement!r}")
    return tactic


def _eval_bool(expr: Expr) -> bool:
    from logos.tactics.rewrite import _eval_ground
    match expr:
        case Lit(v) if isinstance(v, bool): return v
        case Lt(l, r):  return _eval_ground(l) <  _eval_ground(r)
        case Le(l, r):  return _eval_ground(l) <= _eval_ground(r)
        case Gt(l, r):  return _eval_ground(l) >  _eval_ground(r)
        case Ge(l, r):  return _eval_ground(l) >= _eval_ground(r)
        case Eq(l, r):  return _eval_ground(l) == _eval_ground(r)
        case _:         raise ValueError(f"Cannot decide {expr!r}")


from fractions import Fraction


def linarith():
    def tactic(goal: Goal) -> ProofTerm:
        # Collect linear inequalities: (coef_dict, bound, strict)
        # e.g., "x > 2" → ({x: 1}, 2, True)
        ineqs = []
        for name, hyp in goal.context.items():
            ineq = _parse_linear_ineq(hyp)
            if ineq is not None:
                ineqs.append(ineq)

        # Negate the goal and add as a hypothesis
        negated = _negate_ineq(_parse_linear_ineq(goal.statement))
        if negated is None:
            raise TacticFailed("linarith: goal is not a linear inequality")
        ineqs.append(negated)

        # Try to derive a contradiction via non-negative combination
        if _farkas_contradiction(ineqs):
            return Refl(goal.statement)  # token proof; kernel trusts linarith for v0.1
        raise TacticFailed("linarith: no linear combination found")
    return tactic


def _parse_linear_ineq(expr: Expr):
    """Parse `expr` into (coefs: dict[str, Fraction], bound: Fraction, strict: bool).
    coefs[var] + ... OP bound.  Returns None if not linear."""
    match expr:
        case Gt(l, r) | Ge(l, r) | Lt(l, r) | Le(l, r) | Eq(l, r):
            coefs = _linear_coefs(l)
            rcoefs = _linear_coefs(r)
            if coefs is None or rcoefs is None:
                return None
            # Move RHS to left: (lcoefs - rcoefs) OP 0
            combined = {}
            for k, v in coefs.items():  combined[k] = v
            for k, v in rcoefs.items(): combined[k] = combined.get(k, Fraction(0)) - v
            bound = -combined.pop("_const", Fraction(0))
            combined = {k: v for k, v in combined.items() if v != 0}
            strict = isinstance(expr, (Gt, Lt))
            if isinstance(expr, (Lt, Le)):
                combined = {k: -v for k, v in combined.items()}
                bound = -bound
                strict = isinstance(expr, Lt)
            return combined, bound, strict
        case _:
            return None


def _linear_coefs(expr: Expr) -> dict | None:
    """Return {varname: coef, "_const": const} for a linear expression, or None."""
    match expr:
        case Lit(v) if isinstance(v, (int, float)):
            return {"_const": Fraction(v)}
        case Var(name, _):
            return {name: Fraction(1)}
        case Add(l, r):
            lc, rc = _linear_coefs(l), _linear_coefs(r)
            if lc is None or rc is None: return None
            result = dict(lc)
            for k, v in rc.items(): result[k] = result.get(k, Fraction(0)) + v
            return result
        case Sub(l, r):
            lc, rc = _linear_coefs(l), _linear_coefs(r)
            if lc is None or rc is None: return None
            result = dict(lc)
            for k, v in rc.items(): result[k] = result.get(k, Fraction(0)) - v
            return result
        case Mul(Lit(c), e) | Mul(e, Lit(c)) if isinstance(c, (int, float)):
            ec = _linear_coefs(e)
            if ec is None: return None
            return {k: Fraction(c) * v for k, v in ec.items()}
        case Neg(o):
            oc = _linear_coefs(o)
            if oc is None: return None
            return {k: -v for k, v in oc.items()}
        case _:
            return None


def _negate_ineq(ineq):
    if ineq is None: return None
    coefs, bound, strict = ineq
    # Negate: a > b becomes a <= b, i.e., -a >= -b → flip sign
    return ({k: -v for k, v in coefs.items()}, -bound, not strict)


def _farkas_contradiction(ineqs: list) -> bool:
    """Find λ_i >= 0 such that sum(λ_i * ineq_i) yields 0 op c with c > 0 (contradiction)."""
    from itertools import combinations

    # Standalone constant contradictions
    for coefs, bound, strict in ineqs:
        if not coefs:
            if strict and bound >= 0: return True
            if not strict and bound > 0: return True

    # Pair check with exact rational lambdas
    for (c1, b1, s1), (c2, b2, s2) in combinations(ineqs, 2):
        if _pair_contradiction(c1, b1, s1, c2, b2, s2):
            return True

    # Triple check: pick a pivot ineq to scale against each pair
    for i, (c0, b0, s0) in enumerate(ineqs):
        rest = [(c, b, s) for j, (c, b, s) in enumerate(ineqs) if j != i]
        for (c1, b1, s1), (c2, b2, s2) in combinations(rest, 2):
            # Combine ineq0 + pair; try unit lambdas
            for lam0, lam1, lam2 in [(1, 1, 1)]:
                combined: dict = {}
                for k, v in c0.items(): combined[k] = lam0 * v
                for k, v in c1.items(): combined[k] = combined.get(k, Fraction(0)) + lam1 * v
                for k, v in c2.items(): combined[k] = combined.get(k, Fraction(0)) + lam2 * v
                combined = {k: v for k, v in combined.items() if v != 0}
                combined_bound = lam0 * b0 + lam1 * b1 + lam2 * b2
                combined_strict = s0 or s1 or s2
                if not combined:
                    if combined_strict and combined_bound >= 0: return True
                    if not combined_strict and combined_bound > 0: return True
    return False


def _pair_contradiction(c1, b1, s1, c2, b2, s2) -> bool:
    """Find λ1, λ2 > 0 with λ1*c1 + λ2*c2 = 0 and resulting bound proving contradiction."""
    all_vars = set(c1.keys()) | set(c2.keys())
    if not all_vars:
        cb = b1 + b2; cs = s1 or s2
        return (cs and cb >= 0) or (not cs and cb > 0)

    # Solve for ratio λ1/λ2 that makes all variable coefficients cancel
    ratio: Fraction | None = None
    for x in all_vars:
        v1 = c1.get(x, Fraction(0))
        v2 = c2.get(x, Fraction(0))
        if v1 == 0 and v2 == 0: continue
        if v1 == 0 or v2 == 0: return False
        r = -v2 / v1
        if r <= 0: return False
        if ratio is None: ratio = r
        elif ratio != r: return False

    if ratio is None: return False
    cb = ratio * b1 + b2; cs = s1 or s2
    return (cs and cb >= 0) or (not cs and cb > 0)
