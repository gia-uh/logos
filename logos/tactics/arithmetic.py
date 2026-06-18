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
    """Fourier-Motzkin elimination: detect if the linear inequality system is unsatisfiable.

    Each ineq is (coefs: dict[str, Fraction], bound: Fraction, strict: bool)
    meaning:  sum(coefs[v]*v) > bound  (strict)
           or sum(coefs[v]*v) >= bound (not strict)
    """
    def _is_contradicted(system):
        for coefs, bound, strict in system:
            if not coefs:
                if strict and bound >= 0: return True
                if not strict and bound > 0: return True
        return False

    def _elim(x, system):
        pos, neg, zero = [], [], []
        for coefs, bound, strict in system:
            c = coefs.get(x, Fraction(0))
            rest = {k: v for k, v in coefs.items() if k != x}
            if c > 0:
                pos.append((c, rest, bound, strict))
            elif c < 0:
                neg.append((c, rest, bound, strict))
            else:
                zero.append((rest, bound, strict))

        new_sys = list(zero)
        for alpha, r1, b1, s1 in pos:
            for gamma_neg, r2, b2, s2 in neg:
                gamma = -gamma_neg   # > 0
                combined = {}
                for k in set(r1.keys()) | set(r2.keys()):
                    v = gamma * r1.get(k, Fraction(0)) + alpha * r2.get(k, Fraction(0))
                    if v != 0:
                        combined[k] = v
                new_sys.append((combined, gamma * b1 + alpha * b2, s1 or s2))
        return new_sys

    # Collect all variables
    all_vars: set[str] = set()
    for coefs, _, _ in ineqs:
        all_vars |= set(coefs.keys())

    system = [(dict(c), Fraction(b), s) for c, b, s in ineqs]
    for x in sorted(all_vars):       # deterministic variable order
        if _is_contradicted(system):
            return True
        system = _elim(x, system)
    return _is_contradicted(system)
