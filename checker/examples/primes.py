"""Euclid's theorem: for every n >= 2 some prime is greater than n.

Run this file with the installed package to check the proof, write the
portable certificate, and inspect it with the Rust checker:

    python primes.py primes.logos
    logos check --strict primes.logos
    logos inspect --markdown --strict primes.logos

The development is constructive: n! + 1 has a least divisor greater than 1,
that divisor is prime, and it cannot be at most n.  Every step is checked
evidence; Python only builds the terms.
"""
from __future__ import annotations

import sys

import logos
from logos import tactics as t
from logos.expr import And, Eq, Exists, Forall, Implies, Lit, Lt, Not, Var
from logos.kernel import (
    AndElimL, AndElimR, AndIntro, Block, CaseAnalysis, Congr, CoreLaw, EqSubst, ExistsElim,
    ExistsIntro, ExFalso, ForallElim, ForallIntro, HypRef, ImpliesElim,
    ImpliesIntro, Induction, Least, NotElim, NotIntro, RecursorBase,
    RecursorStep, Refl, Symm, TheoremRef, Trans,
)
from logos.tactics._ring import Ring

INT = int
ZERO = Lit(0)
ONE = Lit(1)
TWO = Lit(2)


# ── Transparent definitions ──────────────────────────────────────────────────

def divides(d, n):
    """d | n  :=  exists q, n = d * q."""
    q = Var("q", INT)
    return Exists(q, Eq(n, d * q))


def prime(p):
    """1 < p and no d with 1 < d < p divides p."""
    d = Var("d", INT)
    proper = And(And(Lt(ONE, d), Lt(d, p)), divides(d, p))
    return And(Lt(ONE, p), Not(Exists(d, proper)))


factorial = logos.recursor(
    "factorial",
    1,
    lambda n, previous: (n + 1) * previous,
)


# ── Reusable proof constructors ──────────────────────────────────────────────

def law(name, args, *premises):
    proof = CoreLaw(name, tuple(args))
    for premise in premises:
        proof = ImpliesElim(proof, premise)
    return proof


def close_block(ring, equation):
    if equation.step is None:
        return Refl(equation.left)
    return Block(tuple(ring.steps), equation.step.index)


def apply_theorem(theorem, *terms):
    proof = TheoremRef(theorem)
    for term in terms:
        proof = ForallElim(proof, term)
    return proof


def lt_trans(first, middle, last, low, high):
    return law("lt_trans", (first, middle, last), low, high)


def lt_irrefl(value):
    return law("lt_irrefl", (value,))


def zero_lt_one():
    return law("lt_succ_rev", (ZERO, ZERO), lt_irrefl(ZERO))


def one_lt_two():
    return law("lt_succ_rev", (ONE, ONE), lt_irrefl(ONE))


def not_lt_of_gt(low, high, proof):
    """From low < high derive not (high < low)."""
    inner = lt_trans(low, high, low, proof, HypRef("back"))
    return NotIntro(ImpliesIntro(Lt(high, low), "back", NotElim(lt_irrefl(low), inner)))


def eq_of_not_lt(left, right, left_proof, right_proof):
    return law("eq_of_not_lt_not_lt", (left, right), left_proof, right_proof)


def move_dividend(subject, equality, proof):
    """From subject | left and left = right derive subject | right."""
    tvar = Var("t", INT)
    return EqSubst(equality, tvar, divides(subject, tvar), proof)


# ── Lemma 1: every integer divides itself ────────────────────────────────────

def build_dvd_refl():
    d = Var("d", INT)
    goal = divides(d, d)
    witness = Ring().prove(Eq(d, d * ONE))
    body = ExistsIntro(ONE, witness, goal)
    statement = Forall(d, goal)
    theorem = logos.Theorem(statement, name="dvd_refl")
    theorem.proof(t.exact(ForallIntro(d, body)))
    return theorem


# ── Lemma 2: divisibility is transitive ──────────────────────────────────────

def build_dvd_trans():
    a, b, c = (Var(name, INT) for name in "abc")
    q1, q2 = Var("q1", INT), Var("q2", INT)
    goal = divides(a, c)
    ring = Ring()
    e1 = ring.emit(b, a * q1, HypRef("e1"))
    lifted = ring.lift(lambda term: term * q2, e1)
    e2 = ring.emit(c, b * q2, HypRef("e2"))
    first = ring.chain(e2, lifted)
    step = ring.emit((a * q1) * q2, a * (q1 * q2),
                     Ring().prove(Eq((a * q1) * q2, a * (q1 * q2))))
    full = ring.chain(first, step)
    inner = ExistsIntro(q1 * q2, close_block(ring, full), goal)
    inner = ExistsElim(HypRef("h2"), q2, "e2", inner)
    inner = ExistsElim(HypRef("h1"), q1, "e1", inner)
    term = ForallIntro(a, ForallIntro(b, ForallIntro(c,
        ImpliesIntro(divides(a, b), "h1",
                     ImpliesIntro(divides(b, c), "h2", inner)))))
    statement = Forall(a, Forall(b, Forall(c,
        Implies(divides(a, b), Implies(divides(b, c), divides(a, c))))))
    theorem = logos.Theorem(statement, name="dvd_trans")
    theorem.proof(t.exact(term))
    return theorem


# ── Lemma 3: multiplying the dividend preserves divisibility ────────────────

def build_dvd_mul():
    a, b, c = (Var(name, INT) for name in "abc")
    q = Var("q", INT)
    goal = divides(a, c * b)
    ring = Ring()
    e = ring.emit(b, a * q, HypRef("e"))
    lifted = ring.lift(lambda term: c * term, e)
    step = ring.emit(c * (a * q), a * (q * c),
                     Ring().prove(Eq(c * (a * q), a * (q * c))))
    full = ring.chain(lifted, step)
    inner = ExistsIntro(q * c, close_block(ring, full), goal)
    inner = ExistsElim(HypRef("h"), q, "e", inner)
    term = ForallIntro(a, ForallIntro(b, ForallIntro(c,
        ImpliesIntro(divides(a, b), "h", inner))))
    statement = Forall(a, Forall(b, Forall(c,
        Implies(divides(a, b), divides(a, c * b)))))
    theorem = logos.Theorem(statement, name="dvd_mul")
    theorem.proof(t.exact(term))
    return theorem


# ── Lemma 4: consecutive integers have only unit common divisors ────────────

def build_consecutive_dvd_one():
    a, d = Var("a", INT), Var("d", INT)
    j, k = Var("j", INT), Var("k", INT)
    goal = divides(d, ONE)
    ring = Ring()
    start = ring.emit(ONE, (a + ONE) - a,
                      Ring().prove(Eq(ONE, (a + ONE) - a)))
    hole = Var("hole", INT)
    e2 = ring.emit((a + ONE) - a, (d * k) - a,
                   Congr(hole, hole - a, HypRef("e2")))
    e1 = ring.emit((d * k) - a, (d * k) - (d * j),
                   Congr(hole, (d * k) - hole, HypRef("e1")))
    finish = ring.emit((d * k) - (d * j), d * (k - j),
                       Ring().prove(Eq((d * k) - (d * j), d * (k - j))))
    full = ring.chain(start, e2, e1, finish)
    inner = ExistsIntro(k - j, close_block(ring, full), goal)
    inner = ExistsElim(HypRef("h2"), k, "e2", inner)
    inner = ExistsElim(HypRef("h1"), j, "e1", inner)
    term = ForallIntro(a, ForallIntro(d,
        ImpliesIntro(divides(d, a), "h1",
                     ImpliesIntro(divides(d, a + ONE), "h2", inner))))
    statement = Forall(a, Forall(d,
        Implies(divides(d, a), Implies(divides(d, a + ONE), divides(d, ONE)))))
    theorem = logos.Theorem(statement, name="consecutive_dvd_one")
    theorem.proof(t.exact(term))
    return theorem


# ── Lemma 5: no integer greater than one divides one ────────────────────────

def build_not_dvd_one_of_gt_one():
    d, q = Var("d", INT), Var("q", INT)
    tvar = Var("t", INT)
    # First branch: d = 1 contradicts 1 < d through lt_neq.
    d_eq_one_false = NotElim(
        law("lt_neq", (ONE, d), HypRef("gt")),
        Symm(HypRef("case")),
    )
    # Second branch: d = -1 transports 1 < d to 1 < -1, so 2 < 0 while 0 < 2.
    minus_one = EqSubst(HypRef("case"), d, Lt(ONE, d), HypRef("gt"))
    two_lt_zero = law("lt_add", (ONE, Lit(-1), ONE), minus_one)
    zero_lt_two = lt_trans(ZERO, ONE, TWO, zero_lt_one(), one_lt_two())
    zero_lt_zero = lt_trans(ZERO, TWO, ZERO, zero_lt_two, two_lt_zero)
    minus_one_false = NotElim(lt_irrefl(ZERO), zero_lt_zero)

    unit = law("mul_eq_one", (d, q), Symm(HypRef("e")))
    from logos.kernel import CaseAnalysis
    cases = CaseAnalysis(unit, "case", d_eq_one_false, minus_one_false)
    body = ExistsElim(HypRef("dvd"), q, "e", cases)
    term = ForallIntro(d, ImpliesIntro(Lt(ONE, d), "gt",
        NotIntro(ImpliesIntro(divides(d, ONE), "dvd", body))))
    statement = Forall(d, Implies(Lt(ONE, d), Not(divides(d, ONE))))
    theorem = logos.Theorem(statement, name="not_dvd_one_of_gt_one")
    theorem.proof(t.exact(term))
    return theorem


# ── Lemma 6: the factorial is positive ──────────────────────────────────────

def build_factorial_pos():
    n = Var("n", INT)
    tvar = Var("t", INT)
    predicate = Lt(ZERO, factorial(n))
    base = EqSubst(Symm(RecursorBase(factorial)), tvar, Lt(ZERO, tvar), zero_lt_one())
    k = Var("n", INT)
    hk = Not(Lt(k, ZERO))
    hpos = Lt(ZERO, factorial(k))
    succ_positive = law("lt_succ_rev", (ZERO, k), HypRef("hk"))
    product_positive = law("mul_pos", (k + ONE, factorial(k)),
                           succ_positive, HypRef("hpos"))
    step_equation = RecursorStep(factorial, k, HypRef("hk"))
    step_body = EqSubst(Symm(step_equation), tvar, Lt(ZERO, tvar), product_positive)
    step = ForallIntro(k, ImpliesIntro(hk, "hk",
        ImpliesIntro(hpos, "hpos", step_body)))
    statement = Forall(n, Implies(Not(Lt(n, ZERO)), predicate))
    theorem = logos.Theorem(statement, name="factorial_pos")
    theorem.proof(t.exact(Induction(ZERO, n, predicate, base, step)))
    return theorem


def lt_dne(low, high, double_negation):
    """Derive low < high from its double negation, via decidability."""
    decision = law("lt_decidable", (low, high))
    return CaseAnalysis(
        decision,
        "h",
        HypRef("h"),
        ExFalso(NotElim(double_negation, HypRef("h")), Lt(low, high)),
    )


# ── Lemma 7: every divisor up to n divides n! ───────────────────────────────

def build_factorial_dvd(dvd_mul_theorem):
    n = Var("n", INT)
    d = Var("d", INT)
    predicate = Forall(d, Implies(
        Lt(ONE, d), Implies(Lt(d, n + ONE), divides(d, factorial(n)))))

    # Base: no d satisfies 1 < d < 1.
    base_d = Var("d", INT)
    base_gt = Lt(ONE, base_d)
    base_lt = Lt(base_d, ZERO + ONE)
    base_clash = lt_trans(ONE, base_d, ONE, HypRef("hgt"), HypRef("hlt"))
    base = ForallIntro(base_d, ImpliesIntro(
        base_gt, "hgt",
        ImpliesIntro(base_lt, "hlt",
                     ExFalso(NotElim(lt_irrefl(ONE), base_clash),
                             divides(base_d, factorial(ZERO))))))

    # Step: split on d < k + 1.
    k = Var("n", INT)
    hk = Not(Lt(k, ZERO))
    ih_d = Var("d", INT)
    ih = Forall(ih_d, Implies(
        Lt(ONE, ih_d), Implies(Lt(ih_d, k + ONE), divides(ih_d, factorial(k)))))
    d2 = Var("d", INT)
    d2_gt = Lt(ONE, d2)
    d2_lt = Lt(d2, (k + ONE) + ONE)
    decision = law("lt_decidable", (d2, k + ONE))

    # Case d < k + 1: the induction hypothesis gives d | k!, then multiply.
    smaller = ImpliesElim(
        ImpliesElim(ForallElim(HypRef("ih"), d2), HypRef("hgt")),
        HypRef("hcase"))
    multiplied = ImpliesElim(
        apply_theorem(dvd_mul_theorem, d2, factorial(k), k + ONE), smaller)
    equation = RecursorStep(factorial, k, HypRef("hk"))
    smaller_result = move_dividend(d2, Symm(equation), multiplied)

    # Case not (d < k + 1): the bound gives d = k + 1, then d | (k+1)!.
    forward = law("lt_succ_fwd", (d2, k + ONE), HypRef("hlt"))
    equal = eq_of_not_lt(d2, k + ONE, HypRef("hcase"), forward)
    equation = RecursorStep(factorial, k, HypRef("hk"))
    hole = Var("hole", INT)
    restricted = Congr(hole, hole * factorial(k), Symm(equal))
    quotient = Trans(equation, restricted)
    larger_result = ExistsIntro(
        factorial(k), quotient, divides(d2, factorial(k + ONE)))

    step_body = CaseAnalysis(decision, "hcase", smaller_result, larger_result)
    step = ForallIntro(k, ImpliesIntro(hk, "hk", ImpliesIntro(ih, "ih",
        ForallIntro(d2, ImpliesIntro(d2_gt, "hgt", ImpliesIntro(d2_lt, "hlt",
                                                               step_body))))))
    statement = Forall(n, Implies(Not(Lt(n, ZERO)), predicate))
    theorem = logos.Theorem(statement, name="factorial_dvd")
    theorem.proof(t.exact(Induction(ZERO, n, predicate, base, step)))
    return theorem


# ── Lemma 8: every integer above one has a prime factor ─────────────────────

def build_prime_factor(dvd_refl_theorem, dvd_trans_theorem):
    n = Var("n", INT)
    least_m = Var("m", INT)
    predicate = And(Lt(ONE, least_m), divides(least_m, n))
    membership = And(Not(Lt(least_m, ONE)), predicate)
    nonempty_goal = Exists(least_m, membership)
    nonempty = ExistsIntro(
        n,
        AndIntro(
            not_lt_of_gt(ONE, n, HypRef("gt")),
            AndIntro(HypRef("gt"), apply_theorem(dvd_refl_theorem, n)),
        ),
        nonempty_goal,
    )
    occurrence = Least(ONE, least_m, predicate, nonempty)

    hm = HypRef("hm")
    membership_here = AndElimL(hm)
    not_m_lt_one = AndElimL(membership_here)
    m_properties = AndElimR(membership_here)
    m_gt_one = AndElimL(m_properties)
    m_dvd_n = AndElimR(m_properties)
    minimal = AndElimR(hm)

    d = Var("d", INT)
    proper = And(And(Lt(ONE, d), Lt(d, least_m)), divides(d, least_m))
    exists_proper = Exists(d, proper)

    hd = HypRef("hd")
    proper_here = AndElimL(hd)
    d_gt_one = AndElimL(proper_here)
    d_lt_m = AndElimR(proper_here)
    d_dvd_m = AndElimR(hd)
    d_dvd_n = ImpliesElim(
        ImpliesElim(apply_theorem(dvd_trans_theorem, d, least_m, n), d_dvd_m),
        m_dvd_n,
    )
    not_d_lt_one = not_lt_of_gt(ONE, d, d_gt_one)
    no_smaller = ImpliesElim(
        ForallElim(minimal, d), AndIntro(not_d_lt_one, d_lt_m))
    member = AndIntro(d_gt_one, d_dvd_n)
    contradiction = NotElim(no_smaller, member)
    proper_false = ExistsElim(HypRef("hex"), d, "hd", contradiction)
    no_proper = NotIntro(ImpliesIntro(exists_proper, "hex", proper_false))
    prime_m = AndIntro(m_gt_one, no_proper)

    p_var = Var("p", INT)
    target = Exists(p_var, And(prime(p_var), divides(p_var, n)))
    witness = AndIntro(prime_m, m_dvd_n)
    found = ExistsIntro(least_m, witness, target)
    existence = ExistsElim(occurrence, least_m, "hm", found)
    statement = Forall(n, Implies(Lt(ONE, n), target))
    theorem = logos.Theorem(statement, name="prime_factor")
    theorem.proof(t.exact(ForallIntro(n, ImpliesIntro(Lt(ONE, n), "gt", existence))))
    return theorem


# ── The theorem: infinitely many primes ─────────────────────────────────────

def build_infinitely_many_primes(
    factorial_pos_theorem,
    factorial_dvd_theorem,
    consecutive_theorem,
    not_dvd_one_theorem,
    prime_factor_theorem,
):
    n = Var("n", INT)
    tvar = Var("t", INT)
    target_prime = Var("p", INT)
    target = Exists(target_prime, And(prime(target_prime), Lt(n, target_prime)))

    # n >= 2 gives 1 < n.  First n is not below 1, then n is not equal to 1.
    not_n_lt_one = NotIntro(ImpliesIntro(Lt(n, ONE), "below",
        NotElim(HypRef("ge_two"),
                lt_trans(n, ONE, TWO, HypRef("below"), one_lt_two()))))
    not_one_eq_n = NotIntro(ImpliesIntro(Eq(ONE, n), "equal",
        NotElim(
            EqSubst(Symm(HypRef("equal")), tvar, Not(Lt(tvar, TWO)), HypRef("ge_two")),
            one_lt_two())))
    not_not_one_lt_n = NotIntro(ImpliesIntro(Not(Lt(ONE, n)), "not_above",
        NotElim(not_one_eq_n,
                eq_of_not_lt(ONE, n, HypRef("not_above"), not_n_lt_one))))
    n_gt_one = lt_dne(ONE, n, not_not_one_lt_n)

    zero_lt_n = lt_trans(ZERO, ONE, n, zero_lt_one(), n_gt_one)
    not_n_lt_zero = NotIntro(ImpliesIntro(Lt(n, ZERO), "below_zero",
        NotElim(lt_irrefl(ZERO),
                lt_trans(ZERO, n, ZERO, zero_lt_n, HypRef("below_zero")))))

    # n! is positive, so N = n! + 1 is greater than one.
    fact_positive = ImpliesElim(apply_theorem(factorial_pos_theorem, n), not_n_lt_zero)
    big = law("lt_add", (ZERO, factorial(n), ONE), fact_positive)
    N = factorial(n) + ONE

    # Take a prime factor p of N.
    factor_of_N = ImpliesElim(apply_theorem(prime_factor_theorem, N), big)
    p_var = Var("p", INT)
    hp = HypRef("hp")
    p_prime = AndElimL(hp)
    p_dvd_N = AndElimR(hp)
    p_gt_one = AndElimL(p_prime)

    # If p <= n then p divides n! and n! + 1, hence p divides 1.
    not_n_lt_p = NotIntro(ImpliesIntro(Not(Lt(n, p_var)), "at_most",
        NotElim(
            ImpliesElim(apply_theorem(not_dvd_one_theorem, p_var), p_gt_one),
            ImpliesElim(
                ImpliesElim(
                    apply_theorem(consecutive_theorem, factorial(n), p_var),
                    ImpliesElim(
                        ImpliesElim(
                            ForallElim(
                                ImpliesElim(apply_theorem(factorial_dvd_theorem, n),
                                            not_n_lt_zero),
                                p_var),
                            p_gt_one),
                        law("lt_succ_rev", (p_var, n), HypRef("at_most")))),
                p_dvd_N))))
    p_gt_n = lt_dne(n, p_var, not_n_lt_p)

    located = ExistsIntro(p_var, AndIntro(p_prime, p_gt_n), target)
    body = ExistsElim(factor_of_N, p_var, "hp", located)
    statement = Forall(n, Implies(Not(Lt(n, TWO)), target))
    theorem = logos.Theorem(statement, name="infinitely_many_primes")
    theorem.proof(t.exact(ForallIntro(n, ImpliesIntro(Not(Lt(n, TWO)), "ge_two", body))))
    return theorem


def build_all():
    """Build every lemma and the final theorem, in dependency order."""
    dvd_refl = build_dvd_refl()
    dvd_trans = build_dvd_trans()
    dvd_mul = build_dvd_mul()
    consecutive = build_consecutive_dvd_one()
    not_dvd_one = build_not_dvd_one_of_gt_one()
    factorial_pos = build_factorial_pos()
    factorial_dvd = build_factorial_dvd(dvd_mul)
    prime_factor = build_prime_factor(dvd_refl, dvd_trans)
    final = build_infinitely_many_primes(
        factorial_pos, factorial_dvd, consecutive, not_dvd_one, prime_factor
    )
    lemmas = [
        dvd_refl,
        dvd_trans,
        dvd_mul,
        consecutive,
        not_dvd_one,
        factorial_pos,
        factorial_dvd,
        prime_factor,
    ]
    return lemmas, final


def main(argv):
    output = argv[1] if len(argv) > 1 else "primes.logos"
    lemmas, final = build_all()
    for lemma in lemmas:
        lemma.check()
        print(f"checked {lemma.name}")
    final.check()
    logos.export_proof(final, output)
    print(f"wrote {output}")
    print("Exposition only: 30031 = 59 * 509.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
