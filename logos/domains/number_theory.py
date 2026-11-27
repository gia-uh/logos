"""A small checked theory of divisibility, factorials and primes.

The module holds the transparent definitions and the lemmas that the book's
number theory chapters reuse.  Every lemma is an ordinary Logos theorem: the
proofers are Python functions using the same ``p`` tactics the chapters teach,
and the Rust checker rechecks the exported evidence.  Nothing here assumes a
result it has not checked.

Importing the module only builds symbolic statements and proof scripts.  Call
``check_all()`` (or ``theorem.check()``) with the ``logos`` checker on ``PATH``
to certify them, and ``logos.export_proof(euclid, path)`` to write the
portable certificate.

The derivations stay discoverable in two ways.  Each proof carries a short
docstring and ``p.note`` annotations that appear in ``theorem.inspect()``, and
the source is quoted section by section in the English book, whose tests fail
if the quoted code and this module drift apart.
"""
from __future__ import annotations

import logos
from logos import Int, exists, forall, lit

# --8<-- [start:divides]
@logos.definition
def divides(d: Int, a: Int):
    """d divides a when some integer k makes a equal to d * k."""
    return exists(Int, lambda k: a == d * k)
# --8<-- [end:divides]


# --8<-- [start:prime]
@logos.definition
def prime(q: Int):
    """A prime is greater than one and has no divisor strictly between 1 and q."""
    return (1 < q) & ~exists(Int, lambda d:
        (1 < d) & ((d < q) & divides(d, q)))
# --8<-- [end:prime]


# --8<-- [start:factorial]
factorial = logos.recursor("factorial", 1, lambda n, previous: (n + 1) * previous)
# --8<-- [end:factorial]


# --8<-- [start:divides_self]
@logos.theorem
def divides_self(d: Int):
    """Every integer divides itself."""
    return divides(d, d)

@divides_self.proof
def prove_divides_self(p, d):
    """The quotient is one."""
    product = p.ring(d == d * 1)
    return p.witness(1, product)
# --8<-- [end:divides_self]


# --8<-- [start:divides_trans]
@logos.theorem
def divides_trans(a: Int, b: Int, c: Int):
    """Divisibility is transitive."""
    return (divides(a, b) & divides(b, c)) >> divides(a, c)

@divides_trans.proof
def prove_divides_trans(p, a, b, c):
    """Multiply the two quotient equations."""
    both = p.assume(divides(a, b) & divides(b, c))
    k, ab = p.obtain(both.left())   # b = a * k
    j, bc = p.obtain(both.right())  # c = b * j
    ac = p.ring(c == a * (k * j), using=[ab, bc])
    return p.witness(k * j, ac)
# --8<-- [end:divides_trans]


# --8<-- [start:divides_mul]
@logos.theorem
def divides_mul(a: Int, b: Int, c: Int):
    """A multiple of b is still a multiple of any divisor of b."""
    return divides(a, b) >> divides(a, c * b)

@divides_mul.proof
def prove_divides_mul(p, a, b, c):
    """Scale the quotient by c."""
    ab = p.assume(divides(a, b))
    k, bk = p.obtain(ab)
    scaled = p.ring(c * b == a * (k * c), using=[bk])
    return p.witness(k * c, scaled)
# --8<-- [end:divides_mul]


# --8<-- [start:common_divisor]
@logos.theorem
def common_divisor(d: Int, a: Int):
    """A divisor of two consecutive integers divides one."""
    return (divides(d, a) & divides(d, a + 1)) >> divides(d, 1)

@common_divisor.proof
def prove_common_divisor(p, d, a):
    """Subtract the two quotient equations; the difference is one."""
    both = p.assume(divides(d, a) & divides(d, a + 1))
    k, left = p.obtain(both.left())   # a = d * k
    j, right = p.obtain(both.right()) # a + 1 = d * j
    quotient = j - k
    one = p.ring(1 == d * quotient, using=[left, right])
    return p.witness(quotient, one)
# --8<-- [end:common_divisor]


# --8<-- [start:not_dvd_one]
@logos.theorem
def not_dvd_one(d: Int):
    """No integer greater than one divides one."""
    return (1 < d) >> ~divides(d, 1)

@not_dvd_one.proof
def prove_not_dvd_one(p, d):
    """A product equal to one forces both factors to be 1 or -1."""
    above = p.assume(1 < d)
    with p.negate() as suppose:
        q, one_eq = p.obtain(suppose.assumption)
        p.note("A product equal to one has only 1 and -1 as factors.")
        product_one = p.symm(one_eq)
        split = p.order("mul_eq_one", d, q, using=[product_one])
        with p.cases(split) as cases:
            with cases.left() as d_one:
                cases.finish(p.linear(False, using=[above, d_one]))
            with cases.right() as d_minus_one:
                cases.finish(p.linear(False, using=[above, d_minus_one]))
        suppose.finish(cases.result)
    return suppose.result
# --8<-- [end:not_dvd_one]


# --8<-- [start:factorial_positive_setup]
@logos.theorem
def factorial_positive(n: Int):
    """The factorial of a nonnegative integer is positive."""
    return ~(n < 0) >> (0 < factorial(n))

@factorial_positive.proof
def prove_factorial_positive(p, n):
    """Induct from 0! = 1 and close the step with a product of positives."""
    nonnegative = p.assume(~(n < 0))
    with p.induction(n, 0, nonnegative=nonnegative) as induction:
        # --8<-- [end:factorial_positive_setup]
        # --8<-- [start:factorial_positive_base]
        with induction.base() as base:
            zero = p.recursor_base(factorial)  # 0! = 1
            base.finish(p.linear(0 < factorial(0), using=[zero]))
        # --8<-- [end:factorial_positive_base]
        # --8<-- [start:factorial_positive_step]
        with induction.step() as step:
            k = step.variable
            previous = step.hypothesis  # the induction hypothesis: 0 < k!
            successor = p.order("lt_succ_rev", 0, k, using=[step.nonnegative])
            p.note("The induction hypothesis is 0 < k!; the new factor k + 1 is positive.")
            product = p.order("mul_pos", k + 1, factorial(k),
                              using=[successor, previous])
            equation = p.recursor_step(factorial, k, step.nonnegative)
            step.finish(p.subst(product, p.symm(equation)))
    return induction.result
# --8<-- [end:factorial_positive_step]


# --8<-- [start:mul_succ]
@logos.theorem
def mul_succ(k: Int, f: Int):
    """Multiplying by a successor distributes the successor."""
    return (k + 1) * f == f + k * f

@mul_succ.proof
def prove_mul_succ(p, k, f):
    """Expand the left side."""
    return p.ring((k + 1) * f == f + k * f)
# --8<-- [end:mul_succ]


# --8<-- [start:lt_add_pos]
@logos.theorem
def lt_add_pos(a: Int, b: Int, c: Int):
    """Adding a positive integer keeps a strict inequality."""
    return (a < b) >> ((0 < c) >> (a < b + c))

@lt_add_pos.proof
def prove_lt_add_pos(p, a, b, c):
    """Linear arithmetic combines the two hypotheses."""
    below = p.assume(a < b)
    positive = p.assume(0 < c)
    return p.linear(a < b + c, using=[below, positive])
# --8<-- [end:lt_add_pos]


# --8<-- [start:factorial_above_one_base]
@logos.theorem
def factorial_above_one(n: Int):
    """From 2 onward the factorial is greater than one."""
    return ~(n < 2) >> (1 < factorial(n))

@factorial_above_one.proof
def prove_factorial_above_one(p, n):
    """Induct from 2! = 2 and add the positive term k * k!."""
    at_least_two = p.assume(~(n < 2))
    with p.induction(n, 2, nonnegative=at_least_two) as induction:
        with induction.base() as base:
            zero_lt_one = p.linear(lit(0) < lit(1))
            p.note("The base case computes 2! from the two recursor equations.")
            not_one_lt_zero = p.not_lt_of_lt(lit(0), lit(1), zero_lt_one)
            not_zero_lt_zero = p.order("lt_irrefl", 0)
            step0 = p.recursor_step(factorial, 0, not_zero_lt_zero)
            base_eq = p.recursor_base(factorial)
            step1 = p.recursor_step(factorial, 1, not_one_lt_zero)
            one_is = p.ring(lit(0) + lit(1) == lit(1))
            two_is = p.ring(lit(1) + lit(1) == lit(2))
            step0_one = p.subst(step0, one_is)
            step1_two = p.subst(step1, two_is)
            two_eq = p.ring(factorial(2) == 2,
                            using=[step1_two, step0_one, base_eq])
            base.finish(p.linear(lit(1) < factorial(2), using=[two_eq]))
        # --8<-- [end:factorial_above_one_base]
        # --8<-- [start:factorial_above_one_step]
        with induction.step() as step:
            k = step.variable
            previous = step.hypothesis
            # From 2 <= k we get 0 < k; k! is positive by the previous lemma.
            two_le_k = p.order("not_lt_le", k, 2, using=[step.nonnegative])
            p.note("Write (k + 1)! as k! + k * k!, a sum of a term above one and a positive term.")
            zero_lt_k = p.linear(0 < k, using=[two_le_k])
            not_k_below_zero = p.not_lt_of_lt(0, k, zero_lt_k)
            positive_factorial = p.apply(
                factorial_positive, k, not_k_below_zero
            )
            product_positive = p.order("mul_pos", k, factorial(k),
                                       using=[zero_lt_k, positive_factorial])
            # --8<-- [end:factorial_above_one_step]
            # --8<-- [start:factorial_above_one_sum]
            equation = p.recursor_step(factorial, k, not_k_below_zero)
            distributed = p.apply(mul_succ, k, factorial(k))
            decomposed = p.trans(equation, distributed)
            larger = p.apply(lt_add_pos, 1, factorial(k), k * factorial(k),
                             previous, product_positive)
            step.finish(p.subst(larger, p.symm(decomposed)))
    return induction.result
# --8<-- [end:factorial_above_one_sum]


# --8<-- [start:factorial_dvd_base]
@logos.theorem
def factorial_dvd(n: Int):
    """Every integer above one and at most n divides n!."""
    return ~(n < 0) >> forall(Int, lambda d:
        (1 < d) >> ((d < n + 1) >> divides(d, factorial(n))))

@factorial_dvd.proof
def prove_factorial_dvd(p, n):
    """Induct on n, splitting the new divisor into d < k + 1 and d = k + 1."""
    nonnegative = p.assume(~(n < 0))
    with p.induction(n, 0, nonnegative=nonnegative) as induction:
        with induction.base() as base:
            with p.fix("d") as fixed:
                d = fixed.variable
                above = p.assume(1 < d)
                p.note("At n = 0 no d satisfies 1 < d < 1.")
                below = p.assume(d < lit(0) + lit(1))
                clash = p.linear(False, using=[above, below])
                fixed.finish(p.ex_falso(clash))
            base.finish(fixed.result)
        # --8<-- [end:factorial_dvd_base]
        # --8<-- [start:factorial_dvd_split]
        with induction.step() as step:
            k = step.variable
            with p.fix("d") as fixed:
                d = fixed.variable
                above = p.assume(1 < d)
                bound = p.assume(d < (k + 1) + 1)
                p.note("Either d was already a divisor of k!, or d = k + 1.")
                decision = p.order("lt_decidable", d, k + 1)
                with p.cases(decision) as cases:
                    # --8<-- [end:factorial_dvd_split]
                    # --8<-- [start:factorial_dvd_old]
                    with cases.left() as smaller:
                        ih = p.apply(step.hypothesis, d, above, smaller)
                        multiplied = p.apply(
                            divides_mul, d, factorial(k), k + 1, ih
                        )
                        equation = p.recursor_step(
                            factorial, k, step.nonnegative
                        )
                        cases.finish(p.subst(multiplied, p.symm(equation)))
                    # --8<-- [end:factorial_dvd_old]
                    # --8<-- [start:factorial_dvd_new]
                    with cases.right() as not_smaller:
                        forward = p.order("lt_succ_fwd", d, k + 1,
                                          using=[bound])
                        equal = p.order("eq_of_not_lt_not_lt", d, k + 1,
                                        using=[not_smaller, forward])
                        equation = p.recursor_step(
                            factorial, k, step.nonnegative
                        )
                        same = p.refl(d * factorial(k))
                        moved = p.subst(same, equal)
                        joined = p.trans(equation, moved)
                        cases.finish(p.witness(factorial(k), joined))
                fixed.finish(cases.result)
            step.finish(fixed.result)
    return induction.result
# --8<-- [end:factorial_dvd_new]


# --8<-- [start:least_prime_input]
@logos.theorem
def least_prime_divisor(m: Int):
    """Every integer above one has a prime divisor."""
    return (1 < m) >> exists(Int, lambda q: prime(q) & divides(q, m))

@least_prime_divisor.proof
def prove_least_prime_divisor(p, m):
    """Take the least divisor above one; a proper divisor would contradict it."""
    above_one = p.assume(1 < m)
    self_divisor = p.apply(divides_self, m)
    not_m_below_one = p.not_lt_of_lt(1, m, above_one)
    p.note("m itself is a divisor above one, so the set is not empty.")
    member = p.and_intro(not_m_below_one, p.and_intro(above_one, self_divisor))
    nonempty = p.exists(
        exists(Int, lambda d: ~(d < 1) & ((1 < d) & divides(d, m))),
        m,
        member,
    )
    # --8<-- [end:least_prime_input]
    # --8<-- [start:least_prime_minimum]
    least = p.least(1, nonempty)
    q, properties = p.obtain(least)
    bounds = properties.left()
    q_properties = bounds.right()
    q_above_one = q_properties.left()
    q_dvd_m = q_properties.right()
    minimal = properties.right()
    # --8<-- [end:least_prime_minimum]
    # --8<-- [start:least_prime_proper]
    proper_exists = exists(Int, lambda d:
        (1 < d) & ((d < q) & divides(d, q)))
    with p.negate(~proper_exists) as suppose:
        d, proper = p.obtain(suppose.assumption)
        p.note("A proper divisor d of q also divides m, and it is smaller than q.")
        d_above_one = proper.left()
        d_below_q = proper.right().left()
        d_dvd_q = proper.right().right()
        d_dvd_m = p.apply(
            divides_trans, d, q, m,
            p.and_intro(d_dvd_q, q_dvd_m),
        )
        # --8<-- [end:least_prime_proper]
        # --8<-- [start:least_prime_clash]
        not_below_one = p.not_lt_of_lt(1, d, d_above_one)
        smaller = p.and_intro(not_below_one, d_below_q)
        no_proper = p.apply(minimal, d, smaller)
        clash = p.not_elim(no_proper, p.and_intro(d_above_one, d_dvd_m))
        suppose.finish(clash)
    # --8<-- [end:least_prime_clash]
    # --8<-- [start:least_prime_witness]
    q_prime = p.and_intro(q_above_one, suppose.result)
    return p.witness(q, p.and_intro(q_prime, q_dvd_m))
# --8<-- [end:least_prime_witness]


# --8<-- [start:euclid_candidate]
@logos.theorem
def euclid(n: Int):
    """For every n at least two there is a prime greater than n."""
    return ~(n < 2) >> exists(Int, lambda q: prime(q) & (n < q))

@euclid.proof
def prove_euclid(p, n):
    """Build n! + 1, take its least prime divisor and rule out q <= n."""
    at_least_two = p.assume(~(n < 2))
    f = factorial(n)
    p.note("1 < n! supplies the lower bound for the constructed number.")
    above_f = p.apply(factorial_above_one, n, at_least_two)
    m = f + 1
    above_m = p.linear(1 < m, using=[above_f])
    q, factor = p.obtain(p.apply(least_prime_divisor, m, above_m))
    # --8<-- [end:euclid_candidate]
    # --8<-- [start:euclid_contrary]
    q_prime = factor.left()
    q_dvd_m = factor.right()
    q_above_one = q_prime.left()
    with p.contradict(n < q) as contrary:
        not_n_lt_q = contrary.hypothesis
        q_lt_succ = p.order("lt_succ_rev", q, n, using=[not_n_lt_q])
        p.note("If q <= n then q divides n!, and by construction it divides n! + 1.")
        # --8<-- [end:euclid_contrary]
        # --8<-- [start:euclid_factorial]
        two_le_n = p.order("not_lt_le", n, 2, using=[at_least_two])
        zero_lt_n = p.linear(0 < n, using=[two_le_n])
        not_n_below_zero = p.not_lt_of_lt(0, n, zero_lt_n)
        q_dvd_f = p.apply(
            factorial_dvd, n, not_n_below_zero, q, q_above_one, q_lt_succ
        )
        # --8<-- [end:euclid_factorial]
        # --8<-- [start:euclid_clash]
        neighbors = p.and_intro(q_dvd_f, q_dvd_m)
        divides_one = p.apply(common_divisor, q, f, neighbors)
        no_one = p.apply(not_dvd_one, q, q_above_one)
        contrary.finish(p.not_elim(no_one, divides_one))
    # --8<-- [end:euclid_clash]
    # --8<-- [start:euclid_witness]
    return p.witness(q, p.and_intro(q_prime, contrary.result))
# --8<-- [end:euclid_witness]


LEMMAS = (
    divides_self,
    divides_trans,
    divides_mul,
    common_divisor,
    not_dvd_one,
    factorial_positive,
    mul_succ,
    lt_add_pos,
    factorial_above_one,
    factorial_dvd,
    least_prime_divisor,
    euclid,
)


def check_all() -> list[str]:
    """Check every lemma in dependency order and return their names."""
    for lemma in LEMMAS:
        lemma.check()
    return [lemma.name for lemma in LEMMAS]


def example() -> int:
    """A concrete case: five factorial plus one is 121, whose least prime factor is 11."""
    from math import factorial as python_factorial

    number = python_factorial(5) + 1
    assert number == 11 * 11
    return number
