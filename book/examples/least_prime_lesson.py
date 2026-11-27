import logos
from logos import Int, exists, forall
from logos.domains.number_theory import divides, divides_self, divides_trans
@logos.definition
def prime(q: Int):
    """A prime is greater than one and has no divisor strictly between 1 and q."""
    return (1 < q) & ~exists(Int, lambda d:
        (1 < d) & ((d < q) & divides(d, q)))
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
    least = p.least(1, nonempty)
    q, properties = p.obtain(least)
    bounds = properties.left()
    q_properties = bounds.right()
    q_above_one = q_properties.left()
    q_dvd_m = q_properties.right()
    minimal = properties.right()
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
        not_below_one = p.not_lt_of_lt(1, d, d_above_one)
        smaller = p.and_intro(not_below_one, d_below_q)
        no_proper = p.apply(minimal, d, smaller)
        clash = p.not_elim(no_proper, p.and_intro(d_above_one, d_dvd_m))
        suppose.finish(clash)
    q_prime = p.and_intro(q_above_one, suppose.result)
    return p.witness(q, p.and_intro(q_prime, q_dvd_m))
@logos.theorem
def no_integer_between_one_and_two():
    return ~exists(Int, lambda d: (1 < d) & (d < 2))


@no_integer_between_one_and_two.proof
def prove_no_integer_between_one_and_two(p):
    with p.negate() as suppose:
        d, bounds = p.obtain(suppose.assumption)
        two_le_d = p.order("lt_succ_le", 1, d, using=[bounds.left()])
        suppose.finish(p.linear(False, using=[bounds.right(), two_le_d]))
    return suppose.result

@logos.theorem
def least_above(a: Int):
    return ~(a < 2) >> exists(Int, lambda q:
        (q == a + 1) & (
            (~(q < 0) & (a < q)) &
            forall(Int, lambda smaller:
                (~(smaller < 0) & (smaller < q)) >> ~(a < smaller))
        ))


@least_above.proof
def prove_least_above(p, a):
    at_least_two = p.assume(~(a < 2))
    two_le_a = p.order("not_lt_le", a, 2, using=[at_least_two])
    first = a + 1
    positive = p.linear(0 < first, using=[two_le_a])
    lower = p.not_lt_of_lt(0, first, positive)
    member = p.linear(a < first)
    nonempty = p.exists(
        exists(Int, lambda d: ~(d < 0) & (a < d)),
        first, p.and_intro(lower, member),
    )
    q, properties = p.obtain(p.least(0, nonempty))
    first_le_q = p.order("lt_succ_le", a, q,
                         using=[properties.left().right()])
    with p.negate(~(q < first)) as below:
        below.finish(p.linear(False, using=[first_le_q, below.assumption]))
    with p.negate(~(first < q)) as suppose:
        smaller = p.and_intro(lower, suppose.assumption)
        excluded = p.apply(properties.right(), first, smaller)
        suppose.finish(p.not_elim(excluded, member))
    equal = p.order("eq_of_not_lt_not_lt", q, first,
                    using=[below.result, suppose.result])
    return p.witness(q, p.and_intro(equal, properties))
