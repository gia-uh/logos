import logos
from logos import Int, exists
from logos.domains.number_theory import (
    check_all,
    common_divisor,
    factorial,
    factorial_above_one,
    factorial_dvd,
    least_prime_divisor,
    not_dvd_one,
    prime,
)
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
    q_prime = factor.left()
    q_dvd_m = factor.right()
    q_above_one = q_prime.left()
    with p.contradict(n < q) as contrary:
        not_n_lt_q = contrary.hypothesis
        q_lt_succ = p.order("lt_succ_rev", q, n, using=[not_n_lt_q])
        p.note("If q <= n then q divides n!, and by construction it divides n! + 1.")
        two_le_n = p.order("not_lt_le", n, 2, using=[at_least_two])
        zero_lt_n = p.linear(0 < n, using=[two_le_n])
        not_n_below_zero = p.not_lt_of_lt(0, n, zero_lt_n)
        q_dvd_f = p.apply(
            factorial_dvd, n, not_n_below_zero, q, q_above_one, q_lt_succ
        )
        neighbors = p.and_intro(q_dvd_f, q_dvd_m)
        divides_one = p.apply(common_divisor, q, f, neighbors)
        no_one = p.apply(not_dvd_one, q, q_above_one)
        contrary.finish(p.not_elim(no_one, divides_one))
    return p.witness(q, p.and_intro(q_prime, contrary.result))
@logos.theorem
def two_more_primes(n: Int):
    return ~(n < 2) >> exists(Int, lambda r:
        prime(r) & ((n < r) & exists(Int, lambda s:
            prime(s) & (r < s))))


@two_more_primes.proof
def prove_two_more_primes(p, n):
    bound = p.assume(~(n < 2))
    r, first = p.obtain(p.apply(euclid, n, bound))
    two_le_n = p.order("not_lt_le", n, 2, using=[bound])
    r_above_two = p.linear(2 < r, using=[two_le_n, first.right()])
    r_bound = p.not_lt_of_lt(2, r, r_above_two)
    next_prime, second = p.obtain(p.apply(euclid, r, r_bound))
    later = p.exists(
        exists(Int, lambda s: prime(s) & (r < s)), next_prime, second
    )
    return p.witness(r, p.and_intro(first.left(),
                                   p.and_intro(first.right(), later)))
