import logos
from logos import Int, forall, lit
from logos.domains.number_theory import divides, divides_mul
factorial = logos.recursor("factorial", 1, lambda n, previous: (n + 1) * previous)
@logos.theorem
def factorial_positive(n: Int):
    """The factorial of a nonnegative integer is positive."""
    return ~(n < 0) >> (0 < factorial(n))

@factorial_positive.proof
def prove_factorial_positive(p, n):
    """Induct from 0! = 1 and close the step with a product of positives."""
    nonnegative = p.assume(~(n < 0))
    with p.induction(n, 0, nonnegative=nonnegative) as induction:
        with induction.base() as base:
            zero = p.recursor_base(factorial)  # 0! = 1
            base.finish(p.linear(0 < factorial(0), using=[zero]))
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
@logos.theorem
def mul_succ(k: Int, f: Int):
    """Multiplying by a successor distributes the successor."""
    return (k + 1) * f == f + k * f

@mul_succ.proof
def prove_mul_succ(p, k, f):
    """Expand the left side."""
    return p.ring((k + 1) * f == f + k * f)
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
            equation = p.recursor_step(factorial, k, not_k_below_zero)
            distributed = p.apply(mul_succ, k, factorial(k))
            decomposed = p.trans(equation, distributed)
            larger = p.apply(lt_add_pos, 1, factorial(k), k * factorial(k),
                             previous, product_positive)
            step.finish(p.subst(larger, p.symm(decomposed)))
    return induction.result
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
        with induction.step() as step:
            k = step.variable
            with p.fix("d") as fixed:
                d = fixed.variable
                above = p.assume(1 < d)
                bound = p.assume(d < (k + 1) + 1)
                p.note("Either d was already a divisor of k!, or d = k + 1.")
                decision = p.order("lt_decidable", d, k + 1)
                with p.cases(decision) as cases:
                    with cases.left() as smaller:
                        ih = p.apply(step.hypothesis, d, above, smaller)
                        multiplied = p.apply(
                            divides_mul, d, factorial(k), k + 1, ih
                        )
                        equation = p.recursor_step(
                            factorial, k, step.nonnegative
                        )
                        cases.finish(p.subst(multiplied, p.symm(equation)))
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
@logos.theorem
def two_divides_factorial(n: Int):
    return ~(n < 2) >> divides(2, factorial(n))


@two_divides_factorial.proof
def prove_two_divides_factorial(p, n):
    bound = p.assume(~(n < 2))
    two_le_n = p.order("not_lt_le", n, 2, using=[bound])
    positive = p.linear(0 < n, using=[two_le_n])
    nonnegative = p.not_lt_of_lt(0, n, positive)
    below = p.order("lt_succ_rev", 2, n, using=[bound])
    return p.apply(factorial_dvd, n, nonnegative, 2,
                   p.linear(lit(1) < lit(2)), below)


@logos.theorem
def divisor_of_next_factorial(n: Int, d: Int):
    return (2 <= d) >> ((d <= n) >> divides(d, factorial(n + 1)))


@divisor_of_next_factorial.proof
def prove_divisor_of_next_factorial(p, n, d):
    lower = p.assume(2 <= d)
    upper = p.assume(d <= n)
    positive = p.linear(0 < n + 1, using=[lower, upper])
    nonnegative = p.not_lt_of_lt(0, n + 1, positive)
    above_one = p.linear(1 < d, using=[lower])
    below = p.linear(d < (n + 1) + 1, using=[upper])
    return p.apply(factorial_dvd, n + 1, nonnegative, d, above_one, below)
