---
theme: book
title: Induction That Builds a Factorial
stem: factorial
---

# Induction That Builds a Factorial

The factorial is the product of the first $n$ positive integers: $0! = 1$, $1! = 1$, $4! = 24$. It collects every small number into one, which is exactly what Euclid's argument needs. It is also the first function in the book with a recursive definition, and the first place where an induction hypothesis does real work.

This chapter defines the factorial by its two equations, proves that it is positive, proves that it is greater than one from $2$ onward, and proves that every integer between $2$ and $n$ divides $n!$. The last fact is the one that turns a common divisor into a contradiction.

## Before you start

**Prerequisites.** Chapters 7 and 8: transparent definitions, `p.obtain`, `p.witness`, `p.apply`, the transitive and scaling lemmas for divisibility, and the consecutive-divisor lemma.

**Outcomes.** You will read a primitive-recursive definition and its two equations, run an induction with a base scope and a step scope, use the induction hypothesis as an ordinary fact, rewrite a conclusion with a recursor equation, and prove a divisibility statement by induction with a case split in the step.

## Two equations define the factorial

The code fragments in this chapter are assembled in order into one Python module by Scriptorium.

A recursive function is not a loop in the checker. It is a name together with two equations that the checker accepts as defining laws: one at zero, and one that moves from $k$ to $k + 1$.

```python {export=examples/factorial_lesson.py}
import logos
from logos import Int, forall, lit
from logos.domains.number_theory import divides, divides_mul
```

<!-- source: factorial -->
```python {export=examples/factorial_lesson.py}
factorial = logos.recursor("factorial", 1, lambda n, previous: (n + 1) * previous)
```

In ordinary notation the equations are

$$0! = 1, \qquad (k + 1)! = (k + 1) \cdot k!.$$

The successor equation requires $\neg(k < 0)$. Logos treats `factorial(k)` as a symbolic term, so a proof that needs its value cites one of the equations.

## Positive at every nonnegative argument

Use induction because the successor equation reduces the desired inequality at $k+1$ to one at $k$. Give `p.induction` the variable in the goal, the first argument of the induction range, and evidence that the variable lies in that range. Here the second argument is $0$, so `nonnegative` must prove $\neg(n < 0)$. The keyword still names the lower-bound evidence when induction starts at another integer.

The first scope will owe $0 < 0!$. The second will owe $0 < (k+1)!$ for an arbitrary $k$, with `step.nonnegative` proving $\neg(k < 0)$ and `step.hypothesis` proving $0 < k!$.

<!-- source: factorial_positive_setup -->
```python {export=examples/factorial_lesson.py}
@logos.theorem
def factorial_positive(n: Int):
    """The factorial of a nonnegative integer is positive."""
    return ~(n < 0) >> (0 < factorial(n))

@factorial_positive.proof
def prove_factorial_positive(p, n):
    """Induct from 0! = 1 and close the step with a product of positives."""
    nonnegative = p.assume(~(n < 0))
    with p.induction(n, 0, nonnegative=nonnegative) as induction:
```

In the base scope, cite $0! = 1$ so linear arithmetic can prove the inequality.

<!-- source: factorial_positive_base -->
```python {export=examples/factorial_lesson.py}
        with induction.base() as base:
            zero = p.recursor_base(factorial)  # 0! = 1
            base.finish(p.linear(0 < factorial(0), using=[zero]))
```

In the step scope, derive $0 < k+1$ from the lower bound. The induction hypothesis gives the other positive factor, so `mul_pos` proves $0 < (k + 1)k!$. Which direction takes this fact to the goal? The recursor equation has the factorial on its left. Flip it so `p.subst` replaces the product with the factorial.

<!-- source: factorial_positive_step -->
```python {export=examples/factorial_lesson.py}
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
```

```python {run}
from examples.factorial_lesson import factorial_positive, factorial_above_one, factorial_dvd

factorial_positive.check()
print("factorial_positive:", factorial_positive.certified)
```

## Two identities for the next bound

The next theorem needs to see $(k + 1)!$ as a sum. Two small lemmas make the algebra explicit.

The first distributes a successor over a product. The second says that adding a positive integer to the right side of a strict inequality preserves it.

<!-- source: mul_succ -->
```python {export=examples/factorial_lesson.py}
@logos.theorem
def mul_succ(k: Int, f: Int):
    """Multiplying by a successor distributes the successor."""
    return (k + 1) * f == f + k * f

@mul_succ.proof
def prove_mul_succ(p, k, f):
    """Expand the left side."""
    return p.ring((k + 1) * f == f + k * f)
```

<!-- source: lt_add_pos -->
```python {export=examples/factorial_lesson.py}
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
```

Neither lemma is deep. They are named because the next proof uses them by name, and because naming them keeps the step readable: the checker records which lemma justified each rewrite.

## The factorial is greater than one

From $2$ onward, $n! > 1$. The base case computes $2! = 2$ from the two recursor equations. The step writes $(k + 1)!$ as $k! + k \cdot k!$: the first term is above one by the induction hypothesis, and the second is positive because $k \ge 2$.

Start induction at $2$. The base calculation follows $2! = 2\cdot1! = 2\cdot(1\cdot0!) = 2$. Cite `base_eq` for $0!=1$ and `step0` and `step1` for the two successor equations. Their factorial arguments are written as $0+1$ and $1+1$. Normalize those to $1$ and $2$ with `p.subst` so the factorial terms match across equations. Then `p.ring` combines the three equations into `two_eq`, and the base goal follows by linear arithmetic.

<!-- source: factorial_above_one_base -->
```python {export=examples/factorial_lesson.py}
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
```

In the step, $2 \le k$ gives $0 < k$, and the positivity theorem gives $0 < k!$. Together they make the extra term $k\cdot k!$ positive.

<!-- source: factorial_above_one_step -->
```python {export=examples/factorial_lesson.py}
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
```

The induction hypothesis already places $k!$ above one. Use `lt_add_pos` to add the extra term, then chain the recursor and distributive equations so the sum can be rewritten as $(k+1)!$.

<!-- source: factorial_above_one_sum -->
```python {export=examples/factorial_lesson.py}
            equation = p.recursor_step(factorial, k, not_k_below_zero)
            distributed = p.apply(mul_succ, k, factorial(k))
            decomposed = p.trans(equation, distributed)
            larger = p.apply(lt_add_pos, 1, factorial(k), k * factorial(k),
                             previous, product_positive)
            step.finish(p.subst(larger, p.symm(decomposed)))
    return induction.result
```

Certify the lemma.

```python {run continue}
factorial_above_one.check()
print("factorial_above_one:", factorial_above_one.certified)
```

The bound $1 < n!$ will let us apply the next chapter’s prime-divisor theorem to a number built from $n!$.

## Every small divisor divides the factorial

For every nonnegative $n$, every integer $d$ with $1 < d < n + 1$ divides $n!$. Induct on $n$, since the product gains one factor when $n$ advances. In the base scope, fix an arbitrary $d$ and assume its two bounds. At $n=0$ these imply $1 < d < 1$. Use the contradiction to finish the divisibility goal with `p.ex_falso`.

<!-- source: factorial_dvd_base -->
```python {export=examples/factorial_lesson.py}
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
```

In the step, compare the induction hypothesis’s bound $d < k+1$ with the new bound $d < (k+1)+1$. What integer is admitted only by the new bound? For $k=4$, the old values are $2,3,4$ and the new value is $5$. Test the old bound to decide whether the induction hypothesis applies.

<!-- source: factorial_dvd_split -->
```python {export=examples/factorial_lesson.py}
        with induction.step() as step:
            k = step.variable
            with p.fix("d") as fixed:
                d = fixed.variable
                above = p.assume(1 < d)
                bound = p.assume(d < (k + 1) + 1)
                p.note("Either d was already a divisor of k!, or d = k + 1.")
                decision = p.order("lt_decidable", d, k + 1)
                with p.cases(decision) as cases:
```

For $d < k+1$, the hypothesis gives $d\mid k!$. Multiply the dividend by $k+1$ with `divides_mul`, then rewrite it as $(k+1)!$.

<!-- source: factorial_dvd_old -->
```python {export=examples/factorial_lesson.py}
                    with cases.left() as smaller:
                        ih = p.apply(step.hypothesis, d, above, smaller)
                        multiplied = p.apply(
                            divides_mul, d, factorial(k), k + 1, ih
                        )
                        equation = p.recursor_step(
                            factorial, k, step.nonnegative
                        )
                        cases.finish(p.subst(multiplied, p.symm(equation)))
```

For $\neg(d < k+1)$, the new bound gives $\neg((k+1)<d)$ by the integer successor law. These comparisons force $d=k+1$. To find the witness, write $(k+1)!=(k+1)k!=d\cdot k!$. In the example the witness for $5\mid5!$ is $4!$. The code uses substitution to turn reflexivity of $d\cdot k!$ into the second equality in that chain.

<!-- source: factorial_dvd_new -->
```python {export=examples/factorial_lesson.py}
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
```

Certify the divisibility lemma.

```python {run continue}
factorial_dvd.check()
print("factorial_dvd:", factorial_dvd.certified)
```

Together with the previous lemmas, this is enough to say: if a prime $q$ is at most $n$, then $q$ divides $n!$. The final chapter uses exactly that sentence.

## When a step fails

The rewrite in `prove_factorial_positive` in `logos/domains/number_theory.py` depends on the direction of the recursor equation. Suppose the last line reads

```python
step.finish(p.subst(product, equation))
```

instead of `p.subst(product, p.symm(equation))`. The fact is $0 < (k + 1)k!$, and the equation is $(k + 1)! = (k + 1)k!$. `p.subst` looks for the left side of the equation inside the fact; the left side is `factorial(k + 1)`, which does not occur there.

```text
the equality's left side does not occur in the fact
  expected goal: 0 < factorial(k + 1)
  expected: factorial(k + 1)
  got: 0 < (k + 1) * factorial(k)
```

The message names the missing term and repeats the fact. Flip the equation with `p.symm` and the rewrite goes through. Read the direction of every `p.subst` as “replace this side by that side”.

A second mistake is to forget the hypothesis `~(k < 0)` when citing `p.recursor_step(factorial, k, ...)`. The step equation is only available for nonnegative arguments, and the checker will ask for the missing proof.

## Exit exercise

1. Prove $2\mid n!$ for every $n\ge2$. Use `factorial_dvd` and match its three premises to facts about $n$ and $2$.
2. For any integers $n$ and $d$ with $2\le d\le n$, prove $d\mid(n+1)!$. Decide whether to apply the existing theorem or start a new induction. Explain how the bounds in your proof support that choice.

## Instructor solutions

For the first claim, use the successor law on the assumed lower bound to get $2<n+1$. For the second, the given bounds already imply $n+1\ge0$, $1<d$, and $d<(n+1)+1$. Instantiate the same theorem at $n+1$.

```python {export=examples/factorial_lesson.py}
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

```

```python {run continue}
from examples.factorial_lesson import two_divides_factorial, divisor_of_next_factorial

two_divides_factorial.check()
divisor_of_next_factorial.check()
print("factorial exercises:", two_divides_factorial.certified,
      divisor_of_next_factorial.certified)
```
