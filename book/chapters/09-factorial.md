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

A recursive function is not a loop in the checker. It is a name together with two equations that the checker accepts as defining laws: one at zero, and one that moves from $k$ to $k + 1$.

<!-- source: factorial -->
```python
factorial = logos.recursor("factorial", 1, lambda n, previous: (n + 1) * previous)
```

In ordinary notation the equations are

$$0! = 1, \qquad (k + 1)! = (k + 1) \cdot k!.$$

The second equation is only claimed for nonnegative $k$, which is why every use of it carries a proof of $\neg(k < 0)$. The function is opaque to conversion: the checker will not evaluate `factorial(5)` by itself. A proof that needs a value must cite one of the two equations.

## Positive at every nonnegative argument

The base case is the first equation. The step multiplies two positive integers: $k + 1$ is positive because $k \ge 0$, and $k!$ is positive by the induction hypothesis. The product is $(k + 1)!$ by the second equation.

<!-- source: factorial_positive -->
```python
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
```

Three pieces are visible. `induction.base()` is the scope for $n = 0$; `p.recursor_base(factorial)` cites $0! = 1$, and linear arithmetic turns it into $0 < 0!$. `induction.step()` gives an arbitrary $k$, the hypothesis $\neg(k < 0)$, and the induction hypothesis `previous`, which is $0 < k!$. `p.order("mul_pos", ...)` multiplies the two positive facts, and `p.subst(product, p.symm(equation))` rewrites the product into $0 < (k + 1)!$ using the step equation read right to left.

The direction of the rewrite matters. The equation is $(k + 1)! = (k + 1)k!$; the fact is about $(k + 1)k!$. `p.symm` flips the equation so that the product on the left is replaced by the factorial on the right.

```python {run}
import logos
from logos import Int, lit
from logos.domains import number_theory

number_theory.factorial_positive.check()
print("factorial_positive:", number_theory.factorial_positive.certified)
```

## Two identities for the next bound

The next theorem needs to see $(k + 1)!$ as a sum. Two small lemmas make the algebra explicit.

The first distributes a successor over a product. The second says that adding a positive integer to the right side of a strict inequality preserves it.

<!-- source: mul_succ -->
```python
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
```python
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

The proof of the lemma is one function. The page shows its base half first.

<!-- source: factorial_above_one_base -->
```python
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

The base case is longer than it looks because the checker does not evaluate `factorial(2)` for us. We cite $0! = 1$, the step at $0$, and the step at $1$, and combine them with `p.ring` into $2! = 2$. The last line turns that equation into $1 < 2!$ by linear arithmetic. This is what “the checker only knows the equations” means in practice.

The step half follows.

<!-- source: factorial_above_one_step -->
```python
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
```

Read the step from the bottom up. `larger` says $1 < k! + k \cdot k!$: the induction hypothesis puts $k!$ above one, and `mul_pos` puts $k \cdot k!$ above zero. `decomposed` is the equation $(k + 1)! = k! + k \cdot k!$, obtained by chaining the recursor equation with `mul_succ`. The final `p.subst` carries the inequality across that equation.

Certify the lemma.

```python {run continue}
number_theory.factorial_above_one.check()
print("factorial_above_one:", number_theory.factorial_above_one.certified)
```

The bound $1 < n!$ is stronger than positivity, and the difference will matter in the final chapter. When the constructed number is $n! + 1$, the bound $1 < n!$ still proves $1 < n! + 1$ after the construction is altered. That is what makes the negative control fail later rather than earlier.

## Every small divisor divides the factorial

Now the divisibility statement. For every nonnegative $n$, every integer $d$ with $1 < d < n + 1$ divides $n!$. The induction is on $n$, and the step splits on whether $d$ was already below $k + 1$.

The base case has no divisor to find: $1 < d < 1$ is impossible.

<!-- source: factorial_dvd_base -->
```python
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

The proof fixes an arbitrary $d$ with `p.fix("d")`, assumes the two bounds, and derives a contradiction with `p.linear`. `p.ex_falso` turns the contradiction into the divisibility goal, which is the standard way to prove anything from a false premise.

The step half is the interesting one.

<!-- source: factorial_dvd_step -->
```python
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
```

After `p.fix("d")` and the two assumptions, the proof splits on `p.order("lt_decidable", d, k + 1)`, a checked instance of $d < k + 1 \lor \neg(d < k + 1)$.

- In the left branch, $d < k + 1$. The induction hypothesis applies at $d$, giving $d \mid k!$. `divides_mul` scales the dividend by $k + 1$, giving $d \mid (k + 1)k!$, and the recursor equation rewrites that into $d \mid (k + 1)!$.
- In the right branch, $\neg(d < k + 1)$, while the assumed bound is $d < (k + 1) + 1$. The two together give $d = k + 1$: `lt_succ_fwd` gives $\neg((k + 1) < d)$, and `eq_of_not_lt_not_lt` turns the two non-strict comparisons into equality. The witness for $d \mid (k + 1)!$ is then $k!$, because $(k + 1)! = (k + 1)k! = d \cdot k!$.

The branch that looks harder is the one where $d$ is exactly the new factor. The witness is already in the equation; the work is naming the equality.

Certify the divisibility lemma.

```python {run continue}
number_theory.factorial_dvd.check()
print("factorial_dvd:", number_theory.factorial_dvd.certified)
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

Prove that two divides $n!$ for every $n \ge 2$:

$$\neg(n < 2) \Rightarrow 2 \mid n!.$$

Apply `factorial_dvd` at $n$, with $d = 2$. You need three facts: $\neg(n < 0)$, $1 < 2$, and $2 < n + 1$. The last one follows from $\neg(n < 2)$ by `lt_succ_rev`. The first follows from `not_lt_le` and linear arithmetic. Write the five arguments of the application in the order the lemma expects, then check the theorem.

As a second exercise, prove that $3$ divides $n!$ for every $n \ge 3$. The same lemma applies at $d = 3$; the only new work is the bound $3 < n + 1$. Compare the proof with the one for $2$ and notice that nothing in `factorial_dvd` had to change.
