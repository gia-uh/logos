---
theme: book
title: What Divides Two Neighbours
stem: neighbours
---

# What Divides Two Neighbours

If a number divides both $20$ and $21$, it also divides $1$. The only positive integer that divides $1$ is $1$ itself, so two consecutive integers share no positive divisor larger than one. The claim is easy to believe from one example; the proof has to work for every pair $a$ and $a + 1$.

The argument is short and it is the engine of Euclid's theorem. It combines two existential hypotheses into one witness, and it shows how a negation, a case split and an order law work together.

## Before you start

**Prerequisites.** Chapter 7: the transparent definition of `divides`, `p.assume`, `p.obtain`, `p.witness`, `p.ring`, and the lemmas `divides_self`, `divides_trans` and `divides_mul`.

**Outcomes.** You will subtract two quotient equations to build a new witness, read a proof by contradiction under a negation, split a disjunction produced by a core law, and apply a checked lemma whose premise is a conjunction. By the end you will have proved that a common divisor of consecutive integers divides one, and that no integer above one divides one.

## The difference is one

Suppose $d$ divides $a$ and $a + 1$. Write the two promises as equations:

$$a = dk, \qquad a + 1 = dj.$$

Subtract the first from the second. The left side is $(a + 1) - a = 1$, and the right side is $dj - dk = d(j - k)$. So $1 = d(j - k)$, and the witness for $d \mid 1$ is the difference of the two quotients.

The order of the subtraction matters. With $k - j$ the equation would read $1 = d(k - j)$, which is false for $d = 1$, $a = 4$: the witnesses are $k = 4$ and $j = 5$, and $1 \neq -1$. The lemma is true; the wrong witness is not.

<!-- source: common_divisor -->
```python
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
```

The proof opens both existentials, names the quotients `k` and `j`, and closes the goal with `j - k`. `p.ring` proves $1 = d(j - k)$ from the two equations; it does not choose the difference. The witness is the mathematical decision, and the checker verifies that the equation holds.

## A product of integers that equals one

The final step of Euclid's theorem needs a second fact: no integer greater than one divides one. If $d > 1$ and $1 = dq$, then $d$ and $q$ are integer factors of $1$. The only integer factorisations of $1$ are $1 \cdot 1$ and $(-1) \cdot (-1)$, so $d$ would be $1$ or $-1$, and neither is greater than one.

The proof is a contradiction. It assumes $d > 1$, opens the divisibility hypothesis, and splits the factorisation with the core law `mul_eq_one`. Each branch contradicts the order hypothesis.

<!-- source: not_dvd_one -->
```python
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
```

`p.negate()` proves a negation by assuming its positive statement. Inside the scope, `p.obtain` opens $1 = dq$ and names the quotient. `p.order("mul_eq_one", d, q, using=[product_one])` is a checked core law, not an assumption: it returns the disjunction $d = 1 \lor d = -1$. `p.cases` splits it into two scopes. In the first, $d = 1$ contradicts $1 < d$; in the second, $d = -1$ does the same. `p.linear(False, ...)` turns the pair of order facts into an explicit contradiction in each branch.

Notice that the negation is *inside* the implication. The statement is $(1 < d) \Rightarrow \neg(d \mid 1)$, not $\neg((1 < d) \Rightarrow d \mid 1)$. The first is true for every integer; the second would be false at $d = 2$.

Certify both lemmas.

```python {run}
import logos
from logos.domains import number_theory

for lemma in (number_theory.common_divisor, number_theory.not_dvd_one):
    lemma.check()
    print(f"{lemma.name}: {lemma.certified}")
```

## Apply the pair

The two lemmas are meant to be used together. Here is a small consequence: a common divisor of $a$ and $a + 1$ is never greater than one.

```python {run continue}
from logos import Int

@logos.theorem
def common_divisor_not_above_one(d: Int, a: Int):
    """A common divisor of two consecutive integers is not greater than one."""
    return (number_theory.divides(d, a) & number_theory.divides(d, a + 1)) >> ~(1 < d)

@common_divisor_not_above_one.proof
def prove_common_divisor_not_above_one(p, d, a):
    """A divisor above one would divide one, which is impossible."""
    both = p.assume(number_theory.divides(d, a) & number_theory.divides(d, a + 1))
    divides_one = p.apply(number_theory.common_divisor, d, a, both)
    with p.negate() as suppose:
        above = suppose.assumption
        no_one = p.apply(number_theory.not_dvd_one, d, above)
        suppose.finish(p.not_elim(no_one, divides_one))
    return suppose.result
```

The proof applies `common_divisor` to the conjunction of the two hypotheses, then `not_dvd_one` to the assumed bound. The two checked lemmas meet at $d \mid 1$. This is the pattern the final theorem repeats with $n!$ and $n! + 1$.

```python {run continue}
common_divisor_not_above_one.check()
print("common_divisor_not_above_one:", common_divisor_not_above_one.certified)
```

## When a step fails

Return to `common_divisor` in `logos/domains/number_theory.py` and change the witness in `prove_common_divisor` to the opposite difference:

```python
quotient = k - j
```

The goal is still $d \mid 1$, and both hypotheses are still open. What fails is the equation: the checker cannot connect $1$ with $d(k - j)$.

```text
ring could not connect the goal to the equations opened with 'using'
  expected goal: 1 = d * (k - j)
  opened hypotheses:
    left: a = d * k
    right: a + 1 = d * j
```

The message repeats the two equations and the goal. Substitute the right sides into $1 = (a + 1) - a$ and you get $d(j - k)$, not $d(k - j)$. Restore `j - k` and the lemma certifies again.

A second mistake is to assume the goal is $d \mid a$ instead of $d \mid 1$. The lemma's conclusion is fixed by its statement, so the proof would fail at the final `p.witness`, with the expected existential displayed.

## Exit exercise

Prove that a common divisor of $a$ and $b$ divides their difference:

$$(d \mid a \land d \mid b) \Rightarrow d \mid (a - b).$$

Open both existentials, choose $k - j$ or $j - k$ according to the order of the subtraction, and let `p.ring` check the equation. Write the equation on paper before you write the code; the sign is the only place the proof can go wrong.

As a second exercise, prove that a common divisor of $a$ and $b$ divides $a + b$. The witness is the sum of the quotients, and the same pattern applies without a case split.
