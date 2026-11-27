---
theme: book
title: What Divides Two Neighbours
stem: neighbours
---

# What Divides Two Neighbours

If a number divides both $20$ and $21$, it also divides $1$. The only positive integer that divides $1$ is $1$ itself, so two consecutive integers share no positive divisor larger than one. The claim is easy to believe from one example; the proof has to work for every pair $a$ and $a + 1$.

The argument is short and it is the engine of Euclid's theorem. It combines two existential hypotheses into one witness, and it shows how a negation, a case split and an order law work together.

## Before you start

**Prerequisites.** Chapters 4–7: case splits, transparent divisibility, quotients from `p.obtain`, and matching a checked lemma to a goal with `p.apply`.

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

After assuming `above: 1 < d`, the goal is `~divides(d, 1)`. Enter `p.negate()` to assume `divides(d, 1)` temporarily and aim for `False`.

Opening that temporary assumption gives `one_eq: 1 == d * q`. The checked core law `mul_eq_one`, at $d$ and $q$, needs `d * q == 1` and gives `(d == 1) | (d == -1)`. Compare the two equations before reading the proof. Which direction does the law need? Use `p.symm(one_eq)` to put the product on the left.

With the disjunction in hand, aim for `False` in each branch. Both $d = 1$ and $d = -1$ conflict with $1 < d$, so each `cases.finish` receives its own contradiction proved by `p.linear`. Keep track of the result at each scope boundary.

- **Inside a branch**, `False` follows using that branch's equality.
- **After the case split**, `cases.result` proves `False` without either branch equality. It still depends on the temporary divisibility assumption. Pass it to `suppose.finish`.
- **After the negation scope**, `suppose.result` proves `~divides(d, 1)` under `above`. This is the fact the proof function returns.

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

Certify both lemmas.

```python {run}
import logos
from logos.domains import number_theory

for lemma in (number_theory.common_divisor, number_theory.not_dvd_one):
    lemma.check()
    print(f"{lemma.name}: {lemma.certified}")
```

## Apply the pair

Suppose `both` proves that $d$ divides $a$ and $a+1$. To prove `~(1 < d)`, assume `above: 1 < d` in a negation scope and look for a contradiction. Which of our lemmas give opposite facts about the same proposition?

- `common_divisor` at $d,a$ gives $(d \mid a \land d \mid (a+1)) \Rightarrow d \mid 1$. Pass the whole conjunction `both`, which is the single premise.
- `not_dvd_one` at $d$ gives $(1 < d) \Rightarrow \neg(d \mid 1)$. Pass `above` to discharge its premise.

The resulting facts are `divides_one: divides(d, 1)` and `no_one: ~divides(d, 1)`. Give the negative fact and then the positive fact to `p.not_elim` to derive `False`. Closing the negation scope discharges `above` and gives `~(1 < d)`.

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

The Euclid chapter uses the same pair with $n!$ and $n! + 1$.

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

## Exit exercise

1. Prove $(d \mid a \land d \mid b) \Rightarrow d \mid (a-b)$. Write the equation your witness must satisfy before writing Python.
2. Suppose $1 < d$. Prove $\neg(d \mid (a+1) \land d \mid a)$ using the two lemmas. Write the premise and result of each application, identify the contradictory pair, and say which proposition survives the negation scope.

## Instructor solutions

For the difference, subtract $b = dj$ from $a = dk$. The goal needs $a-b = d(k-j)$.

```python {run continue}
divides = number_theory.divides

@logos.theorem
def divides_difference(d: Int, a: Int, b: Int):
    return (divides(d, a) & divides(d, b)) >> divides(d, a - b)

@divides_difference.proof
def prove_divides_difference(p, d, a, b):
    both = p.assume(divides(d, a) & divides(d, b))
    k, a_eq = p.obtain(both.left())
    j, b_eq = p.obtain(both.right())
    difference = p.ring(a - b == d * (k - j), using=[a_eq, b_eq])
    return p.witness(k - j, difference)

divides_difference.check()
print(f"{divides_difference.name}: {divides_difference.certified}")
```

In the second proof, the temporary conjunction has the neighbours in reverse order. Rebuild it with $d \mid a$ first to obtain $d \mid 1$ from `common_divisor`. The outer assumption $1 < d$ already gives $\neg(d \mid 1)$ via `not_dvd_one`. The contradiction discharges the temporary conjunction, so the negation of that conjunction comes out of the scope.

```python {run continue}
@logos.theorem
def no_common_divisor_above_one(d: Int, a: Int):
    return (1 < d) >> ~(divides(d, a + 1) & divides(d, a))

@no_common_divisor_above_one.proof
def prove_no_common_divisor_above_one(p, d, a):
    above = p.assume(1 < d)
    no_one = p.apply(number_theory.not_dvd_one, d, above)
    with p.negate() as suppose:
        reversed_pair = suppose.assumption
        both = p.and_intro(reversed_pair.right(), reversed_pair.left())
        divides_one = p.apply(number_theory.common_divisor, d, a, both)
        suppose.finish(p.not_elim(no_one, divides_one))
    return suppose.result

no_common_divisor_above_one.check()
print(f"{no_common_divisor_above_one.name}: {no_common_divisor_above_one.certified}")
```
