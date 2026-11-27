---
theme: book
title: The Smallest Divisor
stem: least-prime
---

# The Smallest Divisor

The divisors of $91$ are $1$, $7$, $13$ and $91$. The smallest one above $1$ is $7$, and $7$ is prime. That is not a coincidence. If the smallest divisor above $1$ had a proper divisor, that smaller number would also divide the original, contradicting the choice.

This chapter turns that observation into a theorem: every integer above one has a prime divisor. It is the first proof in the book that uses a minimum, and the first definition with a negated existential inside it.

## Before you start

**Prerequisites.** Chapters 7 to 9: divisibility, transitivity, contradiction under a negation, case splits, and the induction machinery of the factorial chapter.

**Outcomes.** You will read a definition that forbids a witness, use `p.least` to choose the smallest member of a nonempty set of integers, apply the minimality property to a smaller candidate, and prove a statement by deriving a contradiction from its negation. By the end you will have proved that every integer above one has a prime divisor.

## Primes are defined by what they lack

A prime is an integer greater than one with no divisor strictly between one and itself. The definition does not enumerate divisors; it says that a certain existential has no witness.

<!-- source: prime -->
```python
@logos.definition
def prime(q: Int):
    """A prime is greater than one and has no divisor strictly between 1 and q."""
    return (1 < q) & ~exists(Int, lambda d:
        (1 < d) & ((d < q) & divides(d, q)))
```

The body is a conjunction. The first conjunct, $1 < q$, rules out $0$, $1$ and the negative integers. The second is the negation of “there is a $d$ with $1 < d$, $d < q$, and $d \mid q$”. Together they say: $q$ is above one, and no divisor lies strictly between one and $q$.

The definition is transparent, so `prime(q)` unfolds to this body whenever the checker compares statements. Proving `prime(q)` means proving the conjunction; using it means unpacking the two parts.

A concrete look at the divisors of $91$ prepares the proof. This block computes, it does not prove.

```python {run}
number = 91
divisors = [d for d in range(2, number + 1) if number % d == 0]
print("divisors above one:", divisors)
print("least:", divisors[0])
```

The computation says $7$ is the least divisor above one. The proof has to say why the least divisor of *any* $m > 1$ must be prime, without listing anything.

## The least member of a nonempty set

The proof uses a core rule: every nonempty set of integers bounded below has a least member. In Logos the rule is `p.least(lower, nonempty)`. It returns an integer $q$ together with two facts:

1. $q$ belongs to the set;
2. no member of the set is strictly below $q$.

The set here is “divisors of $m$ above one”, written

$$\{\,d : \neg(d < 1) \ \land\ 1 < d \ \land\ d \mid m\,\}.$$

The bound $\neg(d < 1)$ is part of the set description because the least principle is stated for integers bounded below; the real membership condition is the conjunction after it.

The set is not empty: $m$ itself is a divisor of $m$ and $1 < m$. That is the witness the proof offers before calling `p.least`.

<!-- source: least_prime_divisor -->
```python
@logos.theorem
def least_prime_divisor(m: Int):
    """Every integer above one has a prime divisor."""
    return (1 < m) >> exists(Int, lambda q: prime(q) & divides(q, m))

@least_prime_divisor.proof
def prove_least_prime_divisor(p, m):
    """Take the least divisor above one; a proper divisor would contradict it."""
    above_one = p.assume(1 < m)
    self_divisor = p.apply(divides_self, m)
    below_one = p.not_lt_of_lt(1, m, above_one)
    p.note("m itself is a divisor above one, so the set is not empty.")
    member = p.and_intro(below_one, p.and_intro(above_one, self_divisor))
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
```

Read the proof in four movements.

- **Membership.** `self_divisor` is $m \mid m$ from `divides_self`. `below_one` is $\neg(m < 1)$, which follows from $1 < m$. `member` packs the three conjuncts, and `p.exists` offers $m$ as a witness that the set is nonempty.
- **The minimum.** `p.least(1, nonempty)` returns $q$ and its two properties. `p.obtain` names them. `q_properties` gives $1 < q$ and $q \mid m$; `minimal` is the statement that nothing smaller belongs.
- **The contradiction.** Suppose $q$ has a proper divisor $d$, so $1 < d$, $d < q$ and $d \mid q$. Transitivity gives $d \mid m$. Then $d$ is a member of the set, and it is below $q$. The minimality property forbids exactly that.
- **The witness.** The contradiction proves that no proper divisor exists, so `prime(q)` holds. The final `p.witness` returns $q$ with its primality and its divisibility of $m$.

The minimality application is the delicate line:

```python
smaller = p.and_intro(not_below_one, d_below_q)
no_proper = p.apply(minimal, d, smaller)
```

`minimal` expects the lower bound and the comparison with $q$, in that order. The fact it returns is the negation of membership, which is why the next line can combine it with the membership of $d$ to obtain a contradiction.

Certify the theorem.

```python {run}
import logos
from logos.domains import number_theory

number_theory.least_prime_divisor.check()
print("least_prime_divisor:", number_theory.least_prime_divisor.certified)
```

## When a step fails

The contradiction needs $d \mid m$, not $d \mid q$. In `prove_least_prime_divisor` in `logos/domains/number_theory.py`, suppose the last line used the divisor of $q$:

```python
clash = p.not_elim(no_proper, p.and_intro(d_above_one, d_dvd_q))
```

The two facts are true, but the minimality property is about the set of divisors of $m$. The membership it negates is $1 < d \land d \mid m$, and $d \mid q$ is a different proposition.

```text
the evidence does not prove the expected statement
  expected: 1 < d & exists k:Int. m = d * k
  got: 1 < d & exists k:Int. q = d * k
```

The message names both conjunctions. Transitivity is what turns $d \mid q$ and $q \mid m$ into $d \mid m$; without that step, the smaller candidate is not in the set. Restore `d_dvd_m` and the theorem certifies again.

A second mistake is to call `p.least` before proving that the set is nonempty. The rule needs the witness, and the checker will ask for the missing fact rather than choose $m$ for you.

## Exit exercise

Prove that no integer lies strictly between one and two:

$$\neg\exists d \in \mathbb{Z},\ 1 < d \land d < 2.$$

Open the negation with `p.negate()`, obtain the supposed $d$, and use `lt_succ_le` at $1$ and $d$ to turn $1 < d$ into $2 \le d$. Then $d < 2 \le d$ gives $d < d$ by `lt_le_trans`, which contradicts `lt_irrefl`.

Why not let `p.linear` do it? Linear arithmetic reasons over the rationals, where $1.5$ satisfies both bounds. Integrality comes from the successor law, and this exercise is the smallest place where that difference matters.

As a second exercise, prove that every integer above one has a divisor that is at least two. Apply `least_prime_divisor` and unpack the prime's first conjunct. The proof is three lines and it checks that you can read a conjunction out of an existential.
