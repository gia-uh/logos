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

The code fragments in this chapter are assembled in order into one Python module by Scriptorium.

A prime is an integer greater than one with no divisor strictly between one and itself. The definition does not enumerate divisors; it says that a certain existential has no witness.

```python {export=examples/least_prime_lesson.py}
import logos
from logos import Int, exists, forall
from logos.domains.number_theory import divides, divides_self, divides_trans
```

<!-- source: prime -->
```python {export=examples/least_prime_lesson.py}
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

Choose the integers above one that divide $m$. For $m=91$, the set is $\{7,13,91\}$. Which value proves that the set is nonempty without factoring $91$?

`p.least(lower, nonempty)` expects an existential with a lower-bound conjunct and a membership predicate. With lower bound $1$, the exact input is

$$\exists d\in\mathbb{Z},\ \neg(d<1)\land((1<d)\land d\mid m).$$

Choose $m$ itself. The hypothesis $1<m$ supplies the membership inequality and, by asymmetry of strict order, $\neg(m<1)$. Reflexivity of divisibility supplies $m\mid m$. Pack the inner pair first, then add the lower bound. Would $1$ pass all three checks?

<!-- source: least_prime_input -->
```python {export=examples/least_prime_lesson.py}
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
```

Open the minimum to obtain $q$ and this grouped proposition. Here $P(x)$ abbreviates $(1<x)\land x\mid m$.

$$\bigl(\neg(q<1)\land P(q)\bigr)
\land
\bigl(\forall d\in\mathbb{Z},\ (\neg(d<1)\land d<q)\Rightarrow\neg P(d)\bigr).$$

The left projection is `bounds`, with membership `q_properties` on its right. Project from membership to get $1<q$ and $q\mid m$. The outer right projection is `minimal`. It rules out the predicate $P(d)$ once given the lower bound and the strict comparison with $q$.

<!-- source: least_prime_minimum -->
```python {export=examples/least_prime_lesson.py}
    least = p.least(1, nonempty)
    q, properties = p.obtain(least)
    bounds = properties.left()
    q_properties = bounds.right()
    q_above_one = q_properties.left()
    q_dvd_m = q_properties.right()
    minimal = properties.right()
```

We still owe the second conjunct of primality: the negation of a proper divisor’s existence. Assume such a divisor $d$ and unpack its properties. Which one is missing from $P(d)$? We have $d\mid q$, so use transitivity with $q\mid m$ to get $d\mid m$.

<!-- source: least_prime_proper -->
```python {export=examples/least_prime_lesson.py}
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
```

Apply `minimal` at $d$ with $\neg(d<1)\land d<q$. Its result is $\neg((1<d)\land d\mid m)$. Combine that with the positive membership we just established.

<!-- source: least_prime_clash -->
```python {export=examples/least_prime_lesson.py}
        not_below_one = p.not_lt_of_lt(1, d, d_above_one)
        smaller = p.and_intro(not_below_one, d_below_q)
        no_proper = p.apply(minimal, d, smaller)
        clash = p.not_elim(no_proper, p.and_intro(d_above_one, d_dvd_m))
        suppose.finish(clash)
```

The closed negation scope proves that $q$ has no proper divisor. Pair that with $1<q$ to prove primality. The witness for the theorem is $q$, with primality and the original fact $q\mid m$.

<!-- source: least_prime_witness -->
```python {export=examples/least_prime_lesson.py}
    q_prime = p.and_intro(q_above_one, suppose.result)
    return p.witness(q, p.and_intro(q_prime, q_dvd_m))
```

```python {run continue}
from examples.least_prime_lesson import least_prime_divisor

least_prime_divisor.check()
print("least_prime_divisor:", least_prime_divisor.certified)
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

## Exit exercise

1. Prove that no integer lies strictly between one and two. Explain which inference needs the integer domain. The rational number $1.5$ satisfies both inequalities.
2. Given an integer $a\ge2$, consider the positive integers strictly above $a$. Prove that their least member is $a+1$. Use $0$ as the lower bound, choose a membership predicate and find a nonempty witness. Explain how to exclude a smaller minimum and how to use minimality if the returned value exceeds $a+1$.

## Instructor solutions

For the first proof, use the integer successor law on $1<d$ to get $2\le d$. Now linear arithmetic can reject $d<2\le d$.

```python {export=examples/least_prime_lesson.py}
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

```

```python {run continue}
from examples.least_prime_lesson import no_integer_between_one_and_two

no_integer_between_one_and_two.check()
print("integer gap:", no_integer_between_one_and_two.certified)
```

Choose $P(d)$ to be $a<d$. With $a\ge2$, the witness $a+1$ is above both $a$ and the lower bound $0$. The minimum's membership gives $a<q$, so the integer successor law gives $\neg(q<a+1)$. If $a+1<q$, minimality rules out $P(a+1)$, contradicting the evidence used for nonemptiness.

```python {export=examples/least_prime_lesson.py}
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
```

```python {run continue}
from examples.least_prime_lesson import least_above

least_above.check()
print("least above:", least_above.certified)
```
