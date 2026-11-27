---
theme: book
title: One More Prime, Always
stem: euclid
---

# One More Prime, Always

Given an arbitrary integer $n\ge2$, construct a witness for

$$\exists q\in\mathbb{Z},\ \operatorname{prime}(q)\land n<q.$$

The least-divisor theorem gives a prime divisor of any integer above one. What remainder should that integer leave modulo each of $2,\ldots,n$ so none can divide it? First find a number divisible by all those integers. Then choose a remainder that also lets you use the consecutive-divisor lemma.

## Before you start

**Prerequisites.** Chapters 7 to 10. You need `divides_self`, `divides_mul`, `common_divisor`, `not_dvd_one`, `factorial_above_one`, `factorial_dvd` and `least_prime_divisor`, and you should be comfortable applying a lemma whose premise is a conjunction.

**Outcomes.** You will choose a candidate, obtain its prime divisor, justify why it exceeds the bound, read the failure the checker reports when the construction changes, and verify the exported certificate with the Rust checker.

## A concrete case first

The factorial $n!$ is divisible by each of $2,\ldots,n$. Adding one leaves remainder $1$ in every case. For $n=5$, this gives $121=11\times11$. The number is composite, and its prime divisor $11$ already meets our goal.

```python {run}
from math import factorial

number = factorial(5) + 1
print(number, "=", 11, "×", 11)
print("11 > 5:", 11 > 5)
```

## Compose the lemmas

Scriptorium assembles the fragments below in order into one Python module. The number theory module provides the same composition as `number_theory.euclid`.

First match the candidate $m$ to `least_prime_divisor`. Its premise is $1<m$. We have $n\ge2$, so `factorial_above_one` gives $1<n!$ and linear arithmetic gives $1<n!+1$. Open the resulting existential to get a prime divisor $q$, whose value the proof leaves symbolic.

```python {export=examples/euclid_lesson.py}
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
```

<!-- source: euclid_candidate -->
```python {export=examples/euclid_lesson.py}
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
```

The pair `factor` gives $\operatorname{prime}(q)$ and $q\mid m$. To finish with this witness we still need $n<q$. Why prove it indirectly? The opposite comparison tells us that $q$ is small enough to divide the factorial. Over the integers, $\neg(n<q)$ says $q\le n$, which the successor law converts to $q<n+1$.

<!-- source: euclid_contrary -->
```python {export=examples/euclid_lesson.py}
    q_prime = factor.left()
    q_dvd_m = factor.right()
    q_above_one = q_prime.left()
    with p.contradict(n < q) as contrary:
        not_n_lt_q = contrary.hypothesis
        q_lt_succ = p.order("lt_succ_rev", q, n, using=[not_n_lt_q])
        p.note("If q <= n then q divides n!, and by construction it divides n! + 1.")
```

`factorial_dvd` needs $\neg(n<0)$, $1<q$ and $q<n+1$ after its two integer arguments are instantiated. Which facts supply them? The original assumption gives $2\le n$, hence $0<n$ and then $\neg(n<0)$. Primality gives $1<q$. The contrary hypothesis supplies the last bound.

<!-- source: euclid_factorial -->
```python {export=examples/euclid_lesson.py}
        two_le_n = p.order("not_lt_le", n, 2, using=[at_least_two])
        zero_lt_n = p.linear(0 < n, using=[two_le_n])
        not_n_below_zero = p.not_lt_of_lt(0, n, zero_lt_n)
        q_dvd_f = p.apply(
            factorial_dvd, n, not_n_below_zero, q, q_above_one, q_lt_succ
        )
```

We now have $q\mid n!$ and $q\mid n!+1$. Pair them in that order for `common_divisor`. Its result $q\mid1$ conflicts with `not_dvd_one`, which uses the same $1<q$ we took from primality.

<!-- source: euclid_clash -->
```python {export=examples/euclid_lesson.py}
        neighbors = p.and_intro(q_dvd_f, q_dvd_m)
        divides_one = p.apply(common_divisor, q, f, neighbors)
        no_one = p.apply(not_dvd_one, q, q_above_one)
        contrary.finish(p.not_elim(no_one, divides_one))
```

Closing the contradiction gives $n<q$. Return $q$ with that inequality and the primality fact. The constructed number $m$ served as the input to the prime-divisor theorem.

<!-- source: euclid_witness -->
```python {export=examples/euclid_lesson.py}
    return p.witness(q, p.and_intro(q_prime, contrary.result))
```

## Certify and export

Check every lemma in the module, check the theorem, and write the portable certificate.

```python {run}
from examples.euclid_lesson import check_all, euclid, logos

check_all()
euclid.check()
print("euclid:", euclid.certified)
logos.export_proof(euclid, "euclid.logos")
print("certificate: euclid.logos")
```

The certificate is self-contained. The Rust checker needs neither Python nor the module:

```bash
logos check --strict euclid.logos
```

The expected last line is `Verified with 0 custom axioms`. The statement printed above it is

$$\forall n \in \mathbb{Z},\ \neg(n < 2) \rightarrow \exists q \in \mathbb{Z},\ \operatorname{prime}(q) \land n < q.$$

The theory is `logos-core-v1`. The certificate carries the statements and proofs of every lemma the theorem cites, directly or through another lemma, so a reader can audit each dependency. The book's tests run these commands from the installed wheel and compare the result.

## When a step fails

Change one line in the proof above: replace `m = f + 1` with `m = f` in the body of `prove_euclid`.

The proof still proves $1 < m$, because `above_f` is exactly $1 < n!$. It still finds a prime divisor $q$ of $m$. The failure comes later, at the application of the consecutive-divisor lemma: the proof has $q \mid n!$ twice, but the lemma expects $q \mid n!$ and $q \mid n! + 1$.

```text
the fact does not prove the antecedent needed by common_divisor
  expected: exists k:Int. factorial(n) = q * k & exists k:Int. factorial(n) + 1 = q * k
  got: exists k:Int. factorial(n) = q * k & exists k:Int. factorial(n) = q * k
  failing source: divides_one = p.apply(common_divisor, q, f, neighbors)
```

The message names the lemma, shows both conjunctions and points at the authored line. No certificate is written: the export happens after the check, and the check never returns. Restore `+ 1`, run the page again, and the certificate verifies.

The placement of the failure is the lesson. With only the weaker bound $0 < n!$, the altered construction $m = f$ would fail earlier, at `above_m`, and the message would be about linear arithmetic. The bound $1 < n!$ was chosen so that the construction, not the arithmetic, is what the checker catches.

## Exit exercise

1. Apply `euclid` twice to prove that for every $n\ge2$ there are two primes $r,s$ with $n<r<s$. State the nested existential, check your theorem and export its certificate. Identify where the first witness becomes an argument to the second application.
2. Try the construction $n!+2$. Predict the first lemma application that fails and state its required and supplied premises. Find a prime divisor of $4!+2$ and decide whether it exceeds the bound. Which property of the original construction is missing?

## Instructor solutions

To apply `euclid` at $r$, derive $\neg(r<2)$ from $2\le n<r$. The inner existential uses $s$ and the result of the second application. The outer existential packages $r$, its two original properties and the inner existential.

```python {export=examples/euclid_lesson.py}
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

```

```python {run continue}
from examples.euclid_lesson import two_more_primes

two_more_primes.check()
logos.export_proof(two_more_primes, "two-more-primes.logos")
print("two more primes:", two_more_primes.certified)
```

With $m=n!+2$, `common_divisor` is the first broken application. It requires $q\mid n!\land q\mid n!+1$, while the proof supplies $q\mid n!\land q\mid n!+2$. A common divisor of the altered pair can divide their difference $2$. At $n=4$ the candidate is $26=2\cdot13$, and its least prime divisor is $2\le4$.

## Read the portable proof {#what-the-reader-should-be-able-to-check}

Find where the checker opens the prime-divisor existential, and follow the two divisibility facts into the contradiction. The complete reading comes from the checker that accepted the certificate.

::: proof
```python {run continue echo=false}
print(euclid.inspect())
```
:::
