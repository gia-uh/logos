---
theme: book
title: One More Prime, Always
stem: euclid
---

# One More Prime, Always

Someone hands you a list of primes and says it is complete. You could search for the next one, but the list might be longer than your patience. Euclid's argument does something better: it uses the list itself to build a number that cannot be divided by any prime on the list.

The number is $n! + 1$, where $n$ is the largest number in the list. Every prime at most $n$ divides $n!$. If one of them also divides $n! + 1$, it divides their difference, which is $1$. No prime does that. So a prime outside the list exists.

By the end of this chapter you will have a checked theorem, a portable certificate, and a one-line change that breaks the proof at the exact place where the construction matters.

## Before you start

**Prerequisites.** Chapters 7 to 10. You need `divides_self`, `divides_mul`, `common_divisor`, `not_dvd_one`, `factorial_above_one`, `factorial_dvd` and `least_prime_divisor`, and you should be comfortable applying a lemma whose premise is a conjunction.

**Outcomes.** You will compose six named lemmas into one proof, choose a constructed number whose lower bound survives a deliberate mutation, read the failure the checker reports when the construction changes, and verify the exported certificate with the Rust checker.

## A concrete case first

Take the list $1, 2, 3, 4, 5$, so $n = 5$. The product of the list is $5! = 120$, and one more is $121$. The number is not prime, but that does not matter: it has a prime factor, and $11$ is greater than $5$.

```python {run}
from math import factorial

number = factorial(5) + 1
print(number, "=", 11, "×", 11)
print("11 > 5:", 11 > 5)
```

The example shows why the proof does not need $n! + 1$ to be prime. It needs one prime divisor, and the least-divisor theorem supplies one. The rest of the argument shows that this divisor cannot be small.

## Compose the lemmas

The theorem is stated for an arbitrary integer $n \ge 2$:

$$\neg(n < 2) \Rightarrow \exists q,\ \operatorname{prime}(q) \land n < q.$$

The proof imports the checked lemmas and writes the composition in the page, so you can take the construction apart. The code is the same proof that the number theory module packages as `number_theory.euclid`.

```python {run}
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

<!-- source: euclid -->
```python {run continue}
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
```

Read the proof in the order the facts are produced.

- `above_f` is $1 < n!$, from `factorial_above_one` and the hypothesis $2 \le n$. This is deliberately stronger than positivity: it is the bound that will survive when the constructed number changes.
- `m = f + 1` is the constructed number. `above_m` turns $1 < n!$ into $1 < n! + 1$ by linear arithmetic.
- `least_prime_divisor` applies to $m$ because $m > 1$. It returns a prime $q$ that divides $m$.
- The `p.contradict(n < q)` scope assumes the opposite, $q \le n$. From that, `q_lt_succ` gives $q < n + 1$, and `factorial_dvd` gives $q \mid n!$ because $q > 1$.
- `neighbors` packs $q \mid n!$ and $q \mid n! + 1$. `common_divisor` turns the pair into $q \mid 1$.
- `not_dvd_one` needs $1 < q$, which comes from the primality of $q$. The two facts contradict each other, and the contradiction proves $n < q$.
- The final witness is $q$ with its primality and the strict bound.

No step is a new axiom. Each line is either an application of a checked lemma or a core law, and the checker rechecks the dependencies in the certificate.

## Certify and export

Check every lemma in the module, check the theorem, and write the portable certificate.

```python {run continue}
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

## What the reader should be able to check

The page is the proof. The number theory module is the reusable copy, and the certificate is the artifact that leaves Python behind.

- Can you point to the line where the least prime divisor is chosen?
- Can you say why $q \le n$ implies $q \mid n!$?
- Can you say why $q \mid n!$ and $q \mid n! + 1$ contradict the primality of $q$?
- Can you run the two commands below and read the same statement back?

```bash
logos check --strict euclid.logos
logos inspect --strict euclid.logos
```

If the answers are yes, the chapter has done its job: a table of primes is never complete, and the argument that says so is checked by a program that does not know what a prime is beyond its definition.

## Exit exercise

Apply `euclid` twice. From $n \ge 2$ obtain a prime $p > n$; then apply the theorem at $p$ to obtain a prime $q > p$. State the result as

$$\neg(n < 2) \Rightarrow \exists p,\ \operatorname{prime}(p) \land n < p \land \exists q,\ \operatorname{prime}(q) \land p < q.$$

The proof is two `p.obtain` calls and one `p.witness` each time; `lt_trans` supplies $n < q$ if you also want to record it. Check the theorem and export its certificate. The interesting part is not the code but the reading: the second application of `euclid` is a checked lemma applied to a term that the first application produced.

As a second exercise, explain why the construction does not prove that $n! + 1$ is prime. The number $6! + 1 = 721 = 7 \cdot 103$ is a counterexample, and the theorem only needs a prime divisor of the constructed number, not the number itself.

