---
theme: book
title: Even, Odd, and What Divides Means
stem: parity
---

# Even, Odd, and What Divides Means

Is $2^{10} + 1$ even? You can compute it. A proof has to answer the same question for a letter $a$, without knowing which integer it names. Number theory begins when we stop computing examples and start describing the shape of a number: one quotient, one remainder, one product. This chapter builds the first two shapes, *divides* and *even*, and the three lemmas the rest of the sequence reuses.

## Before you start

**Prerequisites.** Chapters 1 to 6. You should be comfortable with `p.assume`, `p.obtain`, `p.witness`, `p.ring`, and with a transparent definition whose body is an existential.

**Outcomes.** You will read a divisibility definition as a promise of a quotient, prove a parity statement by choosing a witness, declare a definition of your own, and apply a checked lemma by name. By the end you will have proved that the sum of two even integers is even and that the successor of an even integer is odd.

## A divisor is a quotient you can name

“$d$ divides $a$” means that $a$ is $d$ times something. The something is an integer, and naming it is the whole proof obligation.

<!-- source: divides -->
```python
@logos.definition
def divides(d: Int, a: Int):
    """d divides a when some integer k makes a equal to d * k."""
    return exists(Int, lambda k: a == d * k)
```

The body is an existential over the integers. Calling `divides(3, 21)` builds the proposition

$$\exists k \in \mathbb{Z},\quad 21 = 3k,$$

not the Python value `True`. The definition is transparent, so the checker may replace the name by this body whenever it compares two statements. It is not an assumption: no axiom was declared, and the body is part of the certificate.

Three small cases fix the reading.

- $3 \mid 21$, because $21 = 3 \cdot 7$. The witness is $7$.
- $5 \mid 0$, because $0 = 5 \cdot 0$. The witness is $0$; zero is a multiple of everything.
- $2 \nmid 7$, because no integer $k$ makes $7 = 2k$.

The quotient is an integer, so it may be negative. The statement $3 \mid -21$ is true with witness $-7$. Do not read “divides” as “is smaller than”: $-21$ is a multiple of $3$ even though it is smaller than $3$.

The definition lives in a small module that the number theory chapters share:

```python {run}
import logos
from logos import Int, exists
from logos.expr import Var
from logos.domains import number_theory

divides = number_theory.divides
d = Var("d", int)
print(logos.format_expr(divides(d, 21)))
print(logos.format_expr(divides(3, 21)))
```

The first line keeps the name `divides`, because `d` is symbolic. The second line unfolds the body, because both arguments are concrete integers: calling a definition on numbers evaluates the Python function that described it. Neither line checks anything; both build a proposition.

## Even means divisible by two

A definition is a name for a body, and you may introduce one whenever the name will make the next proofs shorter. Here two of them pay for themselves.

```python {run continue}
@logos.definition
def even(n: Int):
    """n is even when two divides it."""
    return divides(2, n)

@logos.definition
def odd(n: Int):
    """n is odd when it is one more than a multiple of two."""
    return exists(Int, lambda k: n == 2 * k + 1)
```

`even` does not introduce a new mathematical idea. It is `divides(2, n)` under a shorter name, and the checker unfolds it whenever it needs the existential. `odd` is a different body: it asks for an integer $k$ with $n = 2k + 1$. An integer cannot be both even and odd, but we do not need that fact here.

Now the first proof. If $a = 2i$ and $b = 2j$, the sum is $2(i + j)$. The witness is the sum of the two halves.

```python {run continue}
@logos.theorem
def even_sum(a: Int, b: Int):
    """The sum of two even integers is even."""
    return (even(a) & even(b)) >> even(a + b)

@even_sum.proof
def prove_even_sum(p, a, b):
    """Add the two halves."""
    both = p.assume(even(a) & even(b))
    i, a_eq = p.obtain(both.left())
    j, b_eq = p.obtain(both.right())
    total = p.ring(a + b == 2 * (i + j), using=[a_eq, b_eq])
    return p.witness(i + j, total)
```

Read the four steps in order. `p.assume` enters the antecedent and leaves the goal `even(a + b)`. `p.obtain` unfolds `even(a)` and `even(b)` into the equalities $a = 2i$ and $b = 2j$, naming the witnesses. `p.ring` proves the equation the new witness must satisfy. `p.witness` closes `even(a + b)` by offering $i + j$; the checker unfolds `even` again and compares.

The successor of an even number is odd. The same $k$ works for both statements, but the equation changes.

```python {run continue}
@logos.theorem
def odd_successor(n: Int):
    """The successor of an even integer is odd."""
    return even(n) >> odd(n + 1)

@odd_successor.proof
def prove_odd_successor(p, n):
    """The same half witnesses the successor."""
    even_n = p.assume(even(n))
    k, n_eq = p.obtain(even_n)
    successor = p.ring(n + 1 == 2 * k + 1, using=[n_eq])
    return p.witness(k, successor)
```

The goal after `p.assume` is `odd(n + 1)`, which unfolds to $\exists k,\ n + 1 = 2k + 1$. The witness is the old $k$. Nothing in the proof depends on the value of $n$.

Certify both theorems before moving on.

```python {run continue}
for theorem in (even_sum, odd_successor):
    theorem.check()
    print(f"{theorem.name}: {theorem.certified}")
```

## Three lemmas worth keeping

The next chapter needs the same divisibility facts that Chapter 6 proved for its own example. Instead of copying them, the number theory module keeps them under names. The first says that every integer divides itself, with quotient one.

<!-- source: divides_self -->
```python
@logos.theorem
def divides_self(d: Int):
    """Every integer divides itself."""
    return divides(d, d)

@divides_self.proof
def prove_divides_self(p, d):
    """The quotient is one."""
    product = p.ring(d == d * 1)
    return p.witness(1, product)
```

The second composes two quotients. If $b = ak$ and $c = bj$, then $c = a(kj)$, so the new quotient is the product.

<!-- source: divides_trans -->
```python
@logos.theorem
def divides_trans(a: Int, b: Int, c: Int):
    """Divisibility is transitive."""
    return (divides(a, b) & divides(b, c)) >> divides(a, c)

@divides_trans.proof
def prove_divides_trans(p, a, b, c):
    """Multiply the two quotient equations."""
    both = p.assume(divides(a, b) & divides(b, c))
    k, ab = p.obtain(both.left())   # b = a * k
    j, bc = p.obtain(both.right())  # c = b * j
    ac = p.ring(c == a * (k * j), using=[ab, bc])
    return p.witness(k * j, ac)
```

The third scales the dividend. If $b = ak$, then $cb = c(ak) = a(kc)$, and the quotient changes from $k$ to $kc$.

<!-- source: divides_mul -->
```python
@logos.theorem
def divides_mul(a: Int, b: Int, c: Int):
    """A multiple of b is still a multiple of any divisor of b."""
    return divides(a, b) >> divides(a, c * b)

@divides_mul.proof
def prove_divides_mul(p, a, b, c):
    """Scale the quotient by c."""
    ab = p.assume(divides(a, b))
    k, bk = p.obtain(ab)
    scaled = p.ring(c * b == a * (k * c), using=[bk])
    return p.witness(k * c, scaled)
```

The proofs are short because the mathematics is in the choice of witness. `p.ring` does not guess that choice; it checks the equation you wrote with the quotients you named.

Check all three from the installed package. The module is imported, not edited.

```python {run continue}
for lemma in (
    number_theory.divides_self,
    number_theory.divides_trans,
    number_theory.divides_mul,
):
    lemma.check()
    print(f"{lemma.name}: {lemma.certified}")
```

`certified` is `True` only after the Rust checker accepted the exported evidence. The next chapters call these lemmas by name, and the checker rechecks each dependency rather than trusting the caller.

## When a step fails

The witness is the one place where a parity proof can go wrong without the algebra noticing. Suppose `even_sum` offered $i$ instead of $i + j$:

```python
return p.witness(i, total)
```

The equation `total` is still true, and `i` is still an integer. What fails is the instantiated predicate: the goal is $a + b = 2(i + j)$, while the witness $i$ promises $a + b = 2i$.

```text
the evidence does not prove the instantiated existential predicate
  expected: a + b = 2 * i
  got: a + b = 2 * (i + j)
  opened hypotheses:
    a_eq: a = 2 * i
    b_eq: b = 2 * j
```

The message repeats the two equalities the proof opened. They show why $i$ is too small: it accounts for $a$ alone. Restore `i + j` and the theorem certifies again.

A second mistake is to stop after `total` and return it. `total` proves an equation, not the existential. The `p.witness` call is what packages the equation with its witness.

## Exit exercise

Prove that the product of an even integer and any integer is even:

$$\operatorname{even}(a) \Rightarrow \operatorname{even}(a \cdot b).$$

Apply `number_theory.divides_mul` with $a = 2$, $b = a$ and $c = b$. The lemma returns $\operatorname{divides}(2, b \cdot a)$, so the product arrives commuted. Prove $b \cdot a = a \cdot b$ with `p.ring` and rewrite the fact with `p.subst`, or state the exercise with $b \cdot a$ and explain why the two statements are the same. Check the theorem and confirm that the reading reports zero custom axioms.

As a second exercise, prove that the sum of an even integer and an odd integer is odd. Open both existentials, add the halves, and choose the witness for `odd`. Write the equation before you write the code.
