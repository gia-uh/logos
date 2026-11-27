---
theme: book
title: Definitions That Unfold, Lemmas You Can Name
stem: definitions
---

# Definitions That Unfold, Lemmas You Can Name

A definition is not an assumption. It is a name for a body, and the checker may replace the name with the body whenever it needs to compare two statements. A lemma is not a shortcut either: it is a separately checked theorem whose conclusion another proof may cite. This chapter uses both to build a small theory of divisibility.

## Before you start

**Prerequisites.** Chapters 1 to 5: `p.assume`, `p.apply`, `p.and_intro`, `p.obtain`, `p.witness`, `p.ring`, and the distinction between a proposition and a fact.

**Outcomes.** You will declare a transparent definition, prove lemmas about it, apply a lemma by instantiating its quantifiers and discharging its premises, compose two lemmas, and read the checker's report of the dependency.

## A definition is a body the checker can unfold

Divisibility is the first definition in the book. “$d$ divides $a$” means that some integer $k$ satisfies $a = dk$. The body is an existential, so the operations from Chapter 5 apply directly.

```python {run}
import logos
from logos import Int, exists

@logos.definition
def divides(d: Int, a: Int):
    """d divides a when some integer k makes a equal to d * k."""
    return exists(Int, lambda k: a == d * k)
```

`@logos.definition` records the parameters and the body. Calling `divides(d, a)` with symbolic arguments builds an application node, not a Python boolean. The name `divides` and the body are both part of the artifact, so a reader of the certificate can see what the name means.

The difference from an axiom is important. An axiom would be an opaque fact that the checker accepts without a body. A transparent definition has a body, and **conversion** may unfold it during checking. When a proof proves `exists k. d == d * k`, the checker can compare that with `divides(d, d)` by unfolding the definition. No custom axiom is introduced.

The first lemma says that every integer divides itself. The witness is one.

```python {run continue}
@logos.theorem
def divides_self(d: Int):
    """Every integer divides itself."""
    return divides(d, d)

@divides_self.proof
def prove_divides_self(p, d):
    """The quotient is one."""
    one = p.ring(d == d * 1)
    return p.witness(1, one)
```

`p.ring(d == d * 1)` proves the equation by polynomial normalization. `p.witness(1, one)` closes the existential that the definition unfolds to. The proof never unfolds `divides` by hand; the checker does it when it compares the witness evidence with the definitional body.

## Three lemmas worth keeping

The next three lemmas are the ones the rest of the theory reuses. Each has a short proof, and each is stated as a theorem with a name.

Divisibility is transitive. If $a$ divides $b$ with quotient $k$, and $b$ divides $c$ with quotient $j$, then $c = bj = (ak)j = a(kj)$. The witness for $a \mid c$ is the product $kj$.

```python {run continue}
@logos.theorem
def divides_trans(a: Int, b: Int, c: Int):
    """Divisibility is transitive."""
    return (divides(a, b) & divides(b, c)) >> divides(a, c)

@divides_trans.proof
def prove_divides_trans(p, a, b, c):
    """Multiply the two quotients."""
    both = p.assume(divides(a, b) & divides(b, c))
    k, ab = p.obtain(both.left())
    j, bc = p.obtain(both.right())
    ac = p.ring(c == a * (k * j), using=[ab, bc])
    return p.witness(k * j, ac)
```

A multiple of $b$ is still a multiple of any divisor of $b$. If $b = ak$, then $cb = c(ak) = a(kc)$. The quotient changes from $k$ to $kc$.

```python {run continue}
@logos.theorem
def divides_mul(a: Int, b: Int, c: Int):
    """A multiple of b is still a multiple of any divisor of b."""
    return divides(a, b) >> divides(a, c * b)

@divides_mul.proof
def prove_divides_mul(p, a, b, c):
    """Scale the quotient by c."""
    h = p.assume(divides(a, b))
    k, ab = p.obtain(h)
    scaled = p.ring(c * b == a * (k * c), using=[ab])
    return p.witness(k * c, scaled)
```

The product of divisors divides the product of dividends. If $b = ai$ and $d = cj$, then $bd = (ac)(ij)$.

```python {run continue}
@logos.theorem
def divides_product(a: Int, b: Int, c: Int, d: Int):
    """The product of divisors divides the product of dividends."""
    return (divides(a, b) & divides(c, d)) >> divides(a * c, b * d)

@divides_product.proof
def prove_divides_product(p, a, b, c, d):
    """Multiply the two quotient equations."""
    both = p.assume(divides(a, b) & divides(c, d))
    i, ab = p.obtain(both.left())
    j, cd = p.obtain(both.right())
    product = p.ring(b * d == (a * c) * (i * j), using=[ab, cd])
    return p.witness(i * j, product)
```

Each proof follows the same pattern: open the existential hypotheses, derive the equation the new witness must satisfy, and close the goal with that witness. The mathematics is in the choice of witness; the checker verifies that the choice works.

## Apply a lemma by name

A checked theorem can be used in a later proof. `p.apply` walks the lemma's statement from the outside in. A term argument instantiates a universal binder. A fact argument discharges an implication premise. The result is a fact for whatever remains.

The square of an integer is a multiple of that integer. The proof applies `divides_mul` with $b = a$ and $c = a$ to the trivial divisor from `divides_self`.

```python {run continue}
@logos.theorem
def divides_square(a: Int):
    """An integer divides its own square."""
    return divides(a, a * a)

@divides_square.proof
def prove_divides_square(p, a):
    """Apply the scaling lemma to the trivial divisor."""
    scaled = p.apply(divides_mul, a, a, a)
    trivial = p.apply(divides_self, a)
    return p.apply(scaled, trivial)
```

Read `scaled` before the last line. `divides_mul` has three universal binders, so three term arguments instantiate them. What remains is the implication

$$\operatorname{divides}(a, a) \Rightarrow \operatorname{divides}(a, a \cdot a).$$

`trivial` is a fact for the antecedent. The final `p.apply(scaled, trivial)` discharges the implication and returns a fact for the consequent, which is exactly the goal.

`p.apply` does not search for a proof of the antecedent. It matches the fact you give it against the premise, allowing equality to be used in either direction. If the fact proves something else, the diagnostic names both statements and the lemma argument that failed.

## Compose two lemmas

The next theorem combines the square lemma with transitivity. If $a$ divides $b$, then $a$ divides $b^2$.

```python {run continue}
@logos.theorem
def divides_square_of_multiple(a: Int, b: Int):
    """A divisor of b also divides the square of b."""
    return divides(a, b) >> divides(a, b * b)

@divides_square_of_multiple.proof
def prove_divides_square_of_multiple(p, a, b):
    """Chain the hypothesis with the square lemma through transitivity."""
    multiple = p.assume(divides(a, b))
    square = p.apply(divides_square, b)
    chain = p.apply(divides_trans, a, b, b * b)
    return p.apply(chain, p.and_intro(multiple, square))
```

`square` is the checked lemma `divides_square` instantiated at $b$. `chain` is `divides_trans` with its three universal binders instantiated, leaving an implication whose antecedent is the conjunction $a \mid b \land b \mid b^2$. `p.and_intro(multiple, square)` builds that conjunction, and the final `p.apply` discharges the implication.

The final proof cites two checked lemmas, and `divides_square` cites two more. The exporter includes their evidence. The Rust checker rechecks each dependency, not only the last step, so a change to `divides_square` cannot leave this proof silently valid.

## Check and inspect the result

```python {run continue}
for theorem in (
    divides_self,
    divides_trans,
    divides_mul,
    divides_product,
    divides_square,
    divides_square_of_multiple,
):
    theorem.check()
    print(f"{theorem.name}: {theorem.certified}")

reading = divides_square_of_multiple.inspect()
print("zero custom axioms:", "Uses zero custom axioms." in reading)
```

`inspect()` returns the checker's own Markdown reading of the receipt. The reading names the checked lemmas and reports the custom-axiom count. Here the count is zero: the definition is transparent, the lemmas are checked theorems, and no author-declared assumption was used.

## When a step fails

Suppose the last line of `divides_square_of_multiple` passes the conjunction in the wrong order:

```python
return p.apply(chain, p.and_intro(square, multiple))
```

The facts are individually correct, but the antecedent of `chain` expects $a \mid b$ first. The diagnostic is:

```text
the fact does not prove the antecedent needed by divides_trans
  expected: divides(a, b)
  got: divides(b, b * b)
```

The message names the lemma and the argument position. It does not say that `divides_trans` is false or that the conjunction is malformed; it says that the first component is the wrong proposition. Reorder the arguments to `p.and_intro`.

A second mistake is to stop after `chain` and return it. `chain` still proves an implication, while the goal is the consequent. The final `p.apply(chain, ...)` is what performs the elimination. Read the statement carried by each named fact before the return.

## Exit exercise

Prove

$$\operatorname{divides}(a,\; a \cdot (a \cdot a)).$$

Use `divides_square` to obtain $a \mid a^2$, then use `divides_mul` with $b = a^2$ and $c = a$ to scale it. The final witness is the product of the two quotients. Check the theorem and confirm that the reading reports zero custom axioms.

As a second exercise, prove that if $a \mid b$ and $b \mid c$, then $a \mid c \cdot c$. Use `divides_trans` once to obtain $a \mid c$, then `divides_mul` once to scale it. Write down the intermediate fact each application produces before you write the code.
