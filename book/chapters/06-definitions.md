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

## Build reusable lemmas {#three-lemmas-worth-keeping}

Transitivity lets a later proof connect two divisibility facts through a common middle term.

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

A multiple of $b$ is still a multiple of any divisor of $b$. Suppose $b = ak$ and your goal is $a \mid cb$. Write the equation the witness must satisfy. What expression in $k$ and $c$ fills the blank in $cb = a(\,?\,)$? Predict the witness before reading the proof.

Substitute $b = ak$ to get $cb = c(ak) = a(kc)$. The quotient changes from $k$ to $kc$.

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

## Apply a lemma by name

A checked theorem can be used in a later proof. `p.apply` walks the lemma's statement from the outside in. A term argument instantiates a universal binder. A fact argument discharges an implication premise. The result is a fact for whatever remains.

The goal is `divides(a, a * a)`. Look at the conclusion of `divides_mul(x, y, z)`, which is `divides(x, z * y)`. Match the divisor first, then the two factors. Which arguments make the conclusions agree, and what premise will you still need?

Set `x = a`, `y = a`, and `z = a`. The remaining premise is `divides(a, a)`, the conclusion of `divides_self(a)`. Write down the proposition carried by `scaled` before reading the final application.

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

`p.apply` does not search for a proof of the antecedent. It matches the fact you give it against the premise, allowing equality to be used in either direction. If the fact proves something else, the diagnostic shows the required premise and the proposition you passed.

## Compose two lemmas

Suppose $a \mid b$ and the goal is $a \mid b^2$. Transitivity can connect them through $b$. Its conclusion fixes the first and last arguments, and the hypothesis fixes the middle one. The remaining fact is $b \mid b^2$, which the square lemma gives at $b$.

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
    divides_square,
    divides_square_of_multiple,
):
    theorem.check()
    print(f"{theorem.name}: {theorem.certified}")
```

In **Proof**, look for the citation of the checked square lemma. The receipt identifies checked lemmas by their propositions. Step 67 cites the square lemma and points back to its derivation at step 60. Follow the references from that derivation to step 53, where the square proof cites the scaling lemma. Which of those citations is direct in the final theorem, and which is transitive? In **Custom axioms**, look for the count. The divisibility body belongs under **Domains and definitions**.

::: proof
```python {run continue echo=false}
print(divides_square_of_multiple.inspect())
```
:::

## When a step fails

Suppose the last line of `divides_square_of_multiple` passes the conjunction in the wrong order:

```python
return p.apply(chain, p.and_intro(square, multiple))
```

The facts are individually correct, but the antecedent of `chain` expects $a \mid b$ first. The diagnostic compares the whole antecedent, with some definitions unfolded:

```text
the fact does not prove the antecedent needed by fact
  expected: exists k:Int. b = a * k & exists k:Int. b * b = b * k
  got: exists k:Int. b * b = b * k & divides(a, b)
```

The word `fact` refers to the instantiated implication `chain`. Compare the first component on each line: the premise starts with $a \mid b$, while the supplied conjunction starts with $b \mid b^2$. Restore the order of the arguments to `p.and_intro`.

A second mistake is to stop after `chain` and return it. `chain` still proves an implication, while the goal is the consequent. The final `p.apply(chain, ...)` is what performs the elimination. Read the statement carried by each named fact before the return.

## Guided practice

Prove $a \mid a \cdot (a \cdot a)$. Match the conclusion of `divides_mul` to the goal and use `divides_square` for its remaining premise. Write the instantiated implication before applying it.

## Exit exercise

Given $a \mid b$ and $b \mid c$, prove $a \mid c \cdot c$. Use checked lemmas from this chapter. Before writing Python, name the lemmas you choose and write their instantiated premises and conclusions. Identify the fact that supplies each premise.

As optional witness practice, prove that $a \mid b$ and $c \mid d$ imply $(ac) \mid (bd)$. Write the equation your witness must satisfy.

## Instructor solutions

For the cube, choose the square as the dividend and $a$ as the scale. For the exit exercise, transitivity supplies $a \mid c$, the premise of scaling the dividend $c$ by $c$.

```python {run continue}
@logos.theorem
def divides_cube(a: Int):
    return divides(a, a * (a * a))

@divides_cube.proof
def prove_divides_cube(p, a):
    square = p.apply(divides_square, a)
    return p.apply(divides_mul, a, a * a, a, square)
```

```python {run continue}
@logos.theorem
def divides_square_through(a: Int, b: Int, c: Int):
    return (divides(a, b) & divides(b, c)) >> divides(a, c * c)

@divides_square_through.proof
def prove_divides_square_through(p, a, b, c):
    both = p.assume(divides(a, b) & divides(b, c))
    ac = p.apply(divides_trans, a, b, c, both)
    return p.apply(divides_mul, a, c, c, ac)

for exercise in (divides_cube, divides_square_through):
    exercise.check()
    print(f"{exercise.name}: {exercise.certified}")
```

For the optional product exercise, multiply $b = ai$ by $d = cj$ and regroup to get $bd = (ac)(ij)$.

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

divides_product.check()
print(f"{divides_product.name}: {divides_product.certified}")
```
