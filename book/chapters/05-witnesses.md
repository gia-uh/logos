---
theme: book
title: Witnesses and Their Scope
stem: witnesses
---

# Witnesses and Their Scope

An existential statement promises a value. It does not say which one, and it does not let you keep the value after the promise is discharged. This chapter introduces the two directions of that promise: opening an existential that you already have, and closing an existential that you need to prove. It also introduces the universal quantifier inside a proof and the scope rules that keep witnesses from leaking.

## Before you start

**Prerequisites.** Writing Your First Proof, Facts That Hold Together, and When a Proof Splits in Two: `p.assume`, `p.apply`, `p.and_intro`, `p.cases`, `p.negate`, `p.not_elim` and `p.ex_falso`. You should be comfortable reading a goal and a local hypothesis before each step.

**Outcomes.** You will open an existential with `p.obtain`, close one with `p.witness`, build a named existential with `p.exists`, introduce an arbitrary value with `p.fix`, and explain why a witness may not mention a symbol outside its scope.

## Two directions of an existential

The sum of two even integers is even. “$a$ is even” means that some integer $i$ satisfies $a = 2i$. The hypothesis gives us two such integers, one for each summand. The conclusion asks for $k$ such that $a+b=2k$.

Substitute the equations from the hypotheses and factor out 2:

$$a+b = 2i+2j = 2(i+j).$$

Which expression supplies $k$? The coefficient of 2 in the last expression is $i+j$. In Logos, `exists(Int, lambda i: a == 2 * i)` states the premise about $a$. Given evidence for that premise, `p.obtain` returns a fresh symbolic integer `i` and a fact `a_eq` for $a=2i$. The symbol represents the promised value and carries no Python integer value. Open the second premise in the same way.

```python {run}
import logos
from logos import Int, exists, forall

@logos.theorem
def even_sum(a: Int, b: Int):
    """The sum of two even integers is even."""
    return (
        exists(Int, lambda i: a == 2 * i)
        & exists(Int, lambda j: b == 2 * j)
    ) >> exists(Int, lambda k: a + b == 2 * k)

```

Now use `p.ring` to derive $a+b=2(i+j)$ from the two named equations. It constructs a polynomial certificate that the checker recomputes. Give the chosen term and the equation for that term to `p.witness`.

```python {run continue}
@even_sum.proof
def prove_even_sum(p, a, b):
    """Open both witnesses, add the equations, and package their sum."""
    assumptions = p.assume(
        exists(Int, lambda i: a == 2 * i)
        & exists(Int, lambda j: b == 2 * j)
    )
    i, a_eq = p.obtain(assumptions.left())
    j, b_eq = p.obtain(assumptions.right())
    sum_eq = p.ring(a + b == 2 * (i + j), using=[a_eq, b_eq])
    p.note("The witness for the sum is the sum of the two opened witnesses.")
    return p.witness(i + j, sum_eq)
```

The packaged conclusion says only that some $k$ works. Its statement contains neither of the local symbols `i` and `j`.

## A forall introduces an arbitrary value

The universal quantifier is the dual. To prove $\forall x. P(x)$, you introduce an arbitrary $x$ and prove $P(x)$ without assuming anything special about $x$. The checker generalizes the result at the end.

The theorem below has a premise before the universal: if $a$ is even, then every multiple of $a$ is even. The premise is an existential, and the conclusion contains a forall inside the implication. Open the premise to get $a=2i$, then use `p.fix("x")` to bind an arbitrary $x$. Multiplying the equation by $x$ gives $ax=2(ix)$, so the body of the forall has witness $ix$. Package that fact inside the block and pass it to `fixed.finish` to generalize over $x$.

```python {run continue}
@logos.theorem
def even_multiple(a: Int):
    """If a is even, every multiple of a is even."""
    return (exists(Int, lambda i: a == 2 * i)) >> forall(
        Int, lambda x: exists(Int, lambda k: a * x == 2 * k)
    )

@even_multiple.proof
def prove_even_multiple(p, a):
    """Open the witness for a, introduce x, and multiply the equation by x."""
    even_a = p.assume(exists(Int, lambda i: a == 2 * i))
    i, a_eq = p.obtain(even_a)
    with p.fix("x") as fixed:
        x = fixed.variable
        product = p.ring(a * x == 2 * (i * x), using=[a_eq])
        fixed.finish(p.witness(i * x, product))
    return fixed.result
```

`p.fix("x")` introduces an arbitrary integer. It requires the current goal to be a universal statement. `fixed.variable` is the symbolic value; `fixed.finish(...)` closes the universal scope by generalizing over it. The result is a fact for the whole forall.

Why not use `p.fix` for every theorem parameter? The outer parameters of `@logos.theorem` are already universally quantified. The proof function receives them as symbolic values and the checker generalizes at the end. `p.fix` is for a forall that appears *inside* the statement, after a premise or inside another connective.

The scope of `x` is the `with` block. A fact produced inside the block may mention `x`, but a fact returned to the caller may not, unless the returned statement still binds `x`. `fixed.finish` performs that generalization; after the block, the Python name `x` still exists, but the Logos symbol it names is out of scope.

## Nested existentials

The goal is $\exists x.\;\exists y.\;(a=x) \land (b=y)$. Choose $x=a$. Substitute that choice in the body before reading the code. What existential remains, and what value of $y$ makes its two equalities reflexive?

The inner goal is $\exists y.\;(a=a) \land (b=y)$. Pick $y=b$ and combine `p.refl(a)` with `p.refl(b)`. Use `p.exists(inner_goal, b, evidence)` to package that conjunction for the explicit inner goal. Now `p.witness(a, inner)` has evidence for the entire body at $x=a$.

```python {run continue}
@logos.theorem
def pair_witness(a: Int, b: Int):
    """Two integers are the two coordinates of some pair."""
    return exists(Int, lambda x: exists(Int, lambda y: (a == x) & (b == y)))

@pair_witness.proof
def prove_pair_witness(p, a, b):
    """Build the inner existential first, then the outer one."""
    inner_goal = exists(Int, lambda y: (a == a) & (b == y))
    inner = p.exists(inner_goal, b, p.and_intro(p.refl(a), p.refl(b)))
    return p.witness(a, inner)
```

Construction proceeds inside out because the outer introduction needs the inner existential as its evidence.

## Scope is not a formality

In `even_multiple`, `fixed.finish(p.witness(i * x, product))` packages the witness while the arbitrary `x` is in scope. To see why that timing matters, replace the final `return fixed.result` with this attempt to export the local witness directly. Use `p.exists` to target an explicit existential because the current goal outside `p.fix` is universal.

```python
    escaped_goal = exists(Int, lambda k: a * x == 2 * k)
    return p.exists(escaped_goal, i * x, product)
```

Python still resolves `x` and `product` as local names. Logos rejects the witness because the `with p.fix("x")` block has ended.

```text
the witness mentions symbols that are not in scope
```

The diagnostic's `unbound` field lists `x`. Restore `return fixed.result`. The finished fact binds $x$ in the universal statement, so it can leave the block. The same scope rule applies to arguments used to instantiate a universal lemma with `p.apply`.

## Check the three proofs

```python {run continue}
for theorem in (even_sum, even_multiple, pair_witness):
    theorem.check()
    print(f"{theorem.name}: {theorem.certified}")
```

Each theorem exercises a different direction: two opened witnesses, one opened witness plus an arbitrary value, and two nested witnesses. All three close without a custom axiom.

## When a step fails

Change the final witness in `even_sum` to `i + j + 1` but leave the equation unchanged. The value and the evidence no longer describe the same instance:

```text
the evidence does not prove the instantiated existential predicate
  expected: a + b = 2 * (i + j + 1)
  got: a + b = 2 * (i + j)
```

The expected statement is the body of the existential after substituting the chosen value. The received statement is what the evidence actually proves. The repair is either to change the value or to change the evidence; the proof cannot proceed with a mismatch.

A second common failure is a missing `fixed.finish(...)` inside `p.fix`. The scope then closes without a proof and reports `the forall branch was never finished with .finish(...)`. The fix is to finish the universal branch with a fact for its body, not with a fact for the outer implication.

## Exit exercise

1. Given $\exists i.\;a=2i$, prove $\exists k.\;3a=2k$. Choose a witness, write the exact equation it requires, and explain what the checker would compare if you supplied a different witness with the same evidence.
2. Prove $(\exists i.\;a=2i) \Rightarrow (\exists k.\;a+a=2k)$. Then decide whether the premise is necessary. Justify your answer with a checked proof or a counterexample.
3. Given $a=b$, prove $\forall x.\;\exists y.\;(a+x=y)\land(b+x=y)$. State where you must package the witness and what evidence can leave the scope of $x$.

Check that your proofs certify before comparing approaches.
