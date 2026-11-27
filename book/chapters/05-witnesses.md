---
theme: book
title: Witnesses and Their Scope
stem: witnesses
---

# Witnesses and Their Scope

An existential statement promises a value. It does not say which one, and it does not let you keep the value after the promise is discharged. This chapter introduces the two directions of that promise: opening an existential that you already have, and closing an existential that you need to prove. It also introduces the universal quantifier inside a proof and the scope rules that keep witnesses from leaking.

## Before you start

**Prerequisites.** Chapters 1, 3 and 4: `p.assume`, `p.apply`, `p.and_intro`, `p.cases`, `p.negate`, `p.not_elim` and `p.ex_falso`. You should be comfortable reading a goal and a local hypothesis before each step.

**Outcomes.** You will open an existential with `p.obtain`, close one with `p.witness`, build a named existential with `p.exists`, introduce an arbitrary value with `p.fix`, and explain why a witness may not mention a symbol outside its scope.

## Two directions of an existential

The sum of two even integers is even. “$a$ is even” means that some integer $i$ satisfies $a = 2i$. The hypothesis gives us two such integers, one for each summand. The conclusion asks for one integer for the sum.

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

`exists(Int, lambda i: a == 2 * i)` builds the proposition $\exists i. a = 2i$. The `Int` argument fixes the sort of the bound variable; `lambda` names it in the body.

`p.obtain(assumptions.left())` opens the existential. It returns a pair: a fresh local integer, here `i`, and a fact for the body with the bound variable replaced by that integer. The fact `a_eq` proves $a = 2i$. The variable `i` is not a Python integer and carries no numeric value. It is a symbolic name that stands for the witness the hypothesis promises.

`p.witness(i + j, sum_eq)` goes the other way. It takes a value and evidence that the body holds at that value, and returns evidence for the current existential goal. The value here is $i + j$; the evidence is the equation $a + b = 2(i + j)$, which `p.ring` derived from the two opened equations.

`p.ring(equation, using=[...])` proves a polynomial identity over the integers. It builds an explicit certificate from the equations you name. The checker parses the certificate and recomputes the identity; it does not trust the algebra in the prose.

After the final `p.witness`, the goal no longer mentions `i` or `j`. That is the point of an existential: the value exists, but the proof of the existential does not expose which value it was to the caller. Inside the proof, `i` and `j` are available; outside, only the existential is.

## A forall introduces an arbitrary value

The universal quantifier is the dual. To prove $\forall x. P(x)$, you introduce an arbitrary $x$ and prove $P(x)$ without assuming anything special about $x$. The checker generalizes the result at the end.

The theorem below has a premise before the universal: if $a$ is even, then every multiple of $a$ is even. The premise is an existential, and the conclusion contains a forall inside the implication.

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

The scope of `x` is the `with` block. A fact produced inside the block may mention `x`, but a fact returned to the caller may not, unless the returned statement still binds `x`. `fixed.finish` performs that generalization; after the block, `x` is a name for a value that the caller cannot choose.

## Nested existentials

`p.witness` always closes the *current* goal. That is convenient for the outermost quantifier, but it is not enough to build an inner existential before the outer one. `p.exists(goal, value, evidence)` builds a fact for an explicitly named existential goal without changing the current goal.

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

The goal is $\exists x. \exists y. (a = x) \land (b = y)$. The outer witness is $a$, so the inner goal is $\exists y. (a = a) \land (b = y)$. `p.exists` packages $b$ and the conjunction $(a = a) \land (b = b)$ as a fact for that inner goal. Then `p.witness(a, inner)` closes the outer existential with that fact as evidence.

`p.refl(a)` proves the trivial equality $a = a$. It is the equality introduction rule; it needs no hypotheses. `p.and_intro` combines the two equalities.

The order matters. If you call `p.witness` first, it tries to close the outer existential and expects evidence for the whole body at the chosen value, including the inner existential. Building the inner fact first gives it something to consume.

## Scope is not a formality

A witness may mention only symbols that are in scope at the point where it is used. If it mentions a variable introduced inside a branch or a universal scope that has already closed, the exported artifact would refer to a value the reader cannot reconstruct.

`p.witness` enforces the rule before the checker sees the artifact. A value that mentions an unknown symbol produces:

```text
the witness mentions symbols that are not in scope
```

The machine-readable details name the offending symbol under `unbound`. In a chapter, the usual cause is a typo or a value copied from a hypothesis that was opened in a different branch.

The same rule applies to `p.apply` when it instantiates a universal lemma: the argument must be built from symbols in the current scope. Chapter 6 uses that rule when it applies a lemma with a term that was opened earlier.

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

Prove

$$\bigl(\exists i.\; a = 2i\bigr) \;\Rightarrow\; \bigl(\exists k.\; a + a = 2k\bigr).$$

Open the hypothesis with `p.obtain`, then choose a witness for the conclusion in terms of the opened integer. The equation $a + a = 2(i + i)$ follows from the hypothesis by `p.ring`. Confirm that the final `certified` is `True`.

As a second exercise, prove the same statement with the witness $a$ and the equation $a + a = 2a$. You still assume the premise to enter the implication, but the witness and the evidence do not use it. Both proofs are valid. Which one would you show to a reader who wants to know why the hypothesis was needed?
