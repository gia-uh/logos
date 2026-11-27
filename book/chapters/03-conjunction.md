---
theme: book
title: Facts That Hold Together
stem: conjunction
---

# Facts That Hold Together

Writing Your First Proof built a conditional proof from implications. This chapter adds the first connective: a conjunction $P \land Q$, written `P & Q` in Python. A conjunction is two facts held together as one. The proof operations are small, but they introduce the habit the rest of the book depends on: name the intermediate fact that matches part of your goal.

## Before you start

**Prerequisites.** Writing Your First Proof: `p.assume`, `p.apply`, `p.note`, and the difference between a proposition and evidence for it.

**Outcomes.** You will project a fact from a conjunction, build a conjunction from two facts, name an intermediate fact, and recognize the diagnostic that appears when the returned evidence proves the wrong conjunction.

## A conjunction carries two facts

Suppose you know that $P$ and $Q$ are both true. If someone asks for $Q$ and $P$, in that order, you do not need a new argument: take the second component and the first component, then put them together in the requested order. In Logos, `right()` projects evidence for $Q$ and `left()` projects evidence for $P$. Pass those facts to `p.and_intro` in the order the goal asks for.

```python {run}
import logos
from logos import Prop

@logos.theorem
def and_swap(P: Prop, Q: Prop):
    """A conjunction does not care about the order of its components."""
    return (P & Q) >> (Q & P)

@and_swap.proof
def prove_and_swap(p, P, Q):
    """Read both components, then rebuild the conjunction in the other order."""
    both = p.assume(P & Q)
    p_fact = both.left()
    q_fact = both.right()
    p.note("Q comes from the right component; P from the left.")
    return p.and_intro(q_fact, p_fact)
```

`p.assume(P & Q)` introduces one hypothesis and returns one fact, not two. The fact has a conjunction as its statement. `both.left()` and `both.right()` **project** the two components. Each projection returns a new fact whose statement is the component and whose evidence records which side it came from.

`p.and_intro(q_fact, p_fact)` does the inverse. It takes two facts and returns a fact for `Q & P`. The order of the arguments is the order of the resulting conjunction, so reversing them changes the statement.

The `p.note` line is authored commentary. It rides inside the evidence and appears in the checker's reading, labelled as unchecked. A `#` comment would stay in the Python source and never reach the certificate. Use comments for the mechanics of the code and notes for the mathematics you want a reader of the derivation to see.

## Name the fact that proves part of the goal

Start at the outer conjunction in `(P & Q) & R`. What must the two arguments of the final `p.and_intro` prove? The left one must prove `P & Q` and the right one must prove `R`.

Now read the hypothesis `P & (Q & R)` from the outside in. The left projection supplies `P`, and the right projection supplies `Q & R`. Project that second fact in both directions to get `Q` and `R`. Combine `P` with `Q` first because the whole pair is the left input of the final introduction. Call that intermediate fact `pq`.

```python {run continue}
@logos.theorem
def and_regroup(P: Prop, Q: Prop, R: Prop):
    """Regroup a nested conjunction without losing a component."""
    return (P & (Q & R)) >> ((P & Q) & R)

@and_regroup.proof
def prove_and_regroup(p, P, Q, R):
    """Name each component and build the two halves of the goal."""
    all_three = p.assume(P & (Q & R))
    p_fact = all_three.left()
    rest = all_three.right()
    q_fact = rest.left()
    r_fact = rest.right()
    pq = p.and_intro(p_fact, q_fact)
    p.note("pq is a named intermediate fact for the left half of the goal.")
    return p.and_intro(pq, r_fact)
```

The assignment to `pq` gives the evidence for `P & Q` a name. The proof step is the call to `p.and_intro` that builds the evidence. The name lets you compare the two final inputs with the two sides of the goal separately.

## Check both proofs

```python {run continue}
for theorem in (and_swap, and_regroup):
    theorem.check()
    print(f"{theorem.name}: {theorem.certified}")
```

Each line comes from a real invocation of the Rust checker. The receipt records the statement and the evidence, including the authored notes. Neither proof uses a custom axiom: the only rules are implication introduction, conjunction introduction and conjunction elimination.

The reading below shows the accepted regrouping proof. Look for the conjunction introductions for `P & Q` and then `(P & Q) & R`. The note about `pq` appears as unchecked commentary.

::: proof
```python {run continue echo=false}
print(and_regroup.inspect())
```
:::

## When a step fails

The most common mistake in this chapter is to return the hypothesis instead of the requested conjunction. In `and_swap`, replace the last line with `return both`. The proof function now returns evidence for `P & Q` while the goal is `Q & P`. The part of the diagnostic that names the disagreement is:

```text
Theorem 'and_swap': the returned evidence does not prove the current goal
  expected goal: Q & P
  got: P & Q
```

The message tells you which two statements to compare. It does not say that the proof is mathematically wrong; it says that the final evidence and the current goal disagree. The repair is to project the two components in the order the goal requests.

If `q_fact = rest.right()`, then `q_fact` proves `R`. The intermediate `pq` becomes `P & R`: its left component is still `P`. The checker reports the mismatch at the final return.

```text
Theorem 'and_regroup': the returned evidence does not prove the current goal
  expected goal: (P & Q) & R
  got: (P & R) & R
```

Work back from the differing left halves. They differ on their right component, so inspect the projection that supplied `q_fact`.

## Exit exercise

Given evidence for $(P \land Q) \land R$, prove $Q \land (R \land P)$. Before writing Python, state which two facts the final introduction must combine, in order. Then check that your theorem is certified.

<details>
<summary>Hint after an independent attempt</summary>

The left projection of the hypothesis is itself a conjunction. Project its left and right components to get $P$ and $Q$. Build $R \land P$ from the other projection and the fact for $P$.

</details>
