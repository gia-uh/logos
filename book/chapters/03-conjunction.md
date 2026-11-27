---
theme: book
title: Facts That Hold Together
stem: conjunction
---

# Facts That Hold Together

Chapter 1 built a conditional proof from implications. This chapter adds the first connective: a conjunction $P \land Q$, written `P & Q` in Python. A conjunction is two facts held together as one. The proof operations are small, but they introduce the habit the rest of the book depends on: name the intermediate fact you will reuse.

## Before you start

**Prerequisites.** Chapter 1: `p.assume`, `p.apply`, `p.note`, and the difference between a proposition and evidence for it.

**Outcomes.** You will project a fact from a conjunction, build a conjunction from two facts, name an intermediate fact, and recognize the diagnostic that appears when the returned evidence proves the wrong conjunction.

## A conjunction carries two facts

Suppose you know that $P$ and $Q$ are both true. If someone asks for $Q$ and $P$, in that order, you do not need a new argument: take the second component and the first component, then put them together in the requested order.

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

## Name the fact you will reuse

A proof usually needs a fact more than once. Name it once, with a Python assignment, and pass the name to later steps. The name is for the reader and for diagnostics; the evidence is what the checker consumes.

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

Read the goal before the return: `(P & Q) & R`. `pq` already proves `P & Q`, and `r_fact` proves `R`, so the final `p.and_intro` closes the goal. Without the name, the same evidence would be written as a nested expression:

```python
return p.and_intro(p.and_intro(p_fact, q_fact), r_fact)
```

Both versions produce the same derivation. The named version lets a diagnostic say `pq` instead of repeating the whole expression, and it lets the prose point at the moment the left half was assembled.

A Python assignment does not create a new proof step. It only gives a local name to an existing fact. Reusing the name later reuses the same checked evidence; it does not re-run the derivation.

## Check both proofs

```python {run continue}
for theorem in (and_swap, and_regroup):
    theorem.check()
    print(f"{theorem.name}: {theorem.certified}")
```

Each line comes from a real invocation of the Rust checker. The receipt records the statement and the evidence, including the authored notes. Neither proof uses a custom axiom: the only rules are implication introduction, conjunction introduction and conjunction elimination.

## When a step fails

The most common mistake in this chapter is to return the hypothesis instead of the requested conjunction. In `and_swap`, replace the last line with `return both`. The proof function now returns evidence for `P & Q` while the goal is `Q & P`. The part of the diagnostic that names the disagreement is:

```text
Theorem 'and_swap': the returned evidence does not prove the current goal
  expected goal: Q & P
  got: P & Q
```

The message tells you which two statements to compare. It does not say that the proof is mathematically wrong; it says that the final evidence and the current goal disagree. The repair is to project the two components in the order the goal requests.

A second mistake is to project from the wrong side. If `and_regroup` used `rest.right()` for `q_fact`, the later `p.and_intro(p_fact, q_fact)` would still build a conjunction, but its left component would be `R`, and the final return would fail against `(P & Q) & R`. Compare the printed statement of the fact with the goal before blaming the final step; the error is usually earlier than the line that reports it.

## Exit exercise

Prove

$$\bigl(P \land (Q \land R)\bigr) \;\Rightarrow\; \bigl(R \land (P \land Q)\bigr).$$

Use `p.assume`, `left()`, `right()` and `p.and_intro`. Name the intermediate conjunction $P \land Q$ before you combine it with $R$. Then check the theorem and confirm that `certified` is `True`.

If your first attempt fails with `expected goal: R & (P & Q)`, read the two components of your final `p.and_intro` in order. The left one must prove $R$, not $P$.
