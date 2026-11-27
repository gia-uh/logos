---
theme: book
title: Writing Your First Proof
stem: first-proof
---

# Writing Your First Proof

*Prerequisites: Python functions and decorators, and the idea of implication. Outcomes: state a theorem, attach a proof, run the checker, and read the verifier's whole checked derivation.*

Suppose you know that $P$ implies $Q$ and that $Q$ implies $R$. On paper, you could prove that $P$ implies $R$ in one line: “Assume $P$. Then $Q$, and hence $R$.” The words *then* and *hence* do most of the work. When we write the argument in Logos, we say which implication justifies each step.

## State what you intend to prove

In mathematics, a theorem is a statement we have proved. In Logos, we give that statement a name **before** we prove it, so we have something to attach our argument to. The decorator `@logos.theorem` creates a Python object for that purpose. In this example we call it `compose` because the claim joins two implications end to end.

The parameters describe what the claim ranges over. `Prop` is the Logos type for a proposition, a statement that can be true or false. Writing `P: Prop` tells Logos to give the function a symbolic proposition called `P`. Inside the function, `P >> Q` builds the statement “if $P$, then $Q$.” The expression returned by the function becomes the claim for **every** choice of the three propositions.

On paper, “given $A$ and $B$, prove $C$” becomes $A \Rightarrow (B \Rightarrow C)$. In Python that is `A >> (B >> C)`. This nesting lets us introduce $A$ and then $B$ before working on $C$. Here $A$ is $P \Rightarrow Q$, $B$ is $Q \Rightarrow R$, and $C$ is $P \Rightarrow R$. Write the nested expression with parentheses before reading the declaration.

```python {run}
import logos
from logos import Prop

@logos.theorem
def compose(P: Prop, Q: Prop, R: Prop):
    """If P implies Q and Q implies R, then P implies R."""
    return (P >> Q) >> ((Q >> R) >> (P >> R))
```

Read the outermost arrow first. Its premise is `P >> Q`. Grant that premise, and what remains to show is `(Q >> R) >> (P >> R)`. Grant the second premise, and the goal becomes `P >> R`. The parentheses make that nesting explicit in Python. The docstring states the same claim in words. At this point `compose` holds a statement awaiting a proof.

## Write the argument

A **proof** in Logos is a construction that supplies evidence for the stated claim. Here the evidence must tell us how to get from $P$ to $R$ using the two implications we were given. The decorator `@compose.proof` attaches the following function to that particular theorem.

The first parameter, `p`, is the **proof context**. It keeps track of the claim still to be established (the *goal*) and the facts available at this point in the argument. Logos supplies that context and the same symbolic propositions we named in the statement.

We need two operations. When the goal is an implication, `p.assume` introduces its premise as a **local hypothesis** and moves the goal to its conclusion. The returned Python value records that we may use that hypothesis here. Once we have both an implication and evidence for its premise, `p.apply` combines them to obtain evidence for its conclusion.

After introducing the two given implications and $P$, your goal is $R$. To use $Q \Rightarrow R$, what evidence are you missing? Which available implication can produce it from a hypothesis you already have? Pick the two applications in order before reading the proof.

```python {run continue}
@compose.proof
def prove_compose(p, P, Q, R):
    """Reach R through Q, the proposition both implications mention."""
    p_to_q = p.assume(P >> Q)
    q_to_r = p.assume(Q >> R)

    # The remaining goal is P >> R. Work under its premise.
    given_p = p.assume(P)

    # The second implication needs Q. The first one supplies it.
    have_q = p.apply(p_to_q, given_p)
    p.note("We now have Q, the premise the second implication needs.")
    return p.apply(q_to_r, have_q)
```

The first application supplies the missing evidence, `have_q`. Could we pass `Q` itself to the last line? The letter `Q` names a proposition. The value `have_q` records **why we are entitled to use it**: we had evidence for $P$, and we applied the implication from $P$ to $Q$. That distinction is what lets another program check the argument. The last line uses that evidence to derive $R$.

The proof function also has a docstring. It states the intended strategy in one sentence. The `p.note` line is different from an ordinary `#` comment. A comment helps you read the source; the note travels inside the checked evidence, so a reader of the certificate sees it too. Here it records the state after `have_q` and before the second implication is applied.

Our three assumptions are local to this proof. If someone later uses `compose`, what they get is the whole conditional statement. To obtain evidence for their own $R$, they will still need to supply the two implications and evidence for their $P$.

## Check the proof

So far we have declared a statement and attached a Python function describing how to prove it. Calling `check()` runs that function to construct the evidence. Logos then sends the statement and evidence to its independent Rust verifier, which checks that each inference is valid and that the final conclusion matches the original statement. On success, the theorem object records the verification. If a step cannot be constructed or verified, the call raises an error.

```python {run continue}
compose.check()
```

The check establishes the implication for arbitrary propositions. It never needs to assign particular truth values to $P$, $Q$ or $R$: each step is justified by a rule that works for any such propositions.

## Read a failed step

Change just the last line of the proof to `return p.apply(q_to_r, given_p)`. Before checking it, read the arrow stored in `q_to_r`. Which premise does it require? Which proposition does `given_p` establish?

```text
expected: Q
got: P
```

These two lines describe the attempted **application**, not the theorem's final goal. Logos is still trying to reach $R$. To get there by this arrow it needs evidence for $Q$, and the edit handed it evidence for $P$. Restore `have_q` and check the proof again.

## Read what you proved

Look back at the last line of the proof function. It returns evidence for $R$. Would it be correct to tell someone that you have proved $R$? To answer, read the theorem and the derivation that the verifier accepted.

After `compose.check()`, the theorem has a **receipt**, the record of its successful verification. Its `artifact` contains the exact statement and evidence that were checked. `compose.inspect()` sends those exact bytes to the installed Rust checker and returns its Markdown reading. Python does not rebuild the argument; it asks the verifier that accepted the receipt to explain it. If the receipt is missing or the evidence has changed, `inspect()` raises an error instead of showing a stale reading.

In the full reading below, start with the theorem and the axiom status. Then find steps 7 and 8, where the applications give $Q$ and $R$. Step 9 **discharges** the local assumption $P$ by putting it on the left of an implication. Steps 10 and 11 discharge the two given implications in the same way. Finally, compare the conclusion with the stated theorem.

::: proof
```python {run continue echo=false}
print(compose.inspect())
```
:::

The reading reports zero custom axioms because the three hypotheses are local and each is accounted for by an arrow in the theorem. The final generalizations tell us the argument works for every choice of $P$, $Q$ and $R$.

## Exit exercise

In a new Python file, prove $P \Rightarrow ((P \Rightarrow Q) \Rightarrow Q)$. Decide which hypotheses to introduce in which order and which one supplies the premise of your application. Run your file as in the Quick Start and check for `checked: True`. What whole statement has been established when the final line of your proof returns evidence for $Q$?

## Solution

Introduce $P$ first and $P \Rightarrow Q$ second. The first hypothesis supplies the premise of the implication. The result is the conditional $P \Rightarrow ((P \Rightarrow Q) \Rightarrow Q)$ for arbitrary $P$ and $Q$. Both hypotheses are discharged.

```python {run}
import logos
from logos import Prop

@logos.theorem
def use_implication(P: Prop, Q: Prop):
    return P >> ((P >> Q) >> Q)

@use_implication.proof
def prove_use_implication(p, P, Q):
    given_p = p.assume(P)
    p_to_q = p.assume(P >> Q)
    return p.apply(p_to_q, given_p)

use_implication.check()
assert use_implication.certified
print("checked:", use_implication.certified)
```
