---
theme: book
title: Writing Your First Proof
stem: first-proof
---

# Writing Your First Proof

*Prerequisites: Python functions and decorators, and the idea of implication. Outcomes: state a theorem, attach a proof, run the checker, and read a compact verified derivation.*

Logos is a Python library for writing arguments that a computer can check. Suppose you know that $P$ implies $Q$ and that $Q$ implies $R$. On paper, you could prove that $P$ implies $R$ in one line: “Assume $P$. Then $Q$, and hence $R$.” The words *then* and *hence* do most of the work. When we write the argument in Logos, we say which implication justifies each step.

## State what you intend to prove

In mathematics, a theorem is a statement we have proved. In Logos, we give that statement a name **before** we prove it, so we have something to attach our argument to. The decorator `@logos.theorem` creates a Python object for that purpose. In this example we call it `compose` because the claim joins two implications end to end.

The parameters describe what the claim ranges over. `Prop` is the Logos type for a proposition, a statement that can be true or false. Writing `P: Prop` tells Logos to give the function a symbolic proposition called `P`. Inside the function, `P >> Q` builds the statement “if $P$, then $Q$.” The expression returned by the function becomes the claim for **every** choice of the three propositions.

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

Pause at `have_q`. Could we pass `Q` itself to the last line? The letter `Q` names a proposition. The value `have_q` records **why we are entitled to use it**: we had evidence for $P$, and we applied the implication from $P$ to $Q$. That distinction is what lets another program check the argument. The last line uses that evidence to derive $R$.

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

As a final exercise, write the two applications as a single nested Python expression. Both versions prove the same statement. Which one would you give to someone who wanted to know where $Q$ came from?

## Read what you proved

Look back at the last line of the proof function. It returns evidence for $R$. Would it be correct to tell someone that you have proved $R$? To answer, read the theorem and the derivation that the verifier accepted.

After `compose.check()`, the theorem has a **receipt**, the record of its successful verification. Its `artifact` contains the exact statement and evidence that were checked. `compose.inspect()` sends those exact bytes to the installed Rust checker and returns its Markdown reading. Python does not rebuild the argument; it asks the verifier that accepted the receipt to explain it. If the receipt is missing or the evidence has changed, `inspect()` raises an error instead of showing a stale reading.

```python {run continue}
reading = compose.inspect()
```

The reading is a complete document with its own headings. To keep this chapter's outline intact and the page short, the next block quotes only the parts that answer the question: the authored claim and strategy, the checked statement, and steps 7, 8 and 9.

```python {run continue echo=false}
import re

def _inline_math(text):
    return re.sub(
        r"\$\$\n(.*?)\n\$\$",
        lambda match: "$" + " ".join(match.group(1).split()) + "$",
        text,
        flags=re.S,
    )

def compact_reading(markdown):
    commentary = markdown.split("## Author's commentary (not checked)", 1)[1]
    commentary = commentary.split("## Theorem", 1)[0]

    def authored(label):
        if label not in commentary:
            return ""
        part = commentary.split(label, 1)[1]
        for stop in ("**Claim.**", "**Strategy.**"):
            if stop in part:
                part = part.split(stop, 1)[0]
        lines = [line[2:] if line.startswith("> ") else line for line in part.splitlines()]
        return " ".join(line.strip() for line in lines if line.strip())

    theorem = markdown.split("## Theorem", 1)[1].split("## Domains", 1)[0]
    theorem = " ".join(theorem.replace("$$", "").split())
    if "\\quad" in theorem:
        quantifiers, statement = theorem.rsplit("\\quad", 1)
        theorem_lines = [f"${quantifiers}$", f"${statement.strip()}$"]
    else:
        theorem_lines = [f"${theorem}$"]
    proof = markdown.split("## Proof", 1)[1].split("## Conclusion", 1)[0]
    excerpt = proof[proof.index("**(7)**"):proof.index("**(10)**")]
    excerpt = _inline_math(excerpt)

    quote = [
        f"> **Author's claim (not checked).** {authored('**Claim.**')}",
        ">",
        f"> **Author's strategy (not checked).** {authored('**Strategy.**')}",
        ">",
        "> **Checked statement.**",
    ]
    quote += [">", *[f"> {line}" for line in theorem_lines], ">"]
    quote.append("> **Checked steps 7–9.**")
    for line in excerpt.splitlines():
        line = line[2:] if line.startswith("> ") else line
        quote.append(("> " + line) if line.strip() else ">")
    quote += [">", "> **Checked result.** Uses zero custom axioms."]
    return "\n".join(quote)

print(compact_reading(reading))
```

Step 7 gives us $Q$, the fact we called `have_q`. Step 8 gives us $R$ while the assumption $P$ is still available. Step 9 **discharges** that assumption: what we can carry out of its scope is $P \Rightarrow R$. The next two steps do the same for the other premises. This explains how the reading can report *zero custom axioms* even though our Python used `assume` three times. Each local assumption is accounted for by an arrow in the theorem. The final generalizations tell us that the argument works for every choice of $P$, $Q$ and $R$.
