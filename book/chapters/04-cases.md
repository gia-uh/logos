---
theme: book
title: When a Proof Splits in Two
stem: cases
---

# When a Proof Splits in Two

A disjunction says that one of two things is true, but it does not say which. A proof that uses a disjunction must work in both cases. This chapter adds case analysis, the operations that close a contradictory branch, and the difference between a failed proof search and a checked counterexample.

## Before you start

**Prerequisites.** Chapters 1 and 3: `p.assume`, `p.apply` on a local implication, `p.and_intro`, `left()` and `right()`.

**Outcomes.** You will split a disjunction into two scoped branches, close a branch with `p.ex_falso`, prove a negation with `p.negate`, and package a value that refutes a false universal statement.

## A disjunction is an obligation to branch

The following theorem is the constructive dilemma. If $P$ leads to $R$ and $Q$ leads to $R$, then the disjunction $P \lor Q$ also leads to $R$. The conclusion does not tell us which premise applies; the proof must handle both possibilities.

```python {run}
import logos
from logos import Int, Prop, exists, lit

@logos.theorem
def dilemma(P: Prop, Q: Prop, R: Prop):
    """If both alternatives reach R, so does their disjunction."""
    return ((P >> R) & (Q >> R)) >> ((P | Q) >> R)

@dilemma.proof
def prove_dilemma(p, P, Q, R):
    """Split the disjunction and use the matching implication in each branch."""
    rules = p.assume((P >> R) & (Q >> R))
    either = p.assume(P | Q)
    from_p = rules.left()
    from_q = rules.right()
    with p.cases(either) as cases:
        with cases.left() as p_case:
            cases.finish(p.apply(from_p, p_case))
        with cases.right() as q_case:
            cases.finish(p.apply(from_q, q_case))
    return cases.result
```

`p.cases(either)` opens a **scope** for each side of the disjunction. Inside `with cases.left()`, the local hypothesis `p_case` proves $P$. Inside `with cases.right()`, `q_case` proves $Q$. The two branches are independent: a fact introduced in one is not visible in the other.

Both branches must reach the same goal, here $R$. `cases.finish(...)` closes a branch by handing it a fact for that goal. After both branches are closed, `cases.result` is a fact for $R$ that depends on the original disjunction and on both branch proofs. The checker records this as one disjunction-elimination step: it has the disjunction and a proof of the goal from each side, so the conclusion follows without knowing which side holds.

The outer structure matters. `either` is assumed before the split, so it is available to `p.cases`. The two implications are projected before the split as well. If you project them inside a branch, the other branch will not see the name.

## A contradiction closes a branch

A disjunction plus the negation of one side forces the other side. In the $P$ branch, the hypothesis $P$ and the hypothesis $\neg P$ collide. A collision is a proof of falsehood, and falsehood proves anything.

```python {run continue}
@logos.theorem
def or_elim_negation(P: Prop, Q: Prop):
    """A disjunction plus the negation of one side forces the other side."""
    return ((P | Q) & ~P) >> Q

@or_elim_negation.proof
def prove_or_elim_negation(p, P, Q):
    """In the P branch, P and ~P collide; the Q branch is already the goal."""
    facts = p.assume((P | Q) & ~P)
    either = facts.left()
    not_p = facts.right()
    with p.cases(either) as cases:
        with cases.left() as p_case:
            falsehood = p.not_elim(not_p, p_case)
            cases.finish(p.ex_falso(falsehood))
        with cases.right() as q_case:
            cases.finish(q_case)
    return cases.result
```

`p.not_elim(not_p, p_case)` applies a negated fact to evidence for its operand. Its result is falsehood. `p.ex_falso(falsehood)` is the explosion rule: from falsehood it returns a fact for the **current goal**, whatever that goal is. In the left branch the goal is $Q$, so the falsehood is used to prove $Q$. In the right branch no contradiction is needed; `q_case` already proves $Q$.

Falsehood has no introduction rule and no proof term of its own. It appears only as the conclusion of a failed application, such as `p.not_elim`, or as the goal inside `p.negate`. That is why the code carries a fact for falsehood instead of a Python `False`.

## Negation is a promise of contradiction

To prove $\neg A$, assume $A$ and derive falsehood. `p.negate()` opens exactly that scope. With no argument it uses the current goal, which must be a negation.

```python {run continue}
@logos.theorem
def no_contradiction(P: Prop):
    """No proposition is both true and false."""
    return ~(P & ~P)

@no_contradiction.proof
def prove_no_contradiction(p, P):
    """Assume the conjunction, extract both sides, and derive falsehood."""
    with p.negate() as suppose:
        both = suppose.assumption
        p_fact = both.left()
        not_p = both.right()
        falsehood = p.not_elim(not_p, p_fact)
        suppose.finish(falsehood)
    return suppose.result
```

`suppose.assumption` is the fact for the operand of the negation, here $P \land \neg P$. The two projections produce $P$ and $\neg P$. `p.not_elim` combines them into falsehood. `suppose.finish(falsehood)` closes the scope and builds the negation introduction step. `suppose.result` is the fact for $\neg(P \land \neg P)$.

`p.negate(statement)` takes an optional statement when the negation you want is not the current goal. The argument must itself be a negation, such as `~(0 < 0)`. Passing a positive proposition produces the diagnostic `negate needs a negated statement`; the operation is not a generic proof-by-contradiction rule.

## A counterexample is a checked instance

A failed `check()` does not prove that a statement is false. The proof may be wrong, the automation may be incomplete, or the statement may be true and hard. To refute a universal statement you need a value and a proof that the instance fails.

Consider the false claim that every integer is positive. A counterexample is the integer zero, together with a proof that zero is not positive. Logos can state and check the counterexample as an existential.

`lit(0)` builds the integer literal zero as a Logos expression. Writing `0 < 0` directly in Python would evaluate to a Python boolean before any Logos operation saw it; `lit(0) < lit(0)` builds the proposition instead.

```python {run continue}
@logos.theorem
def zero_not_positive():
    """There is an integer that is not positive: zero."""
    return exists(Int, lambda n: ~(lit(0) < n))

@zero_not_positive.proof
def prove_zero_not_positive(p):
    """Prove the instance fails at zero, then package zero as the witness."""
    zero = lit(0)
    with p.negate(~(zero < zero)) as suppose:
        irrefl = p.order("lt_irrefl", zero)
        falsehood = p.not_elim(irrefl, suppose.assumption)
        suppose.finish(falsehood)
    return p.witness(0, suppose.result)
```

`p.order("lt_irrefl", zero)` cites the checker-owned law that no integer is less than itself. The checker recomputes the instance $\neg(0 < 0)$; Python does not get to assert it. `p.not_elim` turns the assumption $0 < 0$ into falsehood, and `p.negate` closes the negation.

The final `p.witness(0, suppose.result)` packages the value zero and the proof of the instance into evidence for $\exists n. \neg(0 < n)$. That existential is the negation of the universal $\forall n. 0 < n$. Chapter 5 explains witnesses and their scope in detail; for now, read the line as “here is the value, and here is why it works.”

## Check the four proofs

```python {run continue}
for theorem in (dilemma, or_elim_negation, no_contradiction, zero_not_positive):
    theorem.check()
    print(f"{theorem.name}: {theorem.certified}")
```

The first two proofs use disjunction elimination; the third uses negation introduction; the fourth uses a core order law and an existential witness. Each line is a receipt from the Rust checker, not a Python assertion.

## When a step fails

Suppose the left branch of `dilemma` finishes with `cases.finish(p_case)` instead of `cases.finish(p.apply(from_p, p_case))`. The branch has evidence for $P$, but the goal is $R$:

```text
the evidence does not prove the expected statement
  expected: R
  got: P
```

The branch is closed, so the failure is reported at the point where the branch hands over its evidence. The repair is not to change the goal; it is to apply the implication that turns $P$ into $R$.

A different mistake leaves one branch unfinished. If the right branch has no `cases.finish`, the error is:

```text
both branches of a case analysis need evidence
```

Both messages name the branch's obligation, not the original theorem. Read the expected statement first; it is the goal that the branch was supposed to reach.

## Exit exercise

Prove

$$\bigl((P \lor Q) \land \neg Q\bigr) \;\Rightarrow\; P.$$

It is `or_elim_negation` with the two sides exchanged. Split the disjunction, and in the $Q$ branch use $Q$ and $\neg Q$ to derive falsehood before closing with `p.ex_falso`. The $P$ branch is already the goal.

Then state the counterexample theorem for the false universal $\forall n. n < 0$: prove $\exists n. \neg(n < 0)$ with witness zero and an instance proof. Which checker-owned law do you need for $\neg(0 < 0)$?
