---
theme: book
title: When a Proof Splits in Two
stem: cases
---

# When a Proof Splits in Two

A disjunction says that one of two things is true, but it does not say which. A proof that uses a disjunction must work in both cases. This chapter adds case analysis, the operations that close a contradictory branch, and the difference between a failed proof search and a checked counterexample.

## Before you start

**Prerequisites.** Writing Your First Proof and Facts That Hold Together: `p.assume`, `p.apply` on a local implication, `p.and_intro`, `left()` and `right()`.

**Outcomes.** You will split a disjunction into two scoped branches, close a branch with `p.ex_falso`, prove a negation with `p.negate`, and package a value that refutes a false universal statement.

## A disjunction is an obligation to branch

We have evidence for $P \lor Q$ and two implications, $P \Rightarrow R$ and $Q \Rightarrow R$. We need $R$ whichever side holds. Before reading the proof, fill in the missing rule in each branch.

| Branch | New local fact | Goal | Which implication has the local fact as its premise? |
| --- | --- | --- | --- |
| Left | $P$ | $R$ | ? |
| Right | $Q$ | $R$ | ? |

Use `with p.cases(either) as cases` for the split. The nested `with cases.left()` and `with cases.right()` blocks bind the fact for the corresponding side. In each block, `p.apply` uses the implication that matches the local fact, and `cases.finish` hands over evidence for $R$. Read `cases.result` after both branches finish.

```python {run}
import logos
from logos import Int, Prop, exists, lit

@logos.theorem
def dilemma(P: Prop, Q: Prop, R: Prop):
    """If both alternatives reach R, so does their disjunction."""
    return ((P >> R) & (Q >> R)) >> ((P | Q) >> R)

```

Project the two implications before entering either branch so the proof can select them from the shared assumptions.

```python {run continue}
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

The left branch uses `from_p` because its premise is $P$, and the right uses `from_q` because its premise is $Q$. Each local hypothesis can justify steps only in its own branch. The disjunction and the two implications were introduced before the split, so they are available in both. The checker combines the disjunction and both branch proofs in one disjunction-elimination step.

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

Falsehood has no introduction rule and no proof term of its own. Here it is the result of successfully applying `p.not_elim` to contradictory evidence. It is also the goal inside `p.negate`. That is why the code carries a fact for falsehood instead of a Python `False`.

## Negation is a promise of contradiction

To prove $\neg A$, assume $A$ and derive falsehood. `p.negate()` opens exactly that scope. With no argument it uses the current goal, which must be a negation. Here the assumed operand is $P \land \neg P$. Project both parts and apply the negation to the positive fact to reach falsehood.

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

Consider the claim that every integer is positive. Which integer would make $0 < n$ fail? Try zero. Substituting it for $n$ leaves the instance $\neg(0 < 0)$ to prove.

The goal is the whole existential, so name the intermediate negation explicitly with `p.negate(~(zero < zero))`. Inside that scope the assumption is $0 < 0$. The order law of strict irreflexivity, `p.order("lt_irrefl", zero)`, gives $\neg(0 < 0)$ because both sides of the comparison are the same value. Applying that negation to the assumption yields falsehood. The checker recomputes the cited law's instance.

Use `lit(0)` to build a Logos integer expression. Python would evaluate plain `0 < 0` to a boolean before Logos could construct the proposition.

```python {run continue}
@logos.theorem
def zero_not_positive():
    """There is an integer that is not positive: zero."""
    return exists(Int, lambda n: ~(lit(0) < n))

```

The finished negation supplies evidence for the chosen value. The last line passes both to `p.witness` to close the existential.

```python {run continue}
@zero_not_positive.proof
def prove_zero_not_positive(p):
    """Prove the instance fails at zero, then package zero as the witness."""
    zero = lit(0)
    with p.negate(~(zero < zero)) as suppose:
        irrefl = p.order("lt_irrefl", zero)
        falsehood = p.not_elim(irrefl, suppose.assumption)
        suppose.finish(falsehood)

    # Package the checked instance with the integer that makes it hold.
    return p.witness(0, suppose.result)
```

The checked existential $\exists n.\;\neg(0 < n)$ constructively implies $\neg\forall n.\;0 < n$. If we had a proof of the universal, applying it to the witness would give $0 < 0$, contradicting the witness's instance proof. A constructive proof of the negated universal need not supply an integer witness. Chapter 5 shows how to open an existential when you need to use its witness.

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
this case was never finished with cases.finish(...)
```

Both messages name the branch's obligation, not the original theorem. Read the expected statement first; it is the goal that the branch was supposed to reach.

## Exit exercise

1. As a warm-up, prove $((P \lor Q) \land \neg Q) \Rightarrow P$.
2. Given $((Q \Rightarrow R) \land (P \lor Q)) \land (P \Rightarrow R)$, prove $R$. For each branch, state its local fact and goal, and identify where your proof gets the rule it needs.
3. Give a checked counterexample to $\forall n.\; n < 1$ over the integers. Choose a witness and write the instantiated proposition you must prove. Then explain how it refutes the universal.

Check that all three theorems certify.
