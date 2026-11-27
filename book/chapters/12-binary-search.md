---
theme: book
title: Binary Search, All the Way Down
stem: binary-search
---

# Binary Search, All the Way Down

Binary search is short enough to fit on a screen and easy enough to get wrong. The version in this chapter returns any occurrence of a target in a sorted sequence, or $-1$ exactly when the target is absent. It handles the empty sequence, repeated values and a target below or above every element. The proof is total: every run terminates, every array read is in bounds, and the returned value satisfies the postcondition.

The function is ordinary Python. The contract is written in Logos, and the proof is checked twice: once while the page runs, and once by the standalone Rust checker against the exported certificate.

## Before you start

**Prerequisites.** Chapters 6 and 7: transparent definitions, checked lemmas, case analysis and linear arithmetic. You should be comfortable reading an implication and a conjunction.

**Outcomes.** You will bind a contract to an executable function with a loop, read the four parts of a loop invariant, follow the three branches of binary search, check the bounds obligation for every array read, see why the variant proves termination, and reproduce two failures: a shifted midpoint and a weakened invariant. You will also see a concrete input on which the function is wrong when the sortedness precondition is removed.

## The function

The function lives in `examples/binary_search.py`. The block below is the part of that file that defines it: the page writes the block to the file and imports the result, because a contract is bound to the module that defines the function. What you read is exactly what the checker binds.

```python {export=examples/binary_search.py}
import logos
from logos.expr import Lit, Var


def binary_search(xs: list[int], target: int) -> int:
    low = 0
    high = len(xs)
    answer = -1
    while low < high:
        mid = (low + high) // 2
        if xs[mid] == target:
            answer = mid
            low = high
        elif xs[mid] < target:
            low = mid + 1
        else:
            high = mid
    return answer


```

The bounds are half-open: `low` is included and `high` is excluded. The loop stops when the interval is empty. `answer` starts at $-1$ and is overwritten only when `xs[mid]` equals the target. The equality branch also sets `low = high`, which exits the loop without a second condition.

## Sortedness is the precondition

`logos.sorted(xs)` is a checker-owned predicate: for every $0 \le i \le j < \operatorname{len}(xs)$, the element at $i$ is at most the element at $j$. It is not a test over one array; it is a hypothesis over every pair of in-range indices. The contract asks for it explicitly:

```python {export=examples/binary_search.py}
@logos.theorem(about=binary_search)
def binary_search_correct(xs, target, *, result):
    low = Var("low", int)
    high = Var("high", int)
    answer = Var("answer", int)
    n = logos.length(xs)

    lower_cut = logos.forall(
        int, lambda i: (Lit(0) <= i) >> ((i < low) >> (logos.nth(xs, i) < target))
    )
    upper_cut = logos.forall(
        int, lambda i: (high <= i) >> ((i < n) >> (target < logos.nth(xs, i)))
    )
    found = (
        (Lit(0) <= answer)
        & (answer < n)
        & (logos.nth(xs, answer) == target)
        & ~(answer == -1)
    )
    searching = (answer == -1) & lower_cut & upper_cut
    invariant = (
        logos.sorted(xs)
        & (Lit(0) <= low)
        & (low <= high)
        & (high <= n)
        & (found | searching)
    )
    ensures = (
        ((result == -1) & logos.absent(xs, target))
        | ((Lit(0) <= result)
           & (result < n)
           & (logos.nth(xs, result) == target))
    )
    return logos.program_contract(
        requires=logos.sorted(xs),
        ensures=ensures,
        invariant=invariant,
        variant=high - low,
    )


```

The postcondition has two arms. The first says that $-1$ is returned exactly when every in-range element differs from the target. The second says that a non-negative result is an in-range index holding the target. The two arms overlap only in impossible cases, and the proof does not need to choose between them until the loop exits.

## The invariant, piece by piece

The invariant is a conjunction of five facts. Each one has a job:

| Conjunct | What it says | Why the loop needs it |
| --- | --- | --- |
| `sorted(xs)` | The array is ordered | The comparison at `mid` rules out a whole side |
| `0 <= low` | The left bound is a valid index or the empty end | The read `xs[mid]` is in range |
| `low <= high` | The interval is not inverted | The variant is non-negative |
| `high <= n` | The right bound is inside the array | The read and the lower cut stay meaningful |
| `found \| searching` | An occurrence is recorded, or both cuts are still true | The postcondition at exit |

The two cuts are the interesting part. `lower_cut` says every index below `low` holds something smaller than the target. `upper_cut` says every index at or above `high` holds something larger. They are not about the elements the loop has visited; they are about the two regions the loop has ruled out.

`found` says the answer is an in-range occurrence. `searching` says no answer has been recorded and both cuts hold. The disjunction is the loop's memory: either the answer is already safe, or the search is still honest about what remains.

## Three branches, three obligations

The checker turns the loop into verification conditions. The `preserve` obligation is one implication whose antecedent is the invariant and the loop condition, and whose consequent is the invariant after the body. The body has three branches, so the proof has three paths even though the source has one `if`/`elif`/`else`.

**Equality: `xs[mid] == target`.** The branch sets `answer = mid` and `low = high`. `mid` is in `[low, high)` by the bounds conjunct and the half-interval laws, so `found` holds. The cuts are irrelevant because the disjunction is already true. The new interval is empty, so the variant is zero.

**Less: `xs[mid] < target`.** The branch sets `low = mid + 1`, so every index below the new `low` is at most `mid`. Indices below the old `low` are covered by `lower_cut`. The newly discarded interior indices, `low <= i < mid`, are covered by sortedness together with the branch comparison: `xs[i] <= xs[mid] < target`. The upper cut is unchanged.

**Greater: `target < xs[mid]`.** The branch sets `high = mid`, so every index at or above the new `high` is at least `mid`. Index `mid` itself is the branch comparison, the newly discarded interior indices `mid < i < high` satisfy `target < xs[mid] <= xs[i]` by sortedness, and indices at or above the old `high` are covered by `upper_cut`. The lower cut is unchanged.

The three branches are not three separate proofs in the certificate. They are one checked `preserve` condition whose proof splits on the same guards the source uses. The Rust checker recomputes that condition from the exported statements; the Python side only proposes the invariant and the proof terms.

## Bounds and the variant

Every read of `xs[mid]` creates a `read` obligation: under the path condition, $0 \le mid < \operatorname{len}(xs)$. The invariant gives $0 \le low$ and $high \le n$. The loop condition gives $low < high$. The half-interval laws give $low \le (low+high)//2 < high$. The obligation follows by transitivity. This is why the empty sequence needs no special case: the loop never runs, so there is no read.

The variant is `high - low`. It is non-negative because `low <= high`. In the equality branch it becomes zero. In the less branch `low` becomes `mid + 1`, which is strictly greater than the old `low` and at most the old `high`. In the greater branch `high` becomes `mid`, which is strictly less than the old `high` and at least the old `low`. Every branch decreases the interval, so the loop terminates.

## Empty inputs, duplicates and absent targets

The empty sequence has `low = high = 0`, so the loop is skipped and `answer = -1` is returned. `absent(xs, target)` is vacuously true because there is no in-range index. The postcondition's first arm holds.

A sequence of duplicates is handled by the equality branch. The function returns the first `mid` it meets, not the first or last occurrence. The postcondition asks for *an* occurrence, so any of them is correct. The two cuts do not try to identify a canonical occurrence.

An absent target ends with `low >= high` and `answer = -1`. The lower cut says every index below `low` is too small, the upper cut says every index at or above `high` is too large, and `sorted_gap` combines them into `absent(xs, target)`. The empty interval is the point where the two ruled-out regions meet.

## Check, inspect and export

The module ends with the entry point the file runs when you call it directly:

```python {export=examples/binary_search.py}
def main() -> None:
    binary_search_correct.check()
    print("binary_search_correct:", binary_search_correct.certified)
    print("obligations:", ", ".join(binary_search_correct.program.obligations))
    logos.export_proof(binary_search_correct, "binary_search.logos")
    print("certificate: binary_search.logos")


if __name__ == "__main__":
    main()
```

The page imports the module and runs the same function, so the output below is the file's own:

```python {run}
from examples.binary_search import main

main()
```

The checker reports seven obligations: `loop0.preserve`, `loop0.exit`, `loop0.variant_nonnegative`, `loop0.variant_decreases`, `read0`, `read1` and `main`. The two read obligations cover the two occurrences of `xs[mid]` in the source. Each one has a proof term in the certificate. The `main` obligation connects the precondition to the initial invariant and the postcondition; it is where `sorted(xs)` is used for the first time.

The exported file is checked without Python:

```bash
logos check --strict binary_search.logos
```

The expected last line is `Verified with 0 custom axioms`. The statement quantifies over every finite integer sequence and every integer target, not over a sample.

## The counterexample when the precondition is missing

Remove `requires=logos.sorted(xs)`, or replace it with `logos.lit(True)`. The invariant still contains `sorted(xs)`, but nothing establishes it at entry. The proof fails at the first obligation:

```text
logos.proofs.ProofSearchError: main: no proof found for sorted(xs)
```

That is a proof failure, not yet a counterexample. The counterexample is an input on which the executable function violates the postcondition. Take

$$xs = [2, 0, 1], \qquad target = 2.$$

The array is not sorted. The function examines index 1, sees 0, moves right, examines index 2, sees 1, moves right, and returns $-1$. The target is present at index 0.

```python {run}
from examples.binary_search import binary_search

example = [2, 0, 1]
result = binary_search(example, 2)
print("result:", result)
print("target present:", 2 in example)
print("postcondition holds:", result != -1 and example[result] == 2)
```

The output is `result: -1`, `target present: True`, `postcondition holds: False`. The missing premise is not a formality: without it the theorem is false, and this is the value that makes it false. A failed tactic alone would not prove that; the executable run does.

## When a step fails

Two mutations are worth keeping.

**Shift the midpoint.** Replace `mid = (low + high) // 2` with `mid = (low + high + 1) // 2`. The interval can fail to shrink: when `high = low + 1`, the new midpoint is `high`, and the greater branch sets `high = mid`, which does not move. The `preserve` obligation fails before termination is even considered:

```text
logos.proofs.ProofSearchError: loop0.preserve: cannot prove disjunction
((0 <= (low + high + 1) // 2 & (low + high + 1) // 2 < len(xs))
 & xs[(low + high + 1) // 2] = target) & ~((low + high + 1) // 2 = -1) | ...
```

The message is long because it is the whole post-body invariant. The part to read is the shifted midpoint in every read and every cut. The original proof terms no longer match the recomputed condition.

**Weaken the invariant.** Replace `low <= high` with `low < high`. The invariant is now false at exit: the loop stops exactly when `low >= high`, and the equality branch sets `low = high`. The `preserve` obligation fails on the greater branch, where `high` becomes `mid` and the new interval can be empty:

```text
logos.proofs.ProofSearchError: loop0.preserve: cannot prove order atom high < high
```

The message names the impossible strict inequality. The repair is not to weaken the postcondition; it is to keep the non-strict bound that the exit condition actually gives.

## Exit exercise

State the contract for a variant that returns `low` instead of `answer`, the leftmost insertion point. The postcondition becomes

$$\bigl(\forall i.\ 0 \le i < low \Rightarrow xs[i] < target\bigr)
  \land \bigl(\forall i.\ low \le i < n \Rightarrow target \le xs[i]\bigr).$$

Which conjunct of the current invariant replaces `found | searching`? Which branch no longer needs to record an answer? Prove the new contract with `logos.program_contract` and check that the variant is still `high - low`.

As a second exercise, explain why the current invariant is enough for *some* occurrence but not for the first one. The equality branch stops at the first midpoint it meets; the cuts do not say that no earlier occurrence exists. A leftmost contract needs a cut that is strict on both sides, and the equality branch must keep searching left instead of exiting.
