---
theme: book
title: Binary Search, All the Way Down
stem: binary-search
---

# Binary Search, All the Way Down

You search for 6 in `[2, 4, 8, 11, 13]`. The first value you inspect is 8. A moment later your program has thrown away 8, 11 and 13, even though it never looked at the last two. What would convince a checker that the 6 you are looking for was not among them?

On paper you can answer in a sentence. In Logos you have to decide **where that sentence belongs**. Part of it is a promise about the input. Part is a fact available only on this branch. And part must survive the jump back to the top of the loop. Let's first separate the first two ideas in a function where there is nowhere for a useful fact to hide.

## Who has to prove that the list is nonempty?

Here is a function with a perfectly good answer on `[7]`. Try to state what it returns on `[]`. Before we can promise anything about the result, we owe Python a valid index.

```python {export=examples/declarative_calls.py}
import logos


@logos.function
def first(xs: list[int]) -> int:
    """Return the first element of a nonempty sequence."""
    return xs[0]


```

The decorator asks Logos to translate the body when Python defines the function. An unsupported construct is reported at its source line. You can still call the ordinary Python function; on an empty list the read still raises `IndexError`. We want a theorem whose statement says exactly **when** the read is safe. Give that condition a name:

```python {export=examples/declarative_calls.py}
@first.requires
def nonempty(xs):
    return 0 < logos.length(xs)


```

Now put yourself on the other side of the call. You have supplied a nonempty list. What may you rely on when the function returns?

```python {export=examples/declarative_calls.py}
@first.ensures
def returns_first(xs, *, result):
    return result == logos.nth(xs, 0)


```

In this declaration `xs` stands for any input satisfying `nonempty`, and `result` stands for the value the body returns. Checking the function connects those two promises: the premise makes index zero legal, and the expression at the return line supplies the promised value.

```python {run}
from examples.declarative_calls import first

first.check()
print("first:", first.certified)
```

Suppose your own function must accept *every* list. Can you still call `first`? Decide which line below gives you the right to do so.

```python {export=examples/declarative_calls.py}
@logos.function
def first_or_zero(xs: list[int]) -> int:
    """Return the first element, or zero when the sequence is empty."""
    if len(xs) == 0:
        return 0
    else:
        return first(xs)


```

Follow the empty list first. It leaves by the first return and never reaches the call. Now imagine reaching the second return. The test for zero failed; a length is nonnegative, so it must be positive. You have just proved `nonempty(xs)` **at the call site**. There is no reason to impose it on the caller of `first_or_zero`.

Consider this deliberately weak guarantee:

```python {export=examples/declarative_calls.py}
@first_or_zero.ensures
def zero_or_first(xs, *, result):
    return (result == 0) | (result == logos.nth(xs, 0))


```

Would an implementation that always returned zero satisfy it? Yes. Even on `[7]`, the left side of the disjunction would be true. The implementation above returns 7 there, but this particular theorem promises less. It is worth asking this question whenever a check succeeds: *would it also succeed for a program I meant to rule out?*

A postcondition that follows the two paths says what the docstring says:

```python {export=examples/declarative_calls.py}
@first_or_zero.ensures
def exact_first_or_zero(xs, *, result):
    return ((logos.length(xs) == 0) >> (result == 0)) & (
        (0 < logos.length(xs)) >> (result == logos.nth(xs, 0))
    )
```

On an empty list it demands 0; on a nonempty list it demands the first element. The same check proves both postconditions, so the weak one is still there to compare against:

```python {run}
import logos
from examples.declarative_calls import first_or_zero

first_or_zero.check()
print("first_or_zero:", first_or_zero.certified)
print("claims:", ", ".join(clause.name for clause in first_or_zero.clauses()))
logos.export_proof(first_or_zero, "first_or_zero.logos")
print("certificate: first_or_zero.logos")
```

Try deleting the empty-list branch so the call becomes unconditional. The failing obligation, `call0.requires.nonempty`, is at the call, and the message names the clause and the proposition you owe:

```text
logos.contracts.LogosContractError: contract of 'first_or_zero' does not hold:
line 23 calls 'first'; clause 'nonempty' needs 0 < len(xs)
(cannot prove order atom 0 < len(xs); ...)
```

Adding a precondition to the outer function would repair the proof by changing its promise. Restoring the guard repairs it while keeping empty lists legal.

## What will justify returning −1?

Back to the search for 6. Start with all five indices, the half-open interval `[0, 5)`. Its midpoint is 2 and the value there is 8. Move the upper bound to 2. The remaining values are 2 and 4; the next midpoint holds 4. Move the lower bound to 2. The interval is empty. Why can we now return −1?

“There's nothing left to search” is only half the argument. We also need to know that **everything already discarded was safe to discard**. Here is the program whose two assignments to the bounds we must justify.

```python {export=examples/binary_search.py}
import logos


@logos.function
def binary_search(xs: list[int], target: int) -> int:
    """Return an index holding target in a sorted sequence, or -1 if absent."""
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

Write the promise to the caller before trying to write a loop invariant. There are two ways to keep it: return −1 with evidence of absence, or return a valid index with the target at that index. With duplicates, which occurrence is allowed? Read the second alternative closely.

```python {export=examples/binary_search.py}
@binary_search.ensures
def finds_or_absent(xs, target, *, result):
    n = logos.length(xs)
    return ((result == -1) & logos.absent(xs, target)) | (
        (0 <= result) & (result < n) & (logos.nth(xs, result) == target)
    )


```

Any occurrence will do. What do we need from the caller in exchange? Run the search in your head on `[2, 0, 1]` with target 2. At index 1 it sees 0 and moves right, abandoning the answer at index 0. Here is the missing promise:

```python {export=examples/binary_search.py}
@binary_search.requires
def ordered(xs):
    return logos.sorted(xs)


```

## Work backwards from the empty interval

Let `answer == -1` mean that the search is still looking. Draw two marks on paper for `low` and `high`. What would you want written to the left of the first mark and to the right of the second? On the left, **every discarded value is too small**. On the right, **every discarded value is too large**. When the marks meet, those two statements cover every index. That is the argument for absence.

Translate the left-hand statement first. Pick an arbitrary integer `i`. You only owe a comparison if it is an actual index in the discarded prefix. The two arrows inside the quantifier introduce those restrictions.

```python {export=examples/binary_search.py}
@binary_search.invariant
def below_cut(xs, target, *, low, answer):
    return (answer == -1) >> logos.forall(
        int, lambda i: (0 <= i) >> ((i < low) >> (logos.nth(xs, i) < target))
    )


```

Write the right-hand version before reading it. The boundary is easy to miss: does index `high` belong to the remaining interval or to the discarded suffix?

```python {export=examples/binary_search.py}
@binary_search.invariant
def above_cut(xs, target, *, high, answer):
    n = logos.length(xs)
    return (answer == -1) >> logos.forall(
        int, lambda i: (high <= i) >> ((i < n) >> (target < logos.nth(xs, i)))
    )


```

Initially both claims are cheap: there are no indices below zero, and there are no valid indices at or above the length. Preservation is where the proof earns its keep. Suppose `xs[mid] < target`. When `low` becomes `mid + 1`, the old prefix stays discarded. For a *newly* discarded index $i$ between the old lower bound and the midpoint, sortedness gives $xs[i] \le xs[mid] < target$. The comparison at a single position now justifies skipping positions we never read. For the opposite branch, take an index between the midpoint and the old upper bound and try the same argument with the inequalities reversed.

Logos checks an iteration from a symbolic loop head, where it can use the declared invariants. We therefore carry the input's sortedness into the loop. The body never changes the list.

```python {export=examples/binary_search.py}
@binary_search.invariant
def keeps_order(xs):
    return logos.sorted(xs)


```

The midpoint read has its own obligation. We need `low <= mid < high` whenever the loop guard holds, with both bounds inside the original range. Should the invariant itself require `low < high`? Our search for 6 ended with both marks at 2. A good invariant still holds after that last iteration.

```python {export=examples/binary_search.py}
@binary_search.invariant
def bounds(xs, *, low, high):
    return (0 <= low) & (low <= high) & (high <= logos.length(xs))


```

## What happens to the argument when we find the target?

Search for 8 instead. The first comparison succeeds. The code saves index 2, then sets `low = high` so the loop ends. If we insisted that everything left of the new lower bound was too small, we'd be claiming that 8 is smaller than itself. This explains the guard `answer == -1` in the two cut clauses. After a match we keep a different piece of evidence: the index we will hand back.

Walk through the two exits before writing the clause. Search `[2, 4, 8]` for 6. The loop ends with `low == high == 2` and `answer == -1`. The left cut says indices 0 and 1 hold values below 6; the right cut says index 2 holds a value above 6. Together they cover the array, so `absent` holds. Now search for 8. The first comparison succeeds: `answer` becomes 2 and `low` becomes `high`. If the left cut were still active, it would claim `xs[2] < 8`, which is false. That is why the two cuts carry `answer == -1`.

At the loop head, one statement must survive either history: either a valid answer was found, or the search is unfinished and both cuts hold. Write those two alternatives as a disjunction before reading the code. `found` is the second arm of `finds_or_absent`: an in-range index holding the target. `searching` is the first arm after the loop ends with `low == high`: `answer == -1` and the two cuts together give `absent`. The sentinel `-1` is not an index; it is the mark that no answer has been recorded. That is why the cuts are guarded by `answer == -1`, and why `found` excludes the sentinel.

`searching` also repeats the cuts. Mathematically the two separate cut clauses already imply the same thing at exit. The repetition is for the current proof search: this clause is the disjunction the exit obligation splits, and deleting the repeated cuts makes `loop0.exit` fail even though the separate clauses are in scope. The conjunct `~(answer == -1)` inside `found` is different: `0 <= answer` already excludes the sentinel, so it is redundant. It is there to name the case split, not to make the proof pass.

The following clause expresses those two ways of remembering the past. Read `return found | searching` first. Which half survives the assignment `answer = mid`? Which half combines with an empty interval to justify −1?

```python {export=examples/binary_search.py}
@binary_search.invariant
def answer_or_searching(xs, target, *, low, high, answer):
    n = logos.length(xs)
    lower = logos.forall(
        int, lambda i: (0 <= i) >> ((i < low) >> (logos.nth(xs, i) < target))
    )
    upper = logos.forall(
        int, lambda i: (high <= i) >> ((i < n) >> (target < logos.nth(xs, i)))
    )
    found = (
        (0 <= answer) & (answer < n)
        & (logos.nth(xs, answer) == target) & ~(answer == -1)
    )
    searching = (answer == -1) & lower & upper
    return found | searching


```

Logos assumes the invariant clauses together at the loop head and checks each after the body. This is why the proof for one clause can use another: preserving the left cut uses both the old left cut and the sortedness fact. At loop exit the caller gets the postcondition; the caller never needs to name `low`, `high` or `answer`.

## Could a safe search run forever?

Try a one-element interval whose only value is smaller than the target. Replace `low = mid + 1` in your head with `low = mid`. The cuts and bounds can all remain true while we visit the same element forever. Which number should get smaller each time we go around?

```python {export=examples/binary_search.py}
@binary_search.decreases
def remaining(*, low, high):
    return high - low
```

The bounds keep this difference nonnegative. On a miss we exclude at least the midpoint. On a hit we reduce a nonempty interval to length zero. There is no infinite strictly decreasing sequence of nonnegative integers, so the loop must finish.

```python {run}
import logos
from examples.binary_search import binary_search

binary_search.check()
print("binary_search:", binary_search.certified)
logos.export_proof(binary_search, "binary_search.logos")
print("certificate: binary_search.logos")
```

There are now two conclusions behind that single call: execution terminates, and its answer keeps the promise we wrote before the loop proof. Python ties the function to its source. Rust checks the obligations for the translated program and the evidence supplied for each.

## Tell a broken algorithm from a broken argument

Change `(low + high) // 2` to `(low + high + 1) // 2`. Use the smallest sorted list on which the loop can run: with `[0]` and target 0, the new midpoint is 1. The read is outside the list. Here you can refute the proposed implementation with one input. The checker also refuses the proof, at the clause that tracks the discarded prefix:

```text
logos.contracts.LogosContractError: contract of 'binary_search' does not hold:
loop0.preserve.below_cut: cannot prove order atom xs[i] < target
```

Now restore the program and change just the invariant `low <= high` to `low < high`. The empty list already breaks it: both bounds start at zero, so `0 < high` is false before the loop runs. The checker also rejects the greater branch, where `high` becomes `mid`:

```text
logos.contracts.LogosContractError: contract of 'binary_search' does not hold:
loop0.preserve.bounds: cannot prove order atom high < high
```

A failed check is a reason to investigate; the input and the particular claim it violates tell you what to repair.

Finally, revisit the missing sortedness premise. The ordinary Python function still runs on this input:

```python {run}
from examples.binary_search import binary_search

xs = [2, 0, 1]
result = binary_search(xs, 2)
print(result, 2 in xs)
```

The output `-1 True` would refute an unconditional guarantee of absence. It is exactly why `ordered` belongs in the theorem. Without it, the proof stops at entry:

```text
logos.contracts.LogosContractError: contract of 'binary_search' does not hold:
main: no proof found for sorted(xs)
```

As a quick diagnostic, change the promise in a different direction: require the *first* occurrence. Give a sorted input on which the present code returns a later occurrence, and name the branch that would have to keep searching even after seeing the target.

Then write and check the contract for a smaller scan. It uses the same `-1` sentinel and result shape as `binary_search`. It visits successive indices starting at zero until it finds a match or exhausts the list:

```python
@logos.function
def find(xs: list[int], target: int) -> int:
    """Return an index holding target, or -1."""
    i = 0
    answer = -1
    while i < len(xs):
        if xs[i] == target:
            answer = i
            i = len(xs)
        else:
            i = i + 1
    return answer
```

Write its postcondition, two invariants and variant, then check it. The postcondition should say that a nonnegative result is an occurrence; it need not say that `-1` means absence. Which invariant keeps the read `xs[i]` in range, and what does the other one say about `answer` when the scan continues?

For an optional design comparison, consider a lower-bound contract for a sorted list of length `n`. It returns the first index whose value is at least `target`, or `n` if there is no such index. To the right of the cut, including the returned index when it is in range, the contract would require `target <= xs[i]`. Current proof search does not establish the full insertion-point suffix with the tactics shown here. The linear scan is the final checked exercise.
