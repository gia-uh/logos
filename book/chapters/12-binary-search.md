---
theme: book
title: Binary Search, All the Way Down
stem: binary-search
---

# Binary Search, All the Way Down

The previous chapters proved statements that stood on their own. A contract about a function is different: it talks about the code that will run, and it has to survive every input the function accepts. Binary search is short enough to fit on a screen and easy enough to get wrong. This chapter declares its contract beside the function, in ordinary Python, and lets the Rust checker replay the result.

The path has three steps. First a function with no loop, so the syntax and the two promises are visible. Then a function that calls it, so a precondition becomes an obligation at a particular line. Only then binary search, where the new idea is a named loop invariant that survives one iteration.

## Before you start

**Prerequisites.** Chapters 6 and 7: transparent definitions, checked lemmas, case analysis and linear arithmetic. You should be comfortable reading an implication, a conjunction and a quantifier.

**Outcomes.** You will declare a function with `@logos.function`, name its `requires`, `ensures`, `invariant` and `decreases` clauses, see unsupported syntax refused at its own line, prove a call-site precondition, read several named invariants that are assumed together and preserved one by one, and reproduce three failures: a shifted midpoint, a weakened bound, and a missing sortedness premise. You will also see a concrete input on which the executable function is wrong when sortedness is removed.

## A function and its promises

The first module is a complete, runnable file. It defines `first`, names what a caller must provide, names what the result satisfies, and then defines a caller that uses both promises.

```python {export=examples/declarative_calls.py}
import logos


@logos.function
def first(xs: list[int]) -> int:
    """Return the first element of a nonempty sequence."""
    return xs[0]


@first.requires
def nonempty(xs):
    return 0 < logos.length(xs)


@first.ensures
def returns_first(xs, *, result):
    return result == logos.nth(xs, 0)


@logos.function
def first_or_zero(xs: list[int]) -> int:
    """Return the first element, or zero when the sequence is empty."""
    if len(xs) == 0:
        return 0
    else:
        return first(xs)


@first_or_zero.ensures
def zero_or_first(xs, *, result):
    return (result == 0) | (result == logos.nth(xs, 0))


def main() -> None:
    first.check()
    first_or_zero.check()
    print("first:", first.certified)
    print("first obligations:", ", ".join(first.program.obligations))
    print("first_or_zero:", first_or_zero.certified)
    print("caller obligations:", ", ".join(first_or_zero.program.obligations))
    logos.export_proof(first_or_zero, "first_or_zero.logos")
    print("certificate: first_or_zero.logos")


if __name__ == "__main__":
    main()
```

`@logos.function` is a declaration, not a wrapper. It reads the function's source and either translates the body or raises at the first construct Logos cannot represent. That check happens when the module is imported, before any clause below it is declared, so a mistake in the body never waits for a proof attempt. The decorator returns the same function object: calling `first([])` still raises the ordinary `IndexError`. Logos never inserts a runtime contract check.

`@first.requires` names a promise the **caller** makes. `@first.ensures` names a promise the **implementation** returns. The clause parameters are symbolic and are bound by name: `xs` is the parameter, and `result` is the returned value. A clause is an ordinary Python function that returns a Logos expression, so `0 < logos.length(xs)` is a proposition, not a test on a particular list. The clause's own name, `nonempty` or `returns_first`, is what appears in diagnostics and in the reading below.

`first.check()` is where the proof happens. It proves that every read of `xs[0]` is in bounds, that the returned value satisfies `returns_first`, and it sends the certificate to the Rust checker. The module's output is:

```python {run}
from examples.declarative_calls import main

main()
```

`first` has two obligations: `read0`, the bounds of `xs[0]`, and `main`, the postcondition from the precondition. The caller adds `call0.requires.nonempty`, the promise `first` asks of its caller at the call on the `else` branch.

The reading produced by `inspect` is the checker's, not Python's reconstruction. The header carries the author's labels; the derivation below it carries one checked step per obligation.

::: proof
```python {run}
from examples.declarative_calls import first

first.check()
print(first.inspect())
```
:::

## A caller owes the precondition

At `return first(xs)`, the caller owes `nonempty(xs)` for the actual argument on that path. The `else` branch gives `len(xs) != 0`. The checker owns the fact that a length is nonnegative, so the two together give `0 < len(xs)`. Once that obligation is discharged, the caller may use `returns_first` and conclude that the returned value is `xs[0]`.

Remove the guard and the same call is refused. The body would be

```python
@logos.function
def first_or_zero(xs: list[int]) -> int:
    return first(xs)
```

and `.check()` stops before writing any certificate:

```text
logos.contracts.LogosContractError: contract of 'first_or_zero' does not hold:
line 3 calls 'first'; clause 'nonempty' needs 0 < len(xs)
(cannot prove order atom 0 < len(xs); ...)
```

Three things are named: the line of the call, the callee `first`, and the clause `nonempty`. The last part is the proposition that was missing. A declared `requires` is not an axiom: the caller cannot assume it, and the callee's `ensures` is usable only after the callee program itself has been verified. The exported file carries the callee program and the exact call site, so the Rust checker reaches the same conclusion without Python.

## Binary search

The function is the one from the previous chapter, unchanged. The contract is now eight separate named functions instead of one `program_contract(...)` expression. There is no `Var("low", int)` and no code inside a string: the loop-head locals are bound by name in the clause signatures.

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


@binary_search.requires
def ordered(xs):
    return logos.sorted(xs)


@binary_search.invariant
def bounds(xs, *, low, high):
    return (0 <= low) & (low <= high) & (high <= logos.length(xs))


@binary_search.invariant
def keeps_order(xs):
    return logos.sorted(xs)


@binary_search.invariant
def below_cut(xs, target, *, low, answer):
    return (answer == -1) >> logos.forall(
        int, lambda i: (0 <= i) >> ((i < low) >> (logos.nth(xs, i) < target))
    )


@binary_search.invariant
def above_cut(xs, target, *, high, answer):
    n = logos.length(xs)
    return (answer == -1) >> logos.forall(
        int, lambda i: (high <= i) >> ((i < n) >> (target < logos.nth(xs, i)))
    )


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


@binary_search.decreases
def remaining(*, low, high):
    return high - low


@binary_search.ensures
def finds_or_absent(xs, target, *, result):
    n = logos.length(xs)
    return ((result == -1) & logos.absent(xs, target)) | (
        (0 <= result) & (result < n) & (logos.nth(xs, result) == target)
    )


def main() -> None:
    binary_search.check()
    print("binary_search:", binary_search.certified)
    print("obligations:", ", ".join(binary_search.program.obligations))
    logos.export_proof(binary_search, "binary_search.logos")
    print("certificate: binary_search.logos")


if __name__ == "__main__":
    main()
```

The bounds are half-open: `low` is included and `high` is excluded. The loop stops when the interval is empty. `answer` starts at $-1$ and is overwritten only when `xs[mid]` equals the target. The equality branch also sets `low = high`, which exits the loop without a second condition.

`ordered` is the only precondition. `logos.sorted(xs)` is a checker-owned predicate: for every $0 \le i \le j < \operatorname{len}(xs)$, the element at $i$ is at most the element at $j$. It is not a test over one array; it is a hypothesis over every pair of in-range indices. Without it the theorem is false, as the counterexample at the end shows.

## The clauses, one at a time

The loop has five named invariants and one named variant. Logos assumes all five together at the loop head and proves each one after every iteration, as a separate obligation named `loop0.preserve.` followed by the clause name. A failure therefore points at the clause that broke, not at an anonymous conjunction.

| Clause | What it says | Why the loop needs it |
| --- | --- | --- |
| `bounds` | `0 <= low <= high <= len(xs)` | The read `xs[mid]` is in range and the interval cannot invert |
| `keeps_order` | `sorted(xs)` | The comparison at `mid` rules out a whole side |
| `below_cut` | while no answer is recorded, every index below `low` holds something smaller than the target | The left discarded region stays honest |
| `above_cut` | while no answer is recorded, every index at or above `high` holds something larger | The right discarded region stays honest |
| `answer_or_searching` | an occurrence is recorded, or no answer exists yet and both cuts hold | The postcondition at exit |

The two cuts are guarded by `answer == -1`. That is not decoration. In the equality branch the answer is recorded and the loop exits, so the cuts no longer have to describe the interior between `low` and `high`; the disjunction in `answer_or_searching` is already true through `found`. Without the guard, `below_cut` would be false after the equality branch, because the target sits inside the interval that was just abandoned.

`answer_or_searching` repeats the two cuts without the guard. It is the loop's memory: either the answer is already safe, or the search is still honest about what remains. The exit obligation uses that disjunction to split into the two arms of the postcondition.

`remaining` is the variant. Its name appears in `loop0.variant_nonnegative.remaining` and `loop0.variant_decreases.remaining`, so a termination failure names the clause the author wrote rather than a generated ghost.

## Three branches, three obligations

The checker turns the loop into verification conditions. Each preserved clause is one implication whose antecedent is all five invariants and the loop condition, and whose consequent is that clause after the body. The body has three branches, so each proof has three paths even though the source has one `if`/`elif`/`else`.

**Equality: `xs[mid] == target`.** The branch sets `answer = mid` and `low = high`. `mid` is in `[low, high)` by `bounds` and the half-interval laws, so `answer_or_searching` holds through `found`. The two cuts are vacuous because `answer != -1`. The new interval is empty, so `remaining` is zero.

**Less: `xs[mid] < target`.** The branch sets `low = mid + 1`. Every index below the new `low` is at most `mid`. Indices below the old `low` are covered by `below_cut`. The newly discarded interior indices, `low <= i < mid`, are covered by `keeps_order` together with the branch comparison: `xs[i] <= xs[mid] < target`. The upper cut is unchanged.

**Greater: `target < xs[mid]`.** The branch sets `high = mid`. Every index at or above the new `high` is at least `mid`. Index `mid` itself is the branch comparison, the newly discarded interior indices `mid < i < high` satisfy `target < xs[mid] <= xs[i]` by `keeps_order`, and indices at or above the old `high` are covered by `above_cut`. The lower cut is unchanged.

## Bounds and the variant

Every read of `xs[mid]` creates a `read` obligation: under the path condition, $0 \le mid < \operatorname{len}(xs)$. The `bounds` clause gives $0 \le low$ and $high \le n$. The loop condition gives $low < high$. The half-interval laws give $low \le (low+high)//2 < high$. The obligation follows by transitivity. This is why the empty sequence needs no special case: the loop never runs, so there is no read.

The variant is `high - low`. It is non-negative because `low <= high`. In the equality branch it becomes zero. In the less branch `low` becomes `mid + 1`, which is strictly greater than the old `low` and at most the old `high`. In the greater branch `high` becomes `mid`, which is strictly less than the old `high` and at least the old `low`. Every branch decreases the interval, so the loop terminates.

## Empty inputs, duplicates and absent targets

The empty sequence has `low = high = 0`, so the loop is skipped and `answer = -1` is returned. `absent(xs, target)` is vacuously true because there is no in-range index. The postcondition's first arm holds.

A sequence of duplicates is handled by the equality branch. The function returns the first `mid` it meets, not the first or last occurrence. The postcondition asks for *an* occurrence, so any of them is correct. The cuts do not try to identify a canonical occurrence.

An absent target ends with `low >= high` and `answer = -1`. The lower cut says every index below `low` is too small, the upper cut says every index at or above `high` is too large, and `sorted_gap` combines them into `absent(xs, target)`. The empty interval is the point where the two ruled-out regions meet.

## Check, inspect and export

The module's entry point is the block the page runs:

```python {run}
from examples.binary_search import main

main()
```

The checker reports eleven obligations: `loop0.preserve.bounds`, `loop0.preserve.keeps_order`, `loop0.preserve.below_cut`, `loop0.preserve.above_cut`, `loop0.preserve.answer_or_searching`, `loop0.exit`, `loop0.variant_nonnegative.remaining`, `loop0.variant_decreases.remaining`, `read0`, `read1` and `main`. The two read obligations cover the two occurrences of `xs[mid]` in the source. Each one has a proof term in the certificate. The `main` obligation connects the precondition to the initial invariants and the postcondition.

The reading starts with the clause names the author wrote and the checked theorem.

```python {run}
from examples.binary_search import binary_search

binary_search.check()
for line in binary_search.inspect().splitlines():
    if line.startswith("- `") or line.startswith("**Contract.**"):
        print(line)
```

The rest of the reading is a checked derivation with one step per obligation. The full document is what `inspect` returns, and the Rust checker produces it from the same certificate bytes that it verified.

The exported file is checked without Python:

```bash
logos check --strict binary_search.logos
```

The expected last line is `Verified with 0 custom axioms`. The statement quantifies over every finite integer sequence and every integer target, not over a sample.

## The counterexample when the precondition is missing

Weaken `ordered` so it returns a true proposition that says nothing about order, for example `0 <= logos.length(xs)`. The invariant `keeps_order` still contains `sorted(xs)`, but nothing establishes it at entry. The proof fails at the first obligation:

```text
logos.contracts.LogosContractError: contract of 'binary_search' does not hold:
main: no proof found for sorted(xs)
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

The output is `result: -1`, `target present: True`, `postcondition holds: False`. The missing premise is not a formality: without it the theorem is false, and this is the value that makes it false. A failed proof alone would not prove that; the executable run does.

## When a step fails

Three mutations are worth keeping. Each one fails at a named clause, and none writes a certificate.

**Shift the midpoint.** Replace `mid = (low + high) // 2` with `mid = (low + high + 1) // 2`. The interval can fail to shrink: when `high = low + 1`, the new midpoint is `high`, and the greater branch sets `high = mid`, which does not move. The `bounds` clause fails before termination is even considered:

```text
loop0.preserve.bounds: cannot prove order atom (low + high + 1) // 2 + 1 <= high
```

The message names the clause, not an anonymous preserve condition. The part to read is the shifted midpoint in the inequality.

**Weaken the bound.** Replace `low <= high` with `low < high` inside `bounds`. The invariant is now false at exit: the loop stops exactly when `low >= high`, and the equality branch sets `low = high`. The `bounds` clause fails on the greater branch:

```text
loop0.preserve.bounds: cannot prove order atom high < high
```

The message names the impossible strict inequality. The repair is not to weaken the postcondition; it is to keep the non-strict bound that the exit condition actually gives.

**Remove sortedness.** Replace the body of `ordered` with `0 <= logos.length(xs)`. The proof fails at `main`, as above. The counterexample in the previous section shows that the failure is real.

## What the checker trusts

The trust boundary is deliberately small.

- **Python translates; Rust checks.** The decorators read the module source, build a program and clause propositions, and propose proof terms. None of that is trusted. The Rust checker recomputes every verification condition from the program in the certificate and checks every proof term with the core rules.
- **A call is not an axiom.** At `first(xs)`, the caller owes `nonempty(xs)` for those actual arguments under that path condition. The callee's `ensures` is used only after the checker has verified the callee's program in the same certificate. The artifact carries the callee program, its clauses and the call site; the checker verifies callees before callers, rejects a call to a program that is missing or unverified, rejects a recorded contract that differs from the program, and rejects a cycle in the call graph.
- **The source binding is Python's job.** Every `check`, `inspect` and `export` re-reads the defining module, compares the imported code object with a fresh compile, compares the source the declaration was built from, and revisits every transitive callee. A source change, a clause change or a rebinding of a callee refuses with a message asking you to redeclare. The Rust checker cannot see your source; it verifies the artifact as given.
- **No runtime enforcement.** The decorated object is the original function. There is no wrapper, no precondition check before a call, and no postcondition check after one. `first([])` raises `IndexError`, not a contract error.

The supported fragment is deliberately narrow: `int` and `list[int]`, straight-line assignments, one `if`/`else` tree, one `while` loop with a final return, direct calls to module-level functions declared with `@logos.function`, and the integer and sequence operations the previous chapters use. Recursion, arbitrary calls, list mutation, early returns inside a loop and unchecked declarations used as axioms are outside it. A function that needs them is refused at its source line, not approximated.

## Exit exercise

State the contract for a variant that returns `low` instead of `answer`, the leftmost insertion point. The postcondition becomes

$$\bigl(\forall i.\ 0 \le i < low \Rightarrow xs[i] < target\bigr)
  \land \bigl(\forall i.\ low \le i < n \Rightarrow target \le xs[i]\bigr).$$

Which clauses replace `answer_or_searching`? Which branch no longer needs to record an answer? Prove the new contract with the declarative decorators and check that `remaining` is still `high - low`.

As a second exercise, explain why the current clauses are enough for *some* occurrence but not for the first one. The equality branch stops at the first midpoint it meets; the cuts do not say that no earlier occurrence exists. A leftmost contract needs a cut that is strict on both sides, and the equality branch must keep searching left instead of exiting.
