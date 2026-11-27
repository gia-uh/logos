# Logos

Logos lets people and AI agents prove claims about symbolic models in Python and send the proof to someone else to check. A domain can discover a solution, or an author can guide the search with tactics written in Python. The result is a portable `.logos` file. A recipient needs only the Rust executable to verify it offline, inspect its assumptions, or read the derivation as mathematics.

The [English book](https://github.com/gia-uh/logos/tree/main/book) is the guided path from the first checked proof through number theory to Euclid's theorem, followed by a Developer Guide for extending the checked language and a generated Public API Reference. Its chapters are executable Scriptorium sources.

## Install

Logos has two parts. The Python package is `logos-ai`, imported as `logos`; it authors proofs. The `logos` executable is the Rust checker that verifies them. Python 3.12 or newer is required.

Install the Python package with pip:

```bash
python3 -m venv .venv
source .venv/bin/activate
python -m pip install logos-ai
```

Install the checker from source with Cargo, on Linux or macOS:

```bash
git clone https://github.com/gia-uh/logos.git
cd logos
cargo install --locked --path checker
export PATH="${CARGO_HOME:-$HOME/.cargo}/bin:$PATH"
logos --version
```

`theorem.check()` runs `logos check --json -` and sends the artifact on standard input. If the executable is not on `PATH`, the Python call fails with `installed Rust logos checker not found on PATH`.

The release wheel also carries the rendered book and its PDF for offline reading. After installing the wheel:

```bash
python -m logos book --pdf     # print the bundled PDF path
python -m logos book --open    # open the offline HTML book
python -m logos book --serve   # serve it on localhost, for search and links
```

From Python, `import logos.book` exposes `logos.book.pdf()`, `logos.book.site()` and `logos.book.index()`.

## Describe a puzzle and solve it

On an island, every inhabitant is either a knight who tells the truth or a knave who lies. A tells B, “We are both knaves.” This complete Python example asks the domain to discover their roles and export its proof:

```python
from logos.domains.logic_puzzles import KnightsKnaves

puzzle = KnightsKnaves()
a, b = puzzle.entity("A"), puzzle.entity("B")
a.says(a.is_knave() & b.is_knave())

print(puzzle.solve())  # {'A': 'knave', 'B': 'knight'}
puzzle.export_proof("roles.logos")
```

If A were a knight, the statement would be true and A would be a knave. Thus A is a knave and the statement is false. B must be a knight. The checker verifies that this conclusion follows from the role rules and A’s utterance, all of which appear as premises.

To run the example from an empty working directory with the tools installed:

```bash
logos example knights-knaves
python solve_knights_knaves.py roles.logos
logos check --strict roles.logos
logos inspect --markdown roles.logos > proof.md
```

The same command also writes `guide_knights_knaves.py`, which shows how to supply one strategic choice: split on A’s role. Run it without arguments to preview A’s utterance and the proposed claim in English. Give it an output filename to build the guided proof. [Domain guide](https://github.com/gia-uh/logos/blob/main/docs/portable-proof-format.md#knights-and-knaves-example)

## Write a theorem and choose tactics

To guide a proof directly, state the property as a Python function. Here `intro` introduces two arbitrary integers, and `ring` builds a derivation using the integer ring laws.

```python
import logos
from logos import tactics as t

@logos.theorem
def square_of_sum(x: int, y: int):
    return (x + y)**2 == x**2 + 2*x*y + y**2

logos.check(square_of_sum.proof(t.intro("x", "y"), t.ring()))
logos.export_proof(square_of_sum, "square.logos")
```

A custom tactic can inspect the current goal and return evidence, or split it into subgoals and combine their proofs. Rust checks the resulting derivation independently of the tactic.

## Declare a contract beside the function

`@logos.function` reads the function's source and either translates the body or refuses at the first construct it cannot represent, before any clause is declared. Clauses are separate Python functions named by their function names. Their parameters are symbolic and bound by name; `result` is bound only in a postcondition. The decorator returns the original function, so there is no wrapper and no runtime check.

```python
import logos


@logos.function
def first(xs: list[int]) -> int:
    return xs[0]


@first.requires
def nonempty(xs):
    return 0 < logos.length(xs)


@first.ensures
def returns_first(xs, *, result):
    return result == logos.nth(xs, 0)


first.check()
logos.export_proof(first, "first.logos")
```

A caller owes the callee's precondition at the call, using the facts available on that path. The callee's postcondition is usable only after its program has been verified.

```python
@logos.function
def first_or_zero(xs: list[int]) -> int:
    if len(xs) == 0:
        return 0
    else:
        return first(xs)


first_or_zero.check()
```

Checking the caller proves `call0.requires.nonempty` for the `else` branch. Removing the guard is refused with the call line, the callee, the clause and the needed proposition. The certificate carries the callee program and the call site, so the Rust checker replays the dependency without Python. Run the [declarative example](https://github.com/gia-uh/logos/blob/main/book/examples/declarative_calls.py) and read the [binary-search chapter](https://github.com/gia-uh/logos/blob/main/book/chapters/12-binary-search.md) for named invariants and a guarded caller.

## Prove a contract about an ordinary function

`@logos.theorem(about=fn)` binds the theorem to `fn`'s own source. The decorated body returns `logos.contract`, whose `ensures` is a postcondition over the parameters and the keyword-only `result`. Logos reads the function's module, recompiles it, and refuses to continue if the imported code object disagrees with the source. Every check, certification and export repeats that binding and compares the fresh signature and translation with the ones the statement was built from, so replacing `__code__`, reordering parameters or editing the source after decoration cannot certify stale mathematics.

```python
import logos


def advance(mid: int) -> int:
    return mid + 1


@logos.theorem(about=advance)
def advances(mid, *, result):
    return logos.contract(ensures=(result - mid == 1))


advances.check()
logos.export_proof(advances, "advance.logos")
```

The checked statement is `∀ mid:int, ∀ result:int, result = advance(mid) → result - mid = 1`, and `advance` is declared to the checker as the transparent function extracted from the source body. Run the [runnable example](https://github.com/gia-uh/logos/blob/main/examples/function_contract.py) with `python examples/function_contract.py`, then `logos check --strict advance.logos`.

An optional `requires=` becomes an explicit antecedent, so a conditional contract is never silently dropped:

```python
@logos.theorem(about=advance)
def advance_at_zero(mid, *, result):
    return logos.contract(requires=(mid == 0), ensures=(result - mid == 1))
```

A function with one equality branch is proved one path at a time. The `requires=` must select the path: the condition selects the then branch and its negation selects the else branch. The exported transparent definition is that branch, labelled `step[then]` or `step[else]`, so the certificate is not read as defining the whole function.

```python
def step(x: int) -> int:
    if x == 0:
        return 1
    else:
        return x + 1


@logos.theorem(about=step)
def step_at_zero(x, *, result):
    return logos.contract(requires=(x == 0), ensures=(result == 1))


@logos.theorem(about=step)
def step_away_from_zero(x, *, result):
    return logos.contract(requires=(x != 0), ensures=(result == x + 1))
```

A single `requires=(parameter == integer)` is also substituted into the arithmetic check, so a claim at the guard boundary can use the other path's formula:

```python
@logos.theorem(about=step)
def step_at_boundary(x, *, result):
    return logos.contract(requires=(x == 0), ensures=(result == x + 1))
```

The same rule handles a strict order guard. The guard selects the then path and its negation selects the else path, so the equality boundary `x == y` belongs to the else path:

```python
def minimum(x: int, y: int) -> int:
    if x < y:
        return x
    else:
        return y


@logos.theorem(about=minimum)
def minimum_then(x, y, *, result):
    return logos.contract(requires=(x < y), ensures=(result == x))


@logos.theorem(about=minimum)
def minimum_else(x, y, *, result):
    return logos.contract(requires=~(x < y), ensures=(result == y))
```

The portable core owns four strict-order laws: `lt_irrefl`, `lt_trans`, `lt_add` (transport through adding the same integer) and `lt_neq` (strict order implies disequality). A proof may cite them with `t.order(...)`; the Rust checker recomputes the instance, so no custom axiom is involved:

```python
@logos.theorem
def lt_add_transport(x: int, y: int, c: int):
    return (x < y) >> ((x + c) < (y + c))


logos.check(lt_add_transport.proof(t.intro("x", "y", "c", "h"), t.order("lt_add")))
```

Run the [branch example](https://github.com/gia-uh/logos/blob/main/examples/branch_contract.py) with `python examples/branch_contract.py`, then strict-check the three artifacts with `logos check --strict`. Run the [order example](https://github.com/gia-uh/logos/blob/main/examples/order_contract.py) the same way to write both minimum paths and the two order consequences. Run the [single-return example](https://github.com/gia-uh/logos/blob/main/examples/function_contract.py) too.

## Prove a loop program: binary search

The same declarative form binds a real Python function with one `while` loop and proves its contract over every input. The example uses half-open bounds `[low, high)` and returns any valid occurrence, or `-1` exactly when the target is absent.

```python
@logos.function
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


@binary_search.requires
def ordered(xs):
    return logos.sorted(xs)


@binary_search.invariant
def bounds(xs, *, low, high):
    return (0 <= low) & (low <= high) & (high <= logos.length(xs))


@binary_search.invariant
def below_cut(xs, target, *, low, answer):
    return (answer == -1) >> logos.forall(
        int, lambda i: (0 <= i) >> ((i < low) >> (logos.nth(xs, i) < target))
    )


@binary_search.invariant
def answer_or_searching(xs, target, *, low, high, answer):
    # ... found | (answer == -1 and both cuts) ...


@binary_search.decreases
def remaining(*, low, high):
    return high - low


@binary_search.ensures
def finds_or_absent(xs, target, *, result):
    n = logos.length(xs)
    return ((result == -1) & logos.absent(xs, target)) | (
        (0 <= result) & (result < n) & (logos.nth(xs, result) == target)
    )


binary_search.check()
```

The checker assumes the named invariants together at the loop head and proves each one after every iteration, so a failure names `loop0.preserve.bounds`, `loop0.preserve.answer_or_searching`, or the variant `loop0.variant_decreases.remaining`. It recomputes every verification condition from the exported program and checks the proof supplied for each one; no loop summary is trusted.

Run the [full example](https://github.com/gia-uh/logos/blob/main/book/examples/binary_search.py) with `python book/examples/demo_binary_search.py`, then `logos check --strict binary_search.logos`. The contract covers the empty sequence, duplicates and an absent target. A mutated midpoint, a weakened bound, a missing sortedness premise, a changed source and a forged or missing obligation are rejected.

The supported fragment is `int` and `list[int]`, straight-line assignments, one `if`/`else` tree, one `while` loop with a final return, direct calls to module-level functions declared with `@logos.function`, and integer and sequence operations. Recursion, calls through values or arbitrary globals, list mutation, early returns inside a loop, nested loops and unchecked declarations used as axioms are outside it. Unsupported syntax is refused at its source line when the decorator is applied. The authoring layer re-reads the module and every callee on each check, inspect and export; the Rust checker verifies the artifact's programs and proofs as given. The older `@logos.theorem(about=...)` form and `logos.program_contract` remain available for the single-return, branch and loop fragments documented below.

## Prove infinitely many primes

The [Infinitely Many Primes](https://logos.uhgia.org/one-more-prime-always.html) chapter proves that every integer `n >= 2` has a prime `p > n`. The statement expands divisibility and primality inline: `d | n` is `exists q, n = d * q`, and `p` is prime when `1 < p` and no `d` with `1 < d < p` divides `p`. The proof takes a least divisor of `n! + 1`, shows it is prime, and derives `p > n` by the consecutive-divisibility lemma. It needs induction and primitive recursion for the factorial, not an axiom about primes.

```bash
logos example primes
logos check --strict primes.logos
logos inspect --markdown --strict primes.logos > primes.md
python primes.py authored-primes.logos
logos check --strict authored-primes.logos
```

The shipped `primes.logos` and the certificate rebuilt from the installed wheel are byte-for-byte identical. Both verify with zero custom axioms.

## The book: from divisibility to Euclid

The canonical English book is [`book/`](https://github.com/gia-uh/logos/blob/main/book/README.md). Chapters 7 to 11 build
number theory in order: parity and witnesses, consecutive divisors, induction
through the factorial, the least prime divisor, and Euclid's theorem composed
from named checked lemmas.

The reusable definitions and lemmas live in
[`logos/domains/number_theory.py`](https://github.com/gia-uh/logos/blob/main/logos/domains/number_theory.py). This is the
consecutive-divisor lemma as the book presents it:

```python
@logos.theorem
def common_divisor(d: Int, a: Int):
    """A divisor of two consecutive integers divides one."""
    return (divides(d, a) & divides(d, a + 1)) >> divides(d, 1)

@common_divisor.proof
def prove_common_divisor(p, d, a):
    """Subtract the two quotient equations; the difference is one."""
    both = p.assume(divides(d, a) & divides(d, a + 1))
    k, left = p.obtain(both.left())   # a = d * k
    j, right = p.obtain(both.right()) # a + 1 = d * j
    quotient = j - k
    one = p.ring(1 == d * quotient, using=[left, right])
    return p.witness(quotient, one)
```

Render a chapter with Scriptorium and the installed wheel and checker:

```bash
cd book
scriptorium render chapters/08-neighbours.md --html
```

The final chapter proves that every integer `n >= 2` has a prime `q > n` and
writes `euclid.logos` as it runs. The Rust checker verifies that certificate
without Python:

```bash
logos check --strict euclid.logos
```

The older Spanish `export=` pages remain in `book/` as regression fixtures for
the `scriptorium tangle` path; they are not part of the book's navigation.

## Read a proof or build on it

| Command | What it gives you |
| --- | --- |
| `logos check FILE` | The verified theorem, core theory, and custom axioms actually used, including through lemmas. |
| `logos check --strict FILE` | Requires zero used custom axioms. A valid conditional proof denied by policy exits 3; invalid evidence exits 1. |
| `logos inspect --markdown FILE` | A deterministic derivation with LaTeX equations, suitable for a reader or an agent preparing an explanation. |
| `logos inspect --json FILE` | Structured statements, hypotheses, rule applications, and dependencies for tracing the reasoning. |
| `logos commands --json` | The installed CLI’s machine-readable command contract and supported formats. |

A local hypothesis discharged by a proof can appear in the theorem’s antecedent even when strict checking reports zero custom axioms. To try a proof that depends on an explicit custom axiom, run `logos example dependencies` and inspect the emitted `dependencies.logos`. To explore more integer identities, run `logos example arithmetic`.

The [portable proof reference](https://github.com/gia-uh/logos/blob/main/docs/portable-proof-format.md) documents the supported logic, exact integer laws, resource limits, and migration status. The [project vision](https://github.com/gia-uh/logos/issues/2) tracks planned domains and agent workflows.

## License

MIT.
