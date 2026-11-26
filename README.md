# Logos

Logos lets people and AI agents prove claims about symbolic models in Python and send the proof to someone else to check. A domain can discover a solution, or an author can guide the search with tactics written in Python. The result is a portable `.logos` file. A recipient needs only the Rust executable to verify it offline, inspect its assumptions, or read the derivation as mathematics.

## Install from source

Install a Rust toolchain with Cargo and Python 3.12 or newer. From a shell on Linux or macOS:

```bash
git clone https://github.com/gia-uh/logos.git
cd logos
cargo install --locked --path checker
export PATH="${CARGO_HOME:-$HOME/.cargo}/bin:$PATH"
python3 -m venv .venv
source .venv/bin/activate
python -m pip install .
logos --version
```

The Python package is `logos-ai`, imported as `logos`. Python authors proofs. The `logos` executable checks them.

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

The same command also writes `guide_knights_knaves.py`, which shows how to supply one strategic choice: split on A’s role. Run it without arguments to preview A’s utterance and the proposed claim in English. Give it an output filename to build the guided proof. [Domain guide](docs/portable-proof-format.md#knights-and-knaves-example)

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

## Prove a contract about an ordinary function

`@logos.theorem(about=fn)` binds the theorem to `fn`'s own source. The decorated body returns `logos.contract`, whose `ensures` is a postcondition over the parameters and the keyword-only `result`. Logos reads the function's module, recompiles it, and refuses to continue if the imported code object disagrees with the source. Every check, certification and export repeats that binding and compares the fresh translation with the one the statement was built from, so replacing `__code__` or editing the source after decoration cannot certify stale mathematics.

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

The checked statement is `∀ mid:int, ∀ result:int, result = advance(mid) → result - mid = 1`, and `advance` is declared to the checker as the transparent function extracted from the source body. Run the [runnable example](examples/function_contract.py) with `python examples/function_contract.py`, then `logos check --strict advance.logos`.

An optional `requires=` becomes an explicit antecedent, so a conditional contract is never silently dropped:

```python
@logos.theorem(about=advance)
def advance_at_zero(mid, *, result):
    return logos.contract(requires=(mid == 0), ensures=(result - mid == 1))
```

The supported fragment is deliberately small. The function must be an undecorated module-level function whose body is a single `return` of parameters, integer literals and `+`, with every parameter and the return annotated with the built-in `int`. The decorated theorem takes the same input names in the same order plus exactly one keyword-only result. Its `ensures` must be one equality between integer terms over the parameters and the result, with the result on exactly one side; `requires`, when present, is a proposition over the parameters built from integer equalities and `&`, `|`, `~`, `>>`. Branches, loops, calls, globals, closures, wrappers, missing or ambiguous source, postponed annotations and a stale source/code match all raise `logos.LogosContractError` with the file and line. Verification never executes the function with symbolic arguments. Interpreting Python's source and compiling the supported fragment is the trust boundary; the proof about the extracted integer function is checked by Rust.

<details>
<summary>Choose a witness for an existential claim</summary>

To prove that every integer has a successor, use the current arbitrary
integer from the proof goal when choosing the witness.

```python
import logos
import logos.tactics as t


@logos.theorem
def integer_successor(x: int):
    return logos.exists(int, lambda y: y == x + 1)


def choose_successor(goal):
    return t.witness(goal.context["x"] + 1)(goal)


logos.check(integer_successor.proof(t.intro("x"), choose_successor, t.refl()))
logos.export_proof(integer_successor, "successor.logos")
```

The witness `x + 1` leaves the equality `x + 1 == x + 1` to prove.
Rust checks that the witness has the binder's sort and that the evidence
establishes the instantiated predicate in the surrounding scope.

```bash
logos check --strict successor.logos
logos inspect --markdown --strict successor.logos
logos inspect --json --strict successor.logos
```

</details>

## Read a proof or build on it

| Command | What it gives you |
| --- | --- |
| `logos check FILE` | The verified theorem, core theory, and custom axioms actually used, including through lemmas. |
| `logos check --strict FILE` | Requires zero used custom axioms. A valid conditional proof denied by policy exits 3; invalid evidence exits 1. |
| `logos inspect --markdown FILE` | A deterministic derivation with LaTeX equations, suitable for a reader or an agent preparing an explanation. |
| `logos inspect --json FILE` | Structured statements, hypotheses, rule applications, and dependencies for tracing the reasoning. |
| `logos commands --json` | The installed CLI’s machine-readable command contract and supported formats. |

A local hypothesis discharged by a proof can appear in the theorem’s antecedent even when strict checking reports zero custom axioms. To try a proof that depends on an explicit custom axiom, run `logos example dependencies` and inspect the emitted `dependencies.logos`. To explore more integer identities, run `logos example arithmetic`.

The [portable proof reference](docs/portable-proof-format.md) documents the supported logic, exact integer laws, resource limits, and migration status. The [project vision](https://github.com/gia-uh/logos/issues/2) tracks planned domains and agent workflows.

## License

MIT.
