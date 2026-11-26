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

A custom tactic can inspect the current goal and return evidence, or split it into subgoals and combine their proofs. Rust checks the resulting derivation independently of the tactic. For software verification, the theorem is about the encoded model; relating a deployed program to that model is a separate obligation.

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
