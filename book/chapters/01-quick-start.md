---
theme: book
title: Quick Start
stem: quick-start
---

# Quick Start

## Before you start

**Prerequisites.** Python 3.12 or newer, a Rust toolchain with Cargo, and a terminal on Linux or macOS.

**Outcomes.** You will install the Python package and the checker, put the checker on `PATH`, check one theorem end to end, and explain what the successful check certifies.

## Install the two programs

Logos has two parts, and both must be installed. The Python package is `logos-ai`, imported as `logos`. The checker is the `logos` executable built from `checker/`.

From a clone of the repository:

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

`cargo install` compiles the checker and puts it in `${CARGO_HOME:-$HOME/.cargo}/bin`. `python -m pip install .` installs the package into the virtual environment.

`theorem.check()` runs the command `logos check --json -` and sends the artifact on standard input. If the executable is not on `PATH`, the Python call fails with:

```text
installed Rust logos checker not found on PATH
```

If you install the checker somewhere else with `cargo install --root <directory>`, add `<directory>/bin` to `PATH` instead. The rule is always the same: the directory that contains the `logos` executable must be on the `PATH` of the Python process that runs the proof.

Confirm both halves before writing a proof:

```bash
python -P -c "import logos; print(logos.__file__)"
logos --version
```

The `-P` flag stops Python from putting the current directory first, so the command imports the installed wheel rather than the `logos/` directory of the checkout. The first command should print an installed path under `.venv`. The second should print the checker version.

## Check your first theorem

The claim on paper is $(P \Rightarrow Q) \Rightarrow ((Q \Rightarrow R) \Rightarrow (P \Rightarrow R))$. The first two arrows let you assume the two given implications. To establish the remaining $P \Rightarrow R$, assume $P$ and aim for $R$.

In Python, `>>` builds an implication between symbolic propositions, and the parentheses keep each premise and conclusion together. The paper claim becomes `(P >> Q) >> ((Q >> R) >> (P >> R))`. The `@logos.theorem` decorator records the returned expression as the claim for arbitrary propositions. The `@compose.proof` decorator attaches the derivation.

What can you get from $P \Rightarrow Q$ and $P$? You can get $Q$, which is exactly the premise of $Q \Rightarrow R$. Use `p.assume` to introduce the local premises in order, and `p.apply` to get each conclusion from an implication and evidence for its premise.

Save the Python block as `first_proof.py`. With the virtual environment active, run `python -P first_proof.py`. The `-P` flag imports the installed package even when the script is in the checkout.

```python {run}
import logos
from logos import Prop

@logos.theorem
def compose(P: Prop, Q: Prop, R: Prop):
    """If P implies Q and Q implies R, then P implies R."""
    return (P >> Q) >> ((Q >> R) >> (P >> R))

@compose.proof
def prove_compose(p, P, Q, R):
    """Reach R through Q, the proposition both implications mention."""
    p_to_q = p.assume(P >> Q)
    q_to_r = p.assume(Q >> R)
    given_p = p.assume(P)
    have_q = p.apply(p_to_q, given_p)
    return p.apply(q_to_r, have_q)

compose.check()
print("checked:", compose.certified)
print("artifact:", compose.receipt.artifact_sha256[:16])
```

Look for `checked: True`. That means the theorem's current statement and evidence have a matching receipt from the Rust checker. The checker accepted that the two implications suffice to derive $P \Rightarrow R$ for arbitrary propositions. The displayed digest is a short fingerprint of the checked artifact. Its exact value is incidental to this exercise.

## Exit exercise

1. Predict what happens if the last application gets `given_p` in place of `have_q`. Run that edit, identify what was expected and what was supplied, and restore the original.
2. In a new file, write and check $P \Rightarrow P$. Keep the same pattern for a theorem and its proof. Which assumption can supply the conclusion? Run your file and explain what `checked: True` certifies.

## Read the book offline

A release wheel with the bundled book can open it with `python -m logos book --open`. Use `python -m logos book --help` to look up the other options.

## Answers

The changed application expects $Q$, the premise of $Q \Rightarrow R$, and gets $P$. The diagnostic includes `expected: Q` and `got: P`.

For the new claim, introducing the premise $P$ gives the evidence needed for the conclusion $P$. The check certifies the whole implication for an arbitrary proposition.

```python {run}
import logos
from logos import Prop

@logos.theorem
def identity(P: Prop):
    return P >> P

@identity.proof
def prove_identity(p, P):
    return p.assume(P)

identity.check()
assert identity.certified
print("identity checked:", identity.certified)
```

Continue to [Writing Your First Proof](writing-your-first-proof.html) to see how a derivation records each inference and accounts for its local assumptions.
