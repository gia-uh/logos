---
theme: book
title: Quick Start
stem: quick-start
---

# Quick Start

## Before you start

**Prerequisites.** Python 3.12 or newer, a Rust toolchain with Cargo, and a terminal on Linux or macOS.

**Outcomes.** You will install the Python package and the checker, put the checker on `PATH`, check one theorem end to end, and read the receipt that records the check.

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

The `PATH` line is not decoration. `theorem.check()` runs the command `logos check --json -` and sends the artifact on standard input. If the executable is not on `PATH`, the Python call fails with:

```text
installed Rust logos checker not found on PATH
```

If you install the checker somewhere else with `cargo install --root <directory>`, add `<directory>/bin` to `PATH` instead. The rule is always the same: the directory that contains the `logos` executable must be on the `PATH` of the Python process that runs the proof.

Confirm both halves before writing a proof:

```bash
python -P -c "import logos; print(logos.__file__)"
logos --version
```

The `-P` flag stops Python from putting the current directory first, so the command imports the installed wheel rather than the `logos/` directory of the checkout. It must print a path inside the virtual environment, not a path inside the repository. The second must print a version. If either fails, fix the installation before continuing; a proof error later would only hide the real problem.

## Check your first theorem

The statement is transitivity of implication: if $P$ implies $Q$, and $Q$ implies $R$, then $P$ implies $R$. The proof assumes the two implications and $P$, derives $Q$, and applies the second implication to reach $R$.

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

`compose.check()` does three things. It runs the proof function to build evidence. It packages the statement, the evidence and the authored commentary into an artifact. It sends that artifact to the Rust checker. If the checker accepts, the theorem stores the receipt printed above.

`compose.certified` is `True` only while the receipt matches the current statement and evidence. The digest is the SHA-256 of the artifact bytes. Two people who hold the same artifact see the same digest; the checker verifies those bytes, not a Python object.

Chapter 1 explains each line of this proof and reads the checker's own account of the derivation.
