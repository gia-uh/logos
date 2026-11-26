# logos

> A Lean-style proof kernel for Python — prove properties of your code.

**Package:** `logos-ai` | **Status:** v0.1.0

Logos brings formal proof to Python. Write propositions and compose tactics
that produce proof terms. The standalone Rust checker independently verifies
proofs exported as data.

## First portable proof

From this integration branch, install both tools with a Rust toolchain and
Python 3.12 or newer:

```bash
cargo install --locked --path checker
python -m pip install .
```

From an empty directory, with the Rust `logos` on PATH:

```bash
logos --help
logos example
logos inspect authorization.logos
python authorization.py authored.logos
logos check --strict authored.logos
```

To derive `Q` from the custom axiom `A` (`P ∧ Q`) through a checked lemma `L`:

```bash
logos example dependencies
python dependencies.py authored-dependencies.logos
logos inspect authored-dependencies.logos
```

The emitted `dependencies.logos` can also be replayed with the checker alone.
Default verification accepts conditional proofs. `logos check --strict dependencies.logos` exits 3 and prints the assumption and its proof path.

To solve a Knights and Knaves puzzle, describe the inhabitants and what they say:

```python
from logos.domains.logic_puzzles import KnightsKnaves

puzzle = KnightsKnaves()
a, b = puzzle.entity("A"), puzzle.entity("B")
a.says(a.is_knave() & b.is_knave())
print(puzzle.solve())  # {'A': 'knave', 'B': 'knight'}
puzzle.export_proof("puzzle.logos")
```

Run `logos example knights-knaves` to get a runnable script, then
`python solve_knights_knaves.py puzzle.logos` and `logos check --strict puzzle.logos`.
See [solver statuses and statement syntax](docs/portable-proof-format.md#knights-and-knaves-example).

For integer polynomial proofs and structured inspection:

```bash
logos example arithmetic
logos check --strict arithmetic.logos
python arithmetic.py proofs
logos check --strict proofs/binomial_square.logos
logos inspect --json --strict proofs/binomial_square.logos
logos inspect --markdown --strict proofs/binomial_square.logos > proof.md
```

Default inspection prints the checked steps for a reader. JSON inspection
includes typed conclusions, scopes, rule premises, and law substitutions.
Markdown inspection writes a numbered proof with LaTeX math.
See the [portable proof format and migration status](docs/portable-proof-format.md)
for the supported fragment. The broader authoring API below also documents
features still being migrated.

---

## Core Idea

```python
import logos
import logos.tactics as t

@logos.theorem
def add_comm(x: int, y: int):
    return x + y == y + x

logos.check(add_comm.proof(t.intro("x", "y"), t.ring()))
logos.export_proof(add_comm, "add_comm.logos")
```

`LogosProofError` reports rejected evidence. A successful portable theorem
has an immutable verification receipt. Use `logos.tactics.apply(lemma)` to
reference a theorem with a proof attached.

---

## Defining Functions Symbolically

`@logos.define` runs your function body in *expression-tree mode* — the
parameters become symbolic variables, and operators build a tree rather than
evaluating. The checker unfolds the typed definition during conversion.

```python
import logos
import logos.tactics as t

@logos.define
def double(x: int) -> int:
    return x + x

# Calling with a real value evaluates normally
double(5)   # → 10

# Calling with a Var builds an expression tree
x = logos.var("x", int)
double(x)   # → App("double", [Var("x")])

# Prove a property: unfold the definition, then use ring arithmetic
@logos.theorem
def double_is_2x(x: int):
    return double(x) == 2 * x

logos.check(double_is_2x.proof(t.intro("x"), t.unfold(double), t.ring()))
```

---

## Operator Overloading

Expressions are built using Python operators — no wrapper functions needed.
All arithmetic and comparison operators return `Expr` nodes, not Python values.

```python
x, y, z = logos.vars("x y z", int)

# Arithmetic
x + y       # Add(x, y)
x * 2       # Mul(x, Lit(2))   ← literals auto-lifted
-x          # Neg(x)
x ** 2      # Pow(x, Lit(2))

# Comparisons → Expr[bool]
x == y      # Eq(x, y)         ← NOT Python bool
x > 0       # Gt(x, Lit(0))

# Logical connectives (and/or/not can't be overloaded)
(x > 0) & (y > 0)     # And(...)
(x > 0) | (x < 0)     # Or(...)
~(x == y)              # Not(...)
(x > 0) >> (y > 0)    # Implies(...)
```

Accidentally using an expression in a Python `if` or `assert` raises
`TypeError` with a clear message.

---

## Quantifiers

```python
# Lambda form — variables are created implicitly
logos.forall(int, int, lambda x, y: x + y == y + x)
logos.exists(int, lambda x: x > logos.lit(0))

# Explicit form — declare vars first
x, y = logos.vars("x y", int)
Forall(x, y, x + y == y + x)
```

---

## Tactics

Tactics are Python functions that transform proof goals into proof terms.
They're *untrusted* — the kernel checks their output.

### Structural

```python
t.intro("x", "y", "h")   # strip Forall/Implies, add to context
t.assumption()             # close if goal is in context
t.exact(term)              # close with an explicit proof term
t.split()                  # A & B  →  [A, B]
t.left(right_type)         # A | B  →  prove A
t.right(left_type)         # A | B  →  prove B
t.witness(val)             # Exists(x, P)  →  P[x:=val]
t.contradiction()          # close via P and ~P in context
```

### Definitional / Rewriting

```python
t.unfold("double")        # replace double(x) with its body x + x
t.refl()                  # prove a == a
t.rewrite("add_comm")     # rewrite left-to-right using an equation axiom
t.rewrite_rev("add_comm") # rewrite right-to-left
t.eval_()                 # evaluate ground arithmetic sub-expressions
t.norm_num()              # normalize and close numeric ground goals
```

### Arithmetic

```python
t.ring()       # polynomial ring identities: x+y==y+x, (x+y)²==x²+2xy+y²
t.linarith()   # linear arithmetic from linear hypotheses (Farkas)
t.decide()     # evaluate a ground boolean proposition
```

### Combinators

```python
t.then(t.intro("x"), t.ring())   # sequence as a single tactic
t.first(t.refl(), t.ring())      # try each until one succeeds
t.try_(t.ring())                  # apply if possible, silent on failure
t.repeat(t.intro_one())           # apply until failure
t.all_goals(t.assumption())       # apply to every open subgoal
```

---

## Multi-Step Proofs

When a tactic produces multiple subgoals (e.g. `split`), wrap each
subgoal's tactics in a nested list:

```python
x, y = logos.vars("x y", int)

logos.theorem(
    "both_positive",
    logos.forall(int, int, lambda x, y:
        (x > logos.lit(0)) >> (
        (y > logos.lit(0)) >> (
        (x > logos.lit(0)) & (y > logos.lit(0))
    ))),
    proof=[
        t.intro("x", "y", "hx", "hy"),
        t.split(),
        [t.assumption()],    # subgoal 1: x > 0
        [t.assumption()],    # subgoal 2: y > 0
    ],
)
```

---

## Extern Functions

Declare external (uninspectable) functions and axiomatize their properties:

```python
sorted_fn = logos.extern("sorted_list", [list], list)

xs = logos.var("xs", list)

logos.axiom(
    "sorted_preserves_length",
    logos.forall(list, lambda xs: sorted_fn(xs) == sorted_fn(xs)),  # placeholder
)
```

---

## Composing Theorems

Proved theorems are registered as axioms and can be applied inside later proofs:

```python
logos.theorem(
    "add_comm",
    logos.forall(int, int, lambda x, y: x + y == y + x),
    proof=[t.intro("x", "y"), t.ring()],
)

# Use it in another proof via t.apply("add_comm") or t.rewrite("add_comm")
logos.theorem(
    "add_comm_instance",
    logos.forall(int, int, lambda a, b: a + b == b + a),
    proof=[t.intro("a", "b"), t.rewrite("add_comm"), t.refl()],
)
```

---

## The Kernel

The kernel is the only trusted code. It knows 14 inference rules:

| Rule | Proves |
|------|--------|
| `Refl(e)` | `e == e` |
| `Symm(p)` | `b == a` |
| `Trans(p, q)` | `a == c` |
| `Subst(p, f)` | `f(a) == f(b)` |
| `Axiom(name)` | named axiom |
| `HypRef(name)` | named hypothesis |
| `ForallIntro/Elim` | ∀ introduction/elimination |
| `ImpliesIntro/Elim` | → introduction/modus ponens |
| `AndIntro/ElimL/ElimR` | ∧ introduction/elimination |
| `OrIntroL/IntroR` | ∨ introduction |
| `CaseAnalysis` | proof by cases |
| `ExFalso` | ex falso quodlibet |

Every tactic compiles down to these terms. You can write term-mode proofs directly:

```python
from logos.kernel import Refl, ForallIntro, Trans, Axiom
from logos.expr import Var

x = Var("x", int)
term = ForallIntro(x, Refl(x))
# This proves Forall(x, x == x)
```

---

## Writing Custom Tactics

A tactic is a callable `Goal → ProofTerm | (list[Goal], compose_fn)`.

```python
from logos.goal import Goal
from logos.kernel import Refl
from logos.helpers import structural_eq
from logos.runner import TacticFailed

def my_refl(goal: Goal):
    match goal.statement:
        case Eq(lhs, rhs) if structural_eq(lhs, rhs):
            return Refl(lhs)
        case _:
            raise TacticFailed("my_refl: goal is not a == a")

# Splitting tactic: returns (subgoals, compose_fn)
def my_split(goal: Goal):
    match goal.statement:
        case And(left, right):
            return (
                [Goal(goal.context, left), Goal(goal.context, right)],
                lambda proofs: AndIntro(proofs[0], proofs[1]),
            )
        case _:
            raise TacticFailed("my_split: expected A & B")
```

---

## Architecture

```
User layer          @logos.define · logos.theorem · logos.forall
                              ↓
Tactic layer        ring · linarith · intro · cases · ...  (untrusted)
  (untrusted)                ↓
Proof terms         Refl · Trans · Subst · ForallIntro · ...
                              ↓
Kernel (~200 ln)    infer() / check() — the only trusted code
```

---

## Design

See [`docs/design.md`](docs/design.md) for the full specification, and
[`docs/superpowers/plans/2026-06-17-logos-v0.1.md`](docs/superpowers/plans/2026-06-17-logos-v0.1.md)
for the implementation plan.

## License

MIT
