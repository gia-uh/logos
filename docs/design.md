# Logos — Design Specification

**Package:** `logos-ai`
**Tagline:** A Lean-style proof kernel for Python — prove properties of your code.

---

## Vision

Logos is a Python library that lets you prove properties of your code using a small trusted kernel, an expressive proposition language, and a composable tactic system. It follows Lean's architecture: a minimal kernel validates proof terms; all automation (tactics, LLM oracles) is untrusted and produces terms the kernel checks.

---

## Architecture

```
┌─────────────────────────────────────────┐
│  User Layer                             │
│  @logos.define · @logos.theorem         │
│  logos.forall/exists · operator sugar   │
├─────────────────────────────────────────┤
│  Tactic Layer (untrusted)               │
│  ring · linarith · intro · cases · ...  │
│  LLM tactic · custom Python tactics     │
├─────────────────────────────────────────┤
│  Proof Term Layer                       │
│  Refl · Symm · Trans · Subst            │
│  ForallIntro/Elim · ImpliesIntro/Elim   │
│  AndIntro/Elim · OrIntro/Elim · Axiom   │
├─────────────────────────────────────────┤
│  Kernel (trusted, ~200 lines)           │
│  Structurally validates term trees      │
└─────────────────────────────────────────┘
```

The kernel is the only trusted code. Tactics are arbitrary Python — generators, LLM calls, anything — that produce term trees the kernel validates. If the kernel rejects a term, the proof fails, regardless of how it was produced.

---

## Proposition Language

Propositions are Python expression trees built via operator overloading. Variables are `Var[T]` objects; operators produce `Expr[T]` nodes.

### Operator Map

```python
x, y, z = logos.vars("x y z", int)

# Arithmetic → Expr[int]
x + y      # Add(x, y)
x + 1      # Add(x, Lit(1))      ← RHS literals auto-lifted
x - y      # Sub(x, y)
x * y      # Mul(x, y)
x // y     # Div(x, y)
x % 2      # Mod(x, Lit(2))
-x         # Neg(x)
x ** 2     # Pow(x, Lit(2))

# Comparisons → Expr[bool]
x == y     # Eq(x, y)
x != y     # Neq(x, y)
x < y      # Lt(x, y)
x <= y     # Le(x, y)
x > y      # Gt(x, y)
x >= 0     # Ge(x, Lit(0))

# Logical connectives → Expr[bool]
# (and/or/not are Python keywords — use &/|/~/>>)
(x > 0) & (y > 0)       # And(...)
(x > 0) | (x < 0)       # Or(...)
~(x == y)                # Not(...)
(x > 0) >> (x + y > y)  # Implies(...)
```

Auto-lifting: any Python literal appearing as a RHS operand is wrapped in `Lit(...)` automatically.

Guard: `Expr.__bool__` raises `TypeError` — prevents accidental use of an expression in a Python `if` or `assert`.

### Quantifiers

```python
# With pre-declared vars:
Forall(x, y, x + y == y + x)
Exists(x, x > 0)

# With lambda (vars created implicitly):
logos.forall(int, int, lambda x, y: x + y == y + x)
logos.exists(int, lambda x: x > 0)
```

---

## `@logos.define`

Declares a function in the logos expression system. The body runs in expression-tree mode (parameters are `Var[T]`), producing an `Expr[T]`. Logos auto-generates a definition axiom.

```python
@logos.define
def double(x: Var[int]) -> Expr[int]:
    return x + x

# Auto-generates: Forall(x, Eq(double(x), x + x))
```

**Dual mode:** when called with a concrete Python value, runs normally. When called with a `Var` or `Expr`, returns an application node.

```python
double(5)                          # → 10  (Python evaluation)
double(logos.var("x", int))        # → App("double", [Var("x")])
```

### Case Analysis

```python
@logos.define
def abs_val(x: Var[int]) -> Expr[int]:
    return logos.cases(
        (x >= 0,  x),
        (x < 0,  -x),
    )
```

`logos.cases` is the expression-mode equivalent of `if/elif/else`. Logos checks that conditions are exhaustive.

### Recursive Definitions

```python
@logos.define(measure=lambda n: n)   # termination witness
def factorial(n: Var[int]) -> Expr[int]:
    return logos.cases(
        (n == 0,  1),
        (n > 0,   n * factorial(n - 1)),
    )

# Generates:  factorial(0) == 1
#             Forall(n, n > 0, factorial(n) == n * factorial(n - 1))
```

### Extern (Black-Box) Functions

```python
sorted_fn = logos.extern("sorted", [List[int]], List[int])

xs = logos.var("xs", List[int])
logos.axiom("sorted_length",
    logos.forall(List[int], lambda xs:
        sorted_fn(xs).length() == xs.length()
    )
)
```

---

## `logos.theorem`

Declares and proves a named theorem. Checked at import time; `ImportError` if the proof fails.

```python
x, y = logos.vars("x y", int)

logos.theorem(
    "add_comm",
    statement = logos.forall(int, int, lambda x, y: x + y == y + x),
    proof = [tactics.ring()],
)
```

Proved theorems become reusable in other proofs via `tactics.apply("add_comm")`.

---

## Proof Terms (Kernel Language)

The kernel accepts exactly these constructors:

| Term | Proves |
|------|--------|
| `Refl(e)` | `e == e` |
| `Symm(p)` | `b == a` (given `p: a == b`) |
| `Trans(p, q)` | `a == c` (given `p: a==b`, `q: b==c`) |
| `Subst(p, f)` | `f(a) == f(b)` (given `p: a==b`) |
| `Axiom(name)` | the named axiom's statement |
| `ForallIntro(var, body)` | `Forall(var, P)` |
| `ForallElim(p, val)` | `P[var := val]` (given `p: Forall(var, P)`) |
| `ImpliesIntro(hyp_name, body)` | `P >> Q` |
| `ImpliesElim(p, q)` | `Q` (modus ponens; given `p: P>>Q`, `q: P`) |
| `AndIntro(p, q)` | `A & B` |
| `AndElimL(p)` / `AndElimR(p)` | `A` / `B` (given `p: A&B`) |
| `OrIntroL(p)` / `OrIntroR(p)` | `A\|B` |
| `OrElim(p, f, g)` | `C` (case analysis on `p: A\|B`) |
| `NotIntro(f)` / `NotElim(p, q)` | `~A` / anything (contradiction) |

---

## Tactics

### The Protocol

A tactic is a callable:

```python
TacticFn = Callable[[Goal], ProofTerm | Generator[Goal, ProofTerm, ProofTerm]]
```

- **Atomic**: returns a `ProofTerm` directly.
- **Generator**: `yield` subgoals, receive back their proofs via `.send()`, compose, `return` the final term.

```python
@dataclass
class Goal:
    context: dict[str, Expr]   # hypotheses: name → proposition/type
    statement: Expr[bool]      # what to prove
```

`TacticFailed` (a plain exception) signals failure; the runner or `tactics.first()` catches it.

### Bundled Tactics

**Structural**

```python
tactics.intro(*names)        # strip Forall/Implies, add to context
tactics.assumption()         # close if goal is in context
tactics.exact(term)          # close with an explicit proof term
tactics.apply(thm)           # unify with theorem, produce premise subgoals
tactics.cases(*conditions)   # case split → one subgoal per case
tactics.split()              # A & B → [A, B]
tactics.left()               # A | B → prove A
tactics.right()              # A | B → prove B
tactics.witness(val)         # Exists(x, P) → P[x:=val]
tactics.contradiction()      # close via P + ~P in context
```

**Definitional / Rewriting**

```python
tactics.unfold(*fns)         # replace fn(args) with definition body
tactics.refl()               # prove a == a
tactics.rewrite(lemma)       # rewrite left-to-right via equation lemma
tactics.rewrite_rev(lemma)   # rewrite right-to-left
tactics.simp(*lemmas)        # exhaustive rewriting to fixed-point
tactics.eval()               # evaluate concrete subexpressions
tactics.norm_num()           # normalize and close numeric ground goals
```

**Arithmetic**

```python
tactics.ring()               # polynomial ring identities (x+y==y+x, distributivity...)
tactics.linarith()           # linear arithmetic from linear hypotheses (Farkas)
tactics.omega()              # Presburger arithmetic (integers + divisibility)
tactics.decide()             # evaluate a ground decidable proposition
```

**Induction**

```python
tactics.induction(var)            # nat induction: base P(0) + step P(n)→P(n+1)
tactics.strong_induction(var)     # strong nat induction
tactics.induction_list(var)       # structural list induction
```

**Combinators**

```python
tactics.then(*ts)            # sequence
tactics.first(*ts)           # try each, succeed on first non-failure
tactics.try_(t)              # apply t; succeed regardless
tactics.repeat(t)            # apply until failure
tactics.all_goals(t)         # apply t to every open subgoal
tactics.focus(n, t)          # apply t to the nth open subgoal
```

### Writing a Custom Tactic

```python
# Atomic tactic
def my_tactic(goal: Goal) -> ProofTerm:
    match goal.statement:
        case Eq(lhs, rhs) if lhs == rhs:
            return kernel.Refl(lhs)
        case _:
            raise TacticFailed(f"my_tactic: cannot handle {goal.statement}")

# Generator tactic (splits goal into subgoals)
def my_split(goal: Goal) -> Generator[Goal, ProofTerm, ProofTerm]:
    match goal.statement:
        case And(left, right):
            left_proof  = yield Goal(goal.context, left)
            right_proof = yield Goal(goal.context, right)
            return kernel.AndIntro(left_proof, right_proof)
        case _:
            raise TacticFailed("my_split: not A & B")
```

### LLM Tactic

```python
from logos.ai import llm_tactic

logos.theorem(
    "hard_theorem",
    statement = ...,
    proof = [llm_tactic(model="claude-opus-4-7")],
)
```

The LLM receives a serialized `Goal`, returns a proof term as text, `logos.kernel.parse_term()` parses it, and the kernel validates. Hallucinated invalid proofs are caught by the kernel. The tactic retries up to `max_retries` times with error feedback.

---

## `ring` Implementation Sketch

Normalize both sides to a canonical sum-of-monomials form (a `dict` from `frozenset[tuple[str, int]]` to coefficient). If they match, build the proof chain via `Trans`/`Subst` rewrites using logos' built-in ring axioms (commutativity, associativity, distributivity — declared once in `logos.builtins`).

```python
def normalize(expr: Expr) -> dict[frozenset, int]:
    match expr:
        case Lit(n):     return {frozenset(): n}
        case Var(name):  return {frozenset({(name, 1)}): 1}
        case Add(a, b):  return add_polys(normalize(a), normalize(b))
        case Mul(a, b):  return mul_polys(normalize(a), normalize(b))
        case Neg(a):     return scale_poly(normalize(a), -1)
        case Pow(a, Lit(n)): return pow_poly(normalize(a), n)
        case _: raise TacticFailed(f"ring: cannot normalize {expr}")
```

## `linarith` Implementation Sketch

Collect linear inequalities from the context. Use Gaussian elimination (Farkas lemma) to find a non-negative linear combination that implies the goal. Emit the combination as a proof term. ~80 lines, no external dependencies.

---

## Module Layout (proposed)

```
logos/
  __init__.py        # public API: define, theorem, forall, exists, vars, var, axiom, extern
  kernel.py          # trusted: ~200 lines, all ProofTerm constructors + check()
  expr.py            # Expr, Var, Lit, Add, Mul, Eq, Forall, ... + operator overloads
  goal.py            # Goal dataclass + context helpers
  runner.py          # TacticRunner: drives generator protocol
  tactics/
    __init__.py      # exports all bundled tactics
    structural.py    # intro, assumption, exact, apply, cases, split, ...
    rewrite.py       # unfold, refl, rewrite, simp, eval, norm_num
    arithmetic.py    # ring, linarith, omega, decide
    induction.py     # induction, strong_induction, induction_list
    combinators.py   # then, first, try_, repeat, all_goals, focus
  ai.py              # llm_tactic (optional dependency, importable separately)
  builtins.py        # logos' built-in ring/arithmetic axioms
```

---

## Open Design Questions

1. **`omega` scope:** implement ourselves (Omega algorithm, ~300 lines) or wrap `sympy.ntheory`?
2. **`simp` termination:** rewriting can loop; need a term-size bound or convergence check.
3. **Collection types:** `List[int]` expressions need `head`, `tail`, `length`, `nth` nodes. Design separately.
4. **Proof serialization:** should `ProofTerm` trees be serializable to JSON/msgpack for caching and sharing?
5. **mypy plugin:** long-term, a plugin that understands `Refined[T, P]` annotations; out of scope for v0.1.
