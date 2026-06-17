# logos

> A Lean-style proof kernel for Python — prove properties of your code.

**Package:** `logos-ai` | **Status:** v0.1.0 (proof kernel)

Logos lets you declare properties of Python functions and prove them using a
small trusted kernel, a composable tactic system, and optional LLM oracles.
The kernel is the only trusted code (~200 lines). Everything else — tactics,
automation, LLM provers — is untrusted; the kernel catches any invalid proof.

## Quick Start

```python
import logos
import logos.tactics as t
from logos.expr import Var

x, y = logos.vars("x y", int)

# Prove commutativity of addition
logos.theorem(
    "add_comm",
    logos.forall(int, int, lambda x, y: x + y == y + x),
    [t.intro("x", "y"), t.ring()],
)

# Define a function and prove a property
@logos.define
def double(x: Var) -> "Expr":
    return x + x

logos.theorem(
    "double_is_2x",
    logos.forall(int, lambda x: double(x) == logos.lit(2) * x),
    [t.intro("x"), t.unfold("double"), t.ring()],
)
```

## Design

See [`docs/design.md`](docs/design.md) for the full specification.

## License

MIT
