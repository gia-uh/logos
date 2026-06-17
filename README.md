# logos

> A Lean-style proof kernel for Python — prove properties of your code.

**Package:** `logos-ai` | **Status:** design phase

Logos lets you declare properties of Python functions and prove them using a
small trusted kernel, a composable tactic system, and optional LLM oracles.
The kernel is the only trusted code (~200 lines). Everything else — tactics,
automation, LLM provers — is untrusted; the kernel catches any invalid proof.

## Design

See [`docs/design.md`](docs/design.md) for the full specification.

## License

MIT
