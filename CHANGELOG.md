# Changelog

## [0.1.0] - 2026-06-17

### Features
- Trusted proof kernel with 14 inference rules
- Expression language with full operator overloading (`+`, `-`, `*`, `//`, `%`, `**`, `==`, `!=`, `<`, `<=`, `>`, `>=`, `&`, `|`, `~`, `>>`)
- `@logos.define` — symbolic function definitions with auto-generated axioms
- `logos.theorem` / `logos.prove` — proof validation at definition time
- `logos.extern` — axiom declarations for external functions
- Bundled tactics: `ring`, `linarith`, `decide`, `intro`, `assumption`, `exact`, `apply`, `split`, `left`, `right`, `witness`, `unfold`, `refl`, `rewrite`, `eval_`, `norm_num`
- Tactic combinators: `then`, `first`, `try_`, `repeat`
- Built-in ring axioms for integer arithmetic
