# Changelog

## [0.1.0] - 2026-11-27

First public release. The Python distribution is `logos-ai`, imported as
`logos`; the standalone checker is the `logos` executable built from
`checker/`.

### Proof kernel and portable format

- Trusted proof kernel with 14 inference rules, checked by an independent Rust
  verifier that recomputes every conclusion and never runs Python.
- Portable `logos-proof-v1` certificates, read offline with `logos check`,
  `logos check --strict`, `logos inspect` and `logos inspect --json`.
- `logos commands --json` publishes the bundle grammar and all 42
  checker-owned laws, with drift tests against the Rust table and the Python
  schema.
- Strict integer order in the portable core (`lt`) with the checker-owned laws
  `lt_irrefl`, `lt_trans`, `lt_add` and `lt_neq`, and the `t.order()` tactic.
- Checker-owned order, half-interval and sortedness laws with explicit
  soundness arguments.
- Integer order and positivity laws: `mul_pos`, `mul_eq_one`, `mul_nonneg`,
  `div_nonneg`, `div_lt`, `lt_succ_fwd`, `lt_succ_rev`,
  `eq_of_not_lt_not_lt` and `lt_decidable`.
- Checked rational linear-arithmetic certificates (`linear`) and checked local
  facts (`have`).
- Scoped existential elimination (`exists_elim`) and equality substitution
  (`eq_subst`) in the portable core.
- Integer induction (`induction`) and least element (`least`) over a lower
  bound.
- Primitive-recursive integer definitions (`recursor`, `recursor_base`,
  `recursor_step`) with a predecessor-only recursive-call check.
- Finite integer sequences, `len`, `nth`, `sorted` and non-strict order in the
  portable core.
- Source-bound loop programs with `program_ref`, recomputed loop obligations,
  read bounds and a termination variant.
- Mutation tests for wrong midpoints, wrong invariants, forged program bodies
  and missing obligations.

### Authoring

- `logos.theorem` / `logos.prove` — proof validation at definition time.
- `@logos.define` — symbolic function definitions with auto-generated axioms.
- `logos.extern` — axiom declarations for external functions.
- Book-style proofs: `@logos.definition`, `Prop`, `Int`, and an authoring
  context with `assume`, `obtain`, `ring(using=...)` and `witness`.
- Structured authoring failures with the failing source line, expected goal,
  opened equalities and machine-readable `details`.
- Authoring diagnostics that render inequalities, products, quotients and
  sequence reads with the same notation as the book.
- Bundled tactics: `ring`, `linarith`, `decide`, `intro`, `assumption`,
  `exact`, `apply`, `split`, `left`, `right`, `witness`, `unfold`, `refl`,
  `rewrite`, `eval_`, `norm_num`.
- Tactic combinators: `then`, `first`, `try_`, `repeat`, `all_goals`.

### Domains and programs

- `logos.contract` / `@logos.theorem(about=...)` — prove a contract about an
  ordinary function from its source, including one-path branches with the
  guard or its negation as `requires`.
- `logos.program_contract`, sequence helpers and the total-correctness binary
  search example.
- `logos.domains.logic_puzzles` with Knights and Knaves, and the guided proof
  entry points.
- `logos.domains.number_theory`: transparent `divides`, `prime` and
  `factorial`, plus checked lemmas from divisibility through Euclid's theorem.
- A checked interval domain, `logos.domains.intervals`, with transparent
  definitions, four lemmas and a goal-level linear tactic.
- `logos example primes`: a strict certificate that every integer `n >= 2` has
  a prime above it, plus the script that rebuilds it.

### Book and documentation

- One English Scriptorium book, executable end to end, from the first checked
  proof through number theory to Euclid's theorem.
- The English binary-search and production-contract chapters, with a strict
  certificate for the standard-library `punycode.adapt`.
- The English Developer Guide and a generated Public API Reference, with a rift
  gate over every public class, function and method.
- The finite-graph chapter was removed until the library grows a graph domain;
  its published URL now redirects to the binary-search chapter.
- The book builds the public site, the PDF, the old Quarto redirects and the
  offline reading bundled in the wheel.
- `python -m logos book` and `logos.book` expose the bundled offline reading,
  with `--pdf`, `--open`, `--serve`, `--path` and `--json`.

### Packaging

- The release wheel and sdist carry the rendered HTML book, its PDF and a
  manifest with their SHA-256 digests.
- MIT license shipped as `LICENSE` and declared with PEP 639 metadata.
- `RELEASING.md` records the build order, the artifact gates and the supported
  targets.
