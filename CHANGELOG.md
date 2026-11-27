# Changelog

## [Unreleased]

### Features
- Finite integer sequences, `len`, `nth`, `sorted` and non-strict order in the portable core
- Checker-owned order, half-interval and sortedness laws with explicit soundness arguments
- Checked rational linear-arithmetic certificates (`linear`) and checked local facts (`have`)
- Source-bound loop programs with `program_ref`, recomputed loop obligations, read bounds and a termination variant
- `logos.program_contract`, sequence helpers and the total-correctness binary search example
- Mutation tests for wrong midpoints, wrong invariants, forged program bodies and missing obligations
- Scoped existential elimination (`exists_elim`) and equality substitution (`eq_subst`) in the portable core
- Integer induction (`induction`) and least element (`least`) over a lower bound
- Primitive-recursive integer definitions (`recursor`, `recursor_base`, `recursor_step`) with a predecessor-only recursive-call check
- Integer order and positivity laws: `mul_pos`, `mul_eq_one`, `lt_succ_fwd`, `lt_succ_rev`, `eq_of_not_lt_not_lt` and `lt_decidable`
- `logos example primes`: a strict certificate that every integer `n >= 2` has a prime above it, plus the script that rebuilds it
- The Python kernel now infers congruence terms

## [0.1.0] - 2026-06-17

### Features
- `logos.contract` / `@logos.theorem(about=...)` — prove a contract about an ordinary function from its source
- `@logos.theorem(about=...)` — prove one path of a function with a single `==`, `!=` or `<` branch, with the guard or its negation as `requires`
- Strict integer order in the portable core (`lt`) with the checker-owned laws `lt_irrefl`, `lt_trans`, `lt_add` and `lt_neq`, and the `t.order()` tactic
- Trusted proof kernel with 14 inference rules
- Expression language with full operator overloading (`+`, `-`, `*`, `//`, `%`, `**`, `==`, `!=`, `<`, `<=`, `>`, `>=`, `&`, `|`, `~`, `>>`)
- `@logos.define` — symbolic function definitions with auto-generated axioms
- `logos.theorem` / `logos.prove` — proof validation at definition time
- `logos.extern` — axiom declarations for external functions
- Bundled tactics: `ring`, `linarith`, `decide`, `intro`, `assumption`, `exact`, `apply`, `split`, `left`, `right`, `witness`, `unfold`, `refl`, `rewrite`, `eval_`, `norm_num`
- Tactic combinators: `then`, `first`, `try_`, `repeat`, `all_goals`
- Built-in ring axioms for integer arithmetic
