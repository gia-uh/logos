---
theme: book
title: Public API Reference
stem: api-reference
---

# Public API Reference

This chapter is generated from the installed source by
`tools/generate_api_reference.py`. It exists so every public class, function and
method has a named place in the book. The rift rule in `.rift.yaml` reports a
class missing from the chapters as an error; the reference test fails when this
page and the source disagree.

“Public” here means a non-underscore top-level class, or a non-underscore
function or a method declared with `self` or `cls`. Names that begin with an
underscore are implementation details, even when another module imports them.

## Classes

| Class | Module | Purpose |
| --- | --- | --- |
| `AuthoringFailure` | `logos.authoring` | A failed authoring step with a human message and machine data. |
| `Fact` | `logos.authoring` | A proposition and checked evidence for it, plus where it was written. |
| `ProofContext` | `logos.authoring` | The ``p`` argument of a book-style proof function. |
| `BookNotInstalled` | `logos.book` | The distribution has no offline book and no rendered checkout. |
| `LogosContractError` | `logos.contracts` | A contract, or the source binding behind it, could not be established. |
| `Contract` | `logos.contracts` | The two halves of a function contract, written with signature names. |
| `ProgramTheorem` | `logos.contracts` | A contract theorem whose executable body is a checked loop program. |
| `ContractTheorem` | `logos.contracts` | A theorem whose statement comes from a source-bound function contract. |
| `Function` | `logos.define` | A logos-defined function. Callable (builds App nodes) and carries its definition. |
| `Entity` | `logos.domains` | Base class for a domain entity. |
| `Domain` | `logos.domains` | Abstract base for constraint domains over typed entities. |
| `BinaryChoice` | `logos.domains._finite` | — |
| `Counterexample` | `logos.domains._finite` | — |
| `MissingRolePremise` | `logos.domains._finite` | — |
| `KKEntity` | `logos.domains.logic_puzzles` | An entity in a Knights-and-Knaves puzzle. |
| `KnightsKnaves` | `logos.domains.logic_puzzles` | Domain for knights-and-knaves (truth-teller / liar) puzzles. |
| `Expr` | `logos.expr` | Base class for all expression nodes. Operators build expression trees. |
| `Lit` | `logos.expr` | — |
| `Var` | `logos.expr` | — |
| `Add` | `logos.expr` | — |
| `Sub` | `logos.expr` | — |
| `Mul` | `logos.expr` | — |
| `Div` | `logos.expr` | — |
| `Mod` | `logos.expr` | — |
| `Neg` | `logos.expr` | — |
| `Pow` | `logos.expr` | — |
| `Len` | `logos.expr` | — |
| `Nth` | `logos.expr` | — |
| `Sorted` | `logos.expr` | — |
| `Eq` | `logos.expr` | — |
| `Neq` | `logos.expr` | — |
| `Lt` | `logos.expr` | — |
| `Le` | `logos.expr` | — |
| `Gt` | `logos.expr` | — |
| `Ge` | `logos.expr` | — |
| `And` | `logos.expr` | — |
| `Or` | `logos.expr` | — |
| `Not` | `logos.expr` | — |
| `Implies` | `logos.expr` | — |
| `ForallNode` | `logos.expr` | — |
| `ExistsNode` | `logos.expr` | — |
| `App` | `logos.expr` | — |
| `CaseExpr` | `logos.expr` | — |
| `Goal` | `logos.goal` | — |
| `KernelError` | `logos.kernel` | — |
| `Context` | `logos.kernel` | — |
| `ProofTerm` | `logos.kernel` | — |
| `Refl` | `logos.kernel` | — |
| `Symm` | `logos.kernel` | — |
| `Trans` | `logos.kernel` | — |
| `CoreLaw` | `logos.kernel` | — |
| `Congr` | `logos.kernel` | — |
| `Block` | `logos.kernel` | — |
| `StepRef` | `logos.kernel` | — |
| `Linear` | `logos.kernel` | — |
| `ProgramRef` | `logos.kernel` | — |
| `Have` | `logos.kernel` | — |
| `Note` | `logos.kernel` | Authored commentary that travels after its checked evidence. |
| `Subst` | `logos.kernel` | — |
| `Axiom` | `logos.kernel` | — |
| `AxiomRef` | `logos.kernel` | — |
| `TheoremRef` | `logos.kernel` | — |
| `HypRef` | `logos.kernel` | — |
| `ForallIntro` | `logos.kernel` | — |
| `ForallElim` | `logos.kernel` | — |
| `ImpliesIntro` | `logos.kernel` | — |
| `ImpliesElim` | `logos.kernel` | — |
| `AndIntro` | `logos.kernel` | — |
| `AndElimL` | `logos.kernel` | — |
| `AndElimR` | `logos.kernel` | — |
| `OrIntroL` | `logos.kernel` | — |
| `OrIntroR` | `logos.kernel` | — |
| `CaseAnalysis` | `logos.kernel` | Proves C given: proof of (A\|B), proof of C with A as hyp, proof of C with B as hyp. |
| `NotIntro` | `logos.kernel` | Proves ~A given proof of A >> False. |
| `NotElim` | `logos.kernel` | Proves False from proofs of ~A and A. |
| `ExFalso` | `logos.kernel` | Proves anything given proof of False (ex falso quodlibet). |
| `ExistsIntro` | `logos.kernel` | Proves Exists(x, P) given a witness w and a proof of P[x := w]. |
| `ExistsElim` | `logos.kernel` | Proves C from Exists(x, P) and a proof of C under P[x := var]. |
| `EqSubst` | `logos.kernel` | Leibniz elimination: from a == b and P[a], derive P[b]. |
| `Induction` | `logos.kernel` | Ordinary induction on integers at or above ``lower``. |
| `Least` | `logos.kernel` | Least element of a nonempty integer predicate at or above ``lower``. |
| `RecursorBase` | `logos.kernel` | The base equation f(0) = base of a primitive-recursive function. |
| `RecursorStep` | `logos.kernel` | The step equation f(k + 1) = step(k, f(k)) for k >= 0. |
| `LogosProofError` | `logos.portable` | A rejected proof. |
| `ProofReceipt` | `logos.portable` | A verification result for the exact immutable artifact bytes. |
| `ProgramVariable` | `logos.programs` | — |
| `Assign` | `logos.programs` | — |
| `If` | `logos.programs` | — |
| `While` | `logos.programs` | — |
| `Return` | `logos.programs` | — |
| `Program` | `logos.programs` | — |
| `ProgramContract` | `logos.programs` | — |
| `ProofSearchError` | `logos.proofs` | — |
| `TacticFailed` | `logos.runner` | — |
| `TrailingTactics` | `logos.runner` | A tactic closed the goal while tactics remained in the list. |
| `SeqType` | `logos.sequence` | The sort of finite integer sequences. |
| `Equation` | `logos.tactics._ring` | — |
| `Ring` | `logos.tactics._ring` | — |
| `Axiom` | `logos.theorem` | An author-declared assumption. |
| `Theorem` | `logos.theorem` | A statement with tactics that can be verified by logos.check(). |

## Functions and methods

| Name | Module | Purpose |
| --- | --- | --- |
| `var` | `logos` | — |
| `vars` | `logos` | — |
| `lit` | `logos` | — |
| `forall` | `logos` | logos.forall(int, int, lambda x, y: x + y == y + x) — lambda form. |
| `chain` | `logos` | Right-associative implication chain: chain(A, B, C) = A >> (B >> C). |
| `exists` | `logos` | — |
| `main` | `logos.__main__` | — |
| `format_expr` | `logos.authoring` | Render an expression the way a reader writes it in the book. |
| `as_dict` | `logos.authoring.AuthoringFailure` | — |
| `unfold` | `logos.authoring` | Unfold transparent definitions throughout a proposition. |
| `left` | `logos.authoring.Fact` | — |
| `right` | `logos.authoring.Fact` | — |
| `failure` | `logos.authoring.ProofContext` | — |
| `note` | `logos.authoring.ProofContext` | Attach authored commentary after the most recently derived fact. |
| `assume` | `logos.authoring.ProofContext` | — |
| `obtain` | `logos.authoring.ProofContext` | — |
| `apply` | `logos.authoring.ProofContext` | Instantiate a checked theorem (or local implication fact) step by step. |
| `and_intro` | `logos.authoring.ProofContext` | — |
| `exists` | `logos.authoring.ProofContext` | Package a witness as evidence for an existential statement. |
| `subst` | `logos.authoring.ProofContext` | Replace one side of an equality throughout a fact. |
| `refl` | `logos.authoring.ProofContext` | — |
| `symm` | `logos.authoring.ProofContext` | — |
| `trans` | `logos.authoring.ProofContext` | — |
| `not_elim` | `logos.authoring.ProofContext` | — |
| `ex_falso` | `logos.authoring.ProofContext` | — |
| `not_lt_of_lt` | `logos.authoring.ProofContext` | From ``low < high`` derive ``~(high < low)`` without a new axiom. |
| `order` | `logos.authoring.ProofContext` | Cite a core order law with explicit integer arguments and premises. |
| `linear` | `logos.authoring.ProofContext` | Prove a linear inequality from named facts with a checked certificate. |
| `recursor_base` | `logos.authoring.ProofContext` | — |
| `recursor_step` | `logos.authoring.ProofContext` | — |
| `rewrite` | `logos.authoring.ProofContext` | Rewrite the second argument of a transparent ``divides`` fact. |
| `least` | `logos.authoring.ProofContext` | Apply the least-element rule to a nonempty bounded predicate. |
| `fix` | `logos.authoring.ProofContext` | — |
| `negate` | `logos.authoring.ProofContext` | — |
| `cases` | `logos.authoring.ProofContext` | — |
| `contradict` | `logos.authoring.ProofContext` | — |
| `induction` | `logos.authoring.ProofContext` | — |
| `ring` | `logos.authoring.ProofContext` | — |
| `witness` | `logos.authoring.ProofContext` | — |
| `finish` | `logos.authoring.ProofContext` | — |
| `finish` | `logos.authoring._Scope` | — |
| `close` | `logos.authoring._Scope` | — |
| `left` | `logos.authoring._Cases` | — |
| `right` | `logos.authoring._Cases` | — |
| `finish` | `logos.authoring._Cases` | — |
| `base` | `logos.authoring._Induction` | — |
| `step` | `logos.authoring._Induction` | — |
| `binders_and_body` | `logos.authoring` | — |
| `authoring_signature_matches` | `logos.authoring` | — |
| `authoring_tactic` | `logos.authoring` | Wrap a book-style proof function as a tactic for the existing runner. |
| `root` | `logos.book` | The directory holding ``site/`` and ``book.pdf``. |
| `site` | `logos.book` | The directory that holds ``index.html`` and the offline pages. |
| `pdf` | `logos.book` | The downloadable, self-contained PDF. |
| `index` | `logos.book` | The book's home page. |
| `manifest` | `logos.book` | The packaged book's metadata, or an empty mapping for a checkout render. |
| `serve` | `logos.book` | Serve the offline pages on localhost until interrupted. |
| `main` | `logos.book` | — |
| `contract` | `logos.contracts` | Describe a postcondition and an optional explicit precondition. |
| `selected` | `logos.contracts._Fragment` | — |
| `theorem_about` | `logos.contracts` | Build the contract theorem for an ordinary function. |
| `law_sorts` | `logos.core_laws` | — |
| `law_statement` | `logos.core_laws` | — |
| `get_definition` | `logos.define` | — |
| `define` | `logos.define` | @logos.define decorator — creates a Function object. |
| `recursor` | `logos.define` | Declare a primitive-recursive integer function on the naturals. |
| `extern` | `logos.define` | Declare an external (uninterpreted) function symbol. |
| `definition` | `logos.define` | The book spelling of :func:`define` for transparent propositions. |
| `cases` | `logos.define` | — |
| `if_` | `logos.define` | — |
| `theorem` | `logos.domains.Domain` | Build a logos Theorem encoding all domain axioms as premises. |
| `solve` | `logos.domains.Domain` | Try every candidate conclusion; return the unique consistent one. |
| `premises` | `logos.domains._finite.BinaryChoice` | — |
| `validate` | `logos.domains._finite` | — |
| `bind` | `logos.domains._finite` | — |
| `theorem` | `logos.domains._finite` | — |
| `budget` | `logos.domains._finite` | — |
| `certify` | `logos.domains._finite` | Split into role cases, close impossible branches, and prove the goal in the rest. |
| `solve` | `logos.domains._finite` | Return all models and prepare evidence only for a unique result. |
| `sentence` | `logos.domains._prose` | Compose a sentence, letting the domain supply atoms and exact idioms. |
| `contains` | `logos.domains.intervals` | The closed interval [lo, hi] contains x. |
| `overlaps` | `logos.domains.intervals` | The closed intervals [a_lo, a_hi] and [b_lo, b_hi] share a point. |
| `interval` | `logos.domains.intervals` | Close an overlap goal with a checked linear certificate. |
| `overlap_self` | `logos.domains.intervals` | A nonempty interval overlaps itself. |
| `prove_overlap_self` | `logos.domains.intervals` | Both sides of the overlap are the same non-strict bound. |
| `overlap_comm` | `logos.domains.intervals` | Overlap is symmetric. |
| `prove_overlap_comm` | `logos.domains.intervals` | Swap the two conjuncts. |
| `common_point_overlaps` | `logos.domains.intervals` | A point contained in both intervals witnesses an overlap. |
| `prove_common_point_overlaps` | `logos.domains.intervals` | Chain the two containment bounds through x. |
| `disjoint_no_common_point` | `logos.domains.intervals` | An interval entirely to the left shares no point with one to its right. |
| `prove_disjoint_no_common_point` | `logos.domains.intervals` | A common point would force a_hi < b_lo <= x <= a_hi. |
| `check_all` | `logos.domains.intervals` | Check every lemma with the installed Rust verifier. |
| `is_knight` | `logos.domains.logic_puzzles.KKEntity` | — |
| `is_knave` | `logos.domains.logic_puzzles.KKEntity` | — |
| `says` | `logos.domains.logic_puzzles.KKEntity` | Record that this entity asserts stmt. |
| `solve_status` | `logos.domains.logic_puzzles.KnightsKnaves` | The status of the last solve for the current puzzle, or None before solving. |
| `entity` | `logos.domains.logic_puzzles.KnightsKnaves` | Add an inhabitant with a distinct name. |
| `describe` | `logos.domains.logic_puzzles.KnightsKnaves` | Render the claim itself in English without checking its truth. |
| `solve` | `logos.domains.logic_puzzles.KnightsKnaves` | Return one assignment, all alternatives, or None; see solve_status. |
| `export_proof` | `logos.domains.logic_puzzles.KnightsKnaves` | Verify the unique result with Rust and write its conditional proof. |
| `prove` | `logos.domains.logic_puzzles.KnightsKnaves` | Introduce the puzzle premises, run tactics, and return a Rust-checked theorem. |
| `cases_on_role` | `logos.domains.logic_puzzles.KnightsKnaves` | Open the knight branch first and the knave branch second. |
| `use_statements` | `logos.domains.logic_puzzles.KnightsKnaves` | Add the truth or negation of utterances by speakers with a known role. |
| `auto` | `logos.domains.logic_puzzles.KnightsKnaves` | Use finite role reasoning to finish the current open goal. |
| `divides` | `logos.domains.number_theory` | d divides a when some integer k makes a equal to d * k. |
| `prime` | `logos.domains.number_theory` | A prime is greater than one and has no divisor strictly between 1 and q. |
| `divides_self` | `logos.domains.number_theory` | Every integer divides itself. |
| `prove_divides_self` | `logos.domains.number_theory` | The quotient is one. |
| `divides_trans` | `logos.domains.number_theory` | Divisibility is transitive. |
| `prove_divides_trans` | `logos.domains.number_theory` | Multiply the two quotient equations. |
| `divides_mul` | `logos.domains.number_theory` | A multiple of b is still a multiple of any divisor of b. |
| `prove_divides_mul` | `logos.domains.number_theory` | Scale the quotient by c. |
| `common_divisor` | `logos.domains.number_theory` | A divisor of two consecutive integers divides one. |
| `prove_common_divisor` | `logos.domains.number_theory` | Subtract the two quotient equations; the difference is one. |
| `not_dvd_one` | `logos.domains.number_theory` | No integer greater than one divides one. |
| `prove_not_dvd_one` | `logos.domains.number_theory` | A product equal to one forces both factors to be 1 or -1. |
| `factorial_positive` | `logos.domains.number_theory` | The factorial of a nonnegative integer is positive. |
| `prove_factorial_positive` | `logos.domains.number_theory` | Induct from 0! = 1 and close the step with a product of positives. |
| `mul_succ` | `logos.domains.number_theory` | Multiplying by a successor distributes the successor. |
| `prove_mul_succ` | `logos.domains.number_theory` | Expand the left side. |
| `lt_add_pos` | `logos.domains.number_theory` | Adding a positive integer keeps a strict inequality. |
| `prove_lt_add_pos` | `logos.domains.number_theory` | Linear arithmetic combines the two hypotheses. |
| `factorial_above_one` | `logos.domains.number_theory` | From 2 onward the factorial is greater than one. |
| `prove_factorial_above_one` | `logos.domains.number_theory` | Induct from 2! = 2 and add the positive term k * k!. |
| `factorial_dvd` | `logos.domains.number_theory` | Every integer above one and at most n divides n!. |
| `prove_factorial_dvd` | `logos.domains.number_theory` | Induct on n, splitting the new divisor into d < k + 1 and d = k + 1. |
| `least_prime_divisor` | `logos.domains.number_theory` | Every integer above one has a prime divisor. |
| `prove_least_prime_divisor` | `logos.domains.number_theory` | Take the least divisor above one; a proper divisor would contradict it. |
| `euclid` | `logos.domains.number_theory` | For every n at least two there is a prime greater than n. |
| `prove_euclid` | `logos.domains.number_theory` | Build n! + 1, take its least prime divisor and rule out q <= n. |
| `check_all` | `logos.domains.number_theory` | Check every lemma in dependency order and return their names. |
| `example` | `logos.domains.number_theory` | A concrete case: five factorial plus one is 121, whose least prime factor is 11. |
| `Forall` | `logos.expr` | Forall(x, y, body) → nested ForallNode(x, ForallNode(y, body)). |
| `Exists` | `logos.expr` | — |
| `with_hyp` | `logos.goal.Goal` | — |
| `with_statement` | `logos.goal.Goal` | — |
| `normalize_order` | `logos.helpers` | Rewrite ``>``, ``>=`` and ``!=`` into the portable core forms. |
| `structural_eq` | `logos.helpers` | — |
| `substitute` | `logos.helpers` | Replace all free occurrences of `var` in `expr` with `val`. |
| `free_symbol_ids` | `logos.helpers` | — |
| `substitute_symbols` | `logos.helpers` | Substitute by object identity, dropping mappings for shadowed binders. |
| `try_unify` | `logos.helpers` | Match pattern against target with flex_vars as unifiable variables. |
| `free_vars` | `logos.helpers` | — |
| `with_hyp` | `logos.kernel.Context` | — |
| `lookup` | `logos.kernel.Context` | — |
| `infer` | `logos.kernel` | Infer the statement proved by `term` under `ctx`. Raises KernelError if invalid. |
| `check` | `logos.kernel` | Validate that `term` proves `expected`. Raises KernelError on mismatch. |
| `order_law` | `logos.order` | Return the full proposition asserted by ``law`` at ``args``. |
| `split_implications` | `logos.order` | Return the antecedents and the consequent of an implication chain. |
| `statement_declarations` | `logos.portable` | Collect free symbol objects in occurrence order in the supported fragment. |
| `artifact_bytes` | `logos.portable` | — |
| `verify_artifact` | `logos.portable` | — |
| `inspect_artifact` | `logos.portable` | Return the Rust checker's Markdown reading of these exact proof bytes. |
| `export_proof` | `logos.portable` | Write the current checked artifact for a named or anonymous proof. |
| `variables` | `logos.programs.Program` | — |
| `program_contract` | `logos.programs` | — |
| `wp` | `logos.proofs._Generator` | — |
| `reads_in` | `logos.proofs._Generator` | — |
| `verification_conditions` | `logos.proofs` | — |
| `scaled` | `logos.proofs._Constraint` | — |
| `plus` | `logos.proofs._Constraint` | — |
| `farkas` | `logos.proofs` | — |
| `fresh` | `logos.proofs._Search` | — |
| `prove` | `logos.proofs._Search` | — |
| `prove_condition` | `logos.proofs` | — |
| `build_program_obligations` | `logos.proofs` | — |
| `run` | `logos.runner` | Apply tactics in `by` to `goal`, returning a proof term. |
| `run` | `logos.runner._Runner` | — |
| `seq_var` | `logos.sequence` | — |
| `length` | `logos.sequence` | — |
| `nth` | `logos.sequence` | — |
| `sorted` | `logos.sequence` | The checker-owned sortedness predicate over a sequence. |
| `in_bounds` | `logos.sequence` | — |
| `absent` | `logos.sequence` | Every in-range index holds something other than ``target``. |
| `occurrence` | `logos.sequence` | Some in-range index holds ``target``. |
| `emit` | `logos.tactics._ring.Ring` | — |
| `key` | `logos.tactics._ring.Ring` | — |
| `law` | `logos.tactics._ring.Ring` | — |
| `reverse` | `logos.tactics._ring.Ring` | — |
| `chain` | `logos.tactics._ring.Ring` | — |
| `lift` | `logos.tactics._ring.Ring` | — |
| `left_zero` | `logos.tactics._ring.Ring` | — |
| `cancel_left` | `logos.tactics._ring.Ring` | Derive −a + (a + b) = b. |
| `times_zero` | `logos.tactics._ring.Ring` | Distribution gives q + q = q for q = a*0. Cancel q. |
| `as_product` | `logos.tactics._ring.Ring` | Derive a = 1*a. |
| `factor` | `logos.tactics._ring.Ring` | Derive a*m + b*m = (a+b)*m using the pinned left distributive law. |
| `neg_as_product` | `logos.tactics._ring.Ring` | Both (−1)*a and −a add to zero against a. Cancel a. |
| `coefficients` | `logos.tactics._ring.Ring` | — |
| `monomial_key` | `logos.tactics._ring.Ring` | — |
| `factor_key` | `logos.tactics._ring.Ring` | — |
| `add_coefficients` | `logos.tactics._ring.Ring` | — |
| `join` | `logos.tactics._ring.Ring` | Join ordered operands, removing the operator's unit and zero factors. |
| `insert` | `logos.tactics._ring.Ring` | Insert into a sorted, right-associated sum or product. |
| `merge` | `logos.tactics._ring.Ring` | Merge sorted, right-associated operands of an associative operator. |
| `multiply` | `logos.tactics._ring.Ring` | — |
| `normalize` | `logos.tactics._ring.Ring` | — |
| `normalize_uncached` | `logos.tactics._ring.Ring` | — |
| `prove` | `logos.tactics._ring.Ring` | — |
| `ring` | `logos.tactics.arithmetic` | Derive an integer polynomial identity from the core ring laws. |
| `order` | `logos.tactics.arithmetic` | Close a strict-order goal with one core order law. |
| `decide` | `logos.tactics.arithmetic` | Evaluate a ground boolean proposition and close the goal. |
| `linarith` | `logos.tactics.arithmetic` | — |
| `auto` | `logos.tactics.auto` | Automatic tactic. Tries a cascade of strategies up to `depth` search levels. |
| `then` | `logos.tactics.combinators` | Apply tactics in sequence to the current goal (as a single compound tactic). |
| `first` | `logos.tactics.combinators` | Try each tactic in order; succeed with the first that doesn't raise TacticFailed. |
| `try_` | `logos.tactics.combinators` | Apply tactic_fn; if it fails, return a no-op (transforms goal to itself). |
| `repeat` | `logos.tactics.combinators` | Apply tactic_fn until it fails; apply all successful steps. |
| `all_goals` | `logos.tactics.combinators` | Apply tactic_fn to each open subgoal (for use after a splitting tactic). |
| `refl` | `logos.tactics.rewrite` | — |
| `eval_` | `logos.tactics.rewrite` | Evaluate ground (variable-free) arithmetic sub-expressions, then close with Refl. |
| `norm_num` | `logos.tactics.rewrite` | Normalize numeric literals and close if equal. |
| `unfold` | `logos.tactics.rewrite` | Replace App(name, args) nodes with the function's definition body. |
| `rewrite` | `logos.tactics.rewrite` | Rewrite left-to-right using a named equation or Axiom/Theorem object. |
| `rewrite_rev` | `logos.tactics.rewrite` | Rewrite right-to-left using a named equation or Axiom/Theorem object. |
| `intro` | `logos.tactics.structural` | — |
| `assumption` | `logos.tactics.structural` | — |
| `exact` | `logos.tactics.structural` | — |
| `apply` | `logos.tactics.structural` | Apply a theorem/axiom/hypothesis to close or transform the goal. |
| `split` | `logos.tactics.structural` | — |
| `left` | `logos.tactics.structural` | — |
| `right` | `logos.tactics.structural` | — |
| `witness` | `logos.tactics.structural` | Choose a witness and open the instantiated predicate as a proof goal. |
| `cases` | `logos.tactics.structural` | Case analysis on a hypothesis A \| B in context. |
| `have` | `logos.tactics.structural` | Forward modus ponens: from impl_hyp: A→B and ant_hyp: A, add new_name: B. |
| `andL` | `logos.tactics.structural` | Extract left conjunct: from h: A & B, add result_name: A. |
| `andR` | `logos.tactics.structural` | Extract right conjunct: from h: A & B, add result_name: B. |
| `conj` | `logos.tactics.structural` | Conjunction intro: from h1: A and h2: B, add result_name: A & B. |
| `contradiction` | `logos.tactics.structural` | — |
| `receipt` | `logos.theorem._Proof` | — |
| `certified` | `logos.theorem._Proof` | — |
| `inspect` | `logos.theorem._Proof` | Return the Rust checker's Markdown reading of the current receipt. |
| `proof` | `logos.theorem.Theorem` | Attach proof spec. |
| `check` | `logos.theorem.Theorem` | Check this theorem now and certify its actual evidence. |
| `axiom` | `logos.theorem` | @logos.axiom decorator or logos.axiom(expr) — creates a trusted Axiom. |
| `theorem` | `logos.theorem` | @logos.theorem decorator — creates a Theorem object (no proof yet). |
| `check` | `logos.theorem` | Run the tactics and certify their actual evidence with the Rust checker. |
| `prove` | `logos.theorem` | Two modes: |

## Where to read next

The [Developer Guide](extend-the-checked-language-with-a-domain.html) shows how these
pieces fit when you extend the checked language. The [proof format](https://github.com/gia-uh/logos/blob/main/docs/portable-proof-format.md)
states the bytes an independent recipient verifies. For a use-case path through
the same API, start at the introduction and follow the chapters in order.
