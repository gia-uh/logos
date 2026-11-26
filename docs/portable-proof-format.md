# Portable proof format, version 1

A `.logos` file is a UTF-8 JSON object. All fields shown below are required
unless marked optional. Unknown fields, versions and tags are rejected.
`logos commands --json` includes the format and result contract in the
installed checker. Earlier v1 files with empty dependency lists still replay.

| Object | Fields |
| --- | --- |
| Proof file | `format: "logos-proof-v1"`, `theory: "logos-core-v1"`, optional `name: string or null`, `declarations: [Declaration]`, optional `functions: [Function]`, `custom_axioms: [CustomAxiom]`, `lemmas: [Lemma]`, `target: Expression`, `proof: Evidence` |
| Declaration | `id: string`, `name: string` (display label), `sort: "prop" \| "int"` |
| Function | `id: string`, `name: string`, `params: [Sort]`, `result: Sort`, optional `body: Expression` |
| CustomAxiom | `id: string`, `statement: Expression` |
| Lemma | `id: string`, `statement: Expression`, `proof: Evidence` |

IDs are nonempty strings and unique across all bundle lists. The eight
core-law IDs are reserved. Display labels may repeat. A symbol declaration
alone assumes no truth. Transparent function bodies can reference earlier
function declarations and take the declared parameters as bound variables.
Omitting a body declares an opaque function.

| Expression tag | Other fields |
| --- | --- |
| `symbol` | `id` of a symbol declaration |
| `bound` | Zero-based `index` counting outward from the nearest binder. In a function body, the last parameter has index 0 at the root. |
| `int` | `value` as a signed decimal string |
| `add`, `sub`, `mul` | Integer `left` and `right` |
| `neg` | Integer `operand` |
| `pow` | Integer `base` and natural literal `exponent` |
| `eq` | `left` and `right` of the same sort |
| `and`, `or`, `implies` | Propositions `left` and `right` |
| `not` | Proposition `operand` |
| `false` | No fields. The proposition falsehood (⊥). |
| `forall` | Display `name`, binder `sort`, and proposition `body` |
| `app` | Function `id` and corresponding `args` |

| Evidence tag | Other fields and checked rule |
| --- | --- |
| `implies_intro` | `binder`, proposition `premise`, and proof `body`. Introduces and discharges a local hypothesis. |
| `implies_elim` | Proofs `implication` and `premise`. The premise must match the antecedent. Derives the consequent. |
| `hyp_ref` | `binder`. Uses the nearest enclosing local hypothesis with that name. |
| `and_intro` | `left` and `right` proofs. |
| `and_elim_l`, `and_elim_r` | `proof` of a conjunction. |
| `or_intro_l`, `or_intro_r` | `proof` of the chosen disjunct and a proposition `other` for the opposite disjunct. |
| `or_elim` | `proof` of a disjunction, a hypothesis `binder`, and `left` and `right` branch proofs. Each branch binds its own disjunct under that name. Both branches must derive convertible conclusions, and both assumptions are discharged. |
| `not_intro` | `proof` of an implication from the operand to falsehood. |
| `not_elim` | Proofs `negation` and `premise`, the latter matching the negated operand. Derives falsehood. |
| `ex_falso` | `proof` of falsehood and a proposition `conclusion` to derive. |
| `axiom_ref`, `theorem_ref` | `id` of a custom axiom or a checked lemma, respectively. |
| `forall_intro` | Binder `name`, `sort`, and proof `body` under the fresh arbitrary variable. |
| `forall_elim` | Universal `proof` and instantiation `term` of the binder's sort. |
| `refl` | A well-sorted `term`. Derives equality of that term with itself. |
| `symm` | Equality `proof`. |
| `trans` | Equality proofs `left` and `right` with convertible middle expressions. |
| `congr` | Equality `proof` and expression `context` with an extra innermost binder of the operands' sort. Substitutes each operand into the context. |
| `core_law` | Law `id` and ordered integer substitution `args`. |
| `block` | `steps` and zero-based `result` index. The result and all its step dependencies must verify. |
| `step_ref` | `index` of an earlier step within the innermost block. |

The target and each lemma start with empty local scopes. Rust checks
reachable lemmas in dependency order and rejects cycles. Every supplied
declaration, custom axiom and lemma statement is still subject to namespace
and sort checks. A block can share earlier evidence by index. An unreachable
block instruction or lemma cannot contribute assumptions to a judgment.
Local hypotheses and shared conclusions are lifted when read under fresh
binders. Case hypotheses exist only inside the corresponding branch, including
when they shadow an outer hypothesis. Falsehood has no literal proof term.
Rule premises match under the same conversion as theorem conclusions.

### Conversion and the integer laws

Conversion compares typed syntax up to bound-variable renaming after
recursive unfolding of transparent definitions and the specified integer
reductions. Substitution under binders is capture-avoiding. Subtraction
reduces to addition with negation. Powers expand from `a⁰ = 1` and
`aⁿ⁺¹ = aⁿ · a`, including `0⁰ = 1`. Literal addition, multiplication and
negation compute exact integer results. Free symbols and opaque functions
retain their declaration identities. Symbolic commutation, cancellation and
distribution require checked evidence.

| Core law | Checker-owned equality over integers |
| --- | --- |
| `add_assoc` | `(a + b) + c = a + (b + c)` |
| `add_comm` | `a + b = b + a` |
| `add_zero` | `a + 0 = a` |
| `add_inverse` | `a + (−a) = 0` |
| `mul_assoc` | `(a · b) · c = a · (b · c)` |
| `mul_comm` | `a · b = b · a` |
| `mul_one` | `a · 1 = a` |
| `distrib` | `a · (b + c) = a · b + a · c` |

The checker rejects inputs beyond its replay resource limits, including
proof files over 8 MiB and integer computations over 65,536 bits. A limit
error is a failed replay. Integer results are exact within the limits.

## Results and policy

`logos check FILE` verifies the proof. Exit 0 includes conditional proofs.
`logos check --strict FILE` and `logos inspect --strict FILE` verify the
same evidence and exit 3 if it uses a custom axiom. Exit 1 indicates invalid
input or I/O failure. Exit 2 indicates invalid command usage.

A result includes the verified target, a display string, core theory, and
`custom_axioms`. Each used axiom appears once with its full typed
statement and a checked path from the target to a use. The author-provided
label is unverified metadata. The SHA-256 digest identifies the checked
file bytes.

`logos inspect FILE` prints a readable trace. Use
`logos inspect --json FILE` for structured data suitable for reconstructing
the argument. The `claim` points to the verified target and its proof step.
Read `declarations` for free symbols, `functions` for definitions and opaque
signatures, and `custom_axioms` for assumptions.

- Follow `steps[].premises` from `claim.proof_step`. Steps are ordered with
  premises first. Their IDs are structural paths rooted at `proof` or
  `lemma["ID"].proof`. A `step_ref` links to a shared intermediate
  derivation within a block.
- Each step has a `rule`, checker-written `explanation`, typed
  `conclusion` and `context_id`. Contexts list arbitrary variables from
  oldest to newest, so bound index 0 refers to the last variable. They
  also link to the active local assumptions by their step IDs.
  `binder_depth` records how many variables were in scope when the
  assumption was introduced. Introductions and discharges link to the
  affected variable or assumption. For `or_elim`, `discharged_cases`
  lists the left and right local assumption step IDs in that order. Its
  premises list the disjunction, the left assumption and result, and the
  right assumption and result. The result's context excludes both case
  assumptions.
- `provenance` distinguishes core laws, author assumptions, checked lemmas
  and local hypotheses. A `law` gives the formal equality and the named
  formal-to-actual substitution. Symbols in that formal equality name
  law parameters rather than bundle declarations.
- `premise_conversion` records the common normal form when a transitivity
  step composes syntactically different middle expressions, or when a
  logic rule compares syntactically different but convertible premises.
  `conclusion_conversion` links a derivation's result to a differently
  written target or lemma statement.

Use `logos inspect --markdown --strict FILE > proof.md` to save a
deterministic GitHub Markdown derivation with LaTeX math. The document
introduces arbitrary variables and local hypotheses in prose, then groups
rewrites into equations with short local references. It distinguishes
assumptions from previously checked lemmas. Conversion rows show the compared expressions and their
checked common normal form. With `--strict`, a valid conditional proof
produces a document marked as denied and exits 3. An invalid proof produces
a diagnostic on stderr and no document. `--markdown` and `--json` are
mutually exclusive.

When writing your own proof from inspection, state the claim and introduce
the variables and hypotheses in words. Group routine rewrites into
equations and name the laws that justify them. Explain the final
conversion using the compared forms and distinguish assumptions from checked
lemmas. Leave internal step IDs, binder IDs, artifact names and hashes in
the audit record.

With `--json`, successful judgments and policy denials both go to stdout.
Their statuses are `verified` and `policy_denied`, respectively. Policy denial
still carries the assumptions and, for `inspect`, the checked steps. An
invalid proof emits an `error` diagnostic to stderr without a judgment.

Run `logos example` for the unconditional authorization proof. Run
`logos example dependencies` for both `dependencies.logos`, a ready-to-replay
proof of `Q` from `P ∧ Q`, and its Python source. Both examples ship in the
executable. Run `logos example arithmetic` for a ready-to-replay addition
commutativity proof and Python source that exports six integer identities.
The reference invalid authorization fixture swaps the projection
and derives the other conclusion.

## Knights and Knaves example

Install the Python wheel and put the checker on PATH. From an empty directory:

```bash
logos example knights-knaves
python solve_knights_knaves.py puzzle.logos
logos check --strict puzzle.logos
logos inspect --markdown --strict puzzle.logos > puzzle.md
```

The [caller example](../checker/examples/solve_knights_knaves.py) declares
inhabitants with `entity(name)` and records each utterance with `speaker.says(expr)`.
Each statement can use the puzzle's `is_knight()` and `is_knave()` propositions,
`&`, `|`, `~`, `>>` (implication), and `logos.lit(False)`. You can record several
statements for the same speaker.

`puzzle.solve()` searches assignments and prepares evidence for a unique result.
`puzzle.solve_status` describes its return value.

| Status | Return value |
| --- | --- |
| `unique` | One dictionary from inhabitant names to roles |
| `underdetermined` | A list of all satisfying assignments |
| `inconsistent` | `None` after finding zero satisfying assignments |
| `unknown` | `None` after exhausting the time budget |

Use `solve(timeout=seconds)` to change the default half-second search and evidence
construction budget. Use `timeout=None` for an unbounded search. Adding an
inhabitant or an utterance invalidates the previous result.

`puzzle.export_proof(path)` sends the generated evidence for a unique result
to the Rust checker and writes the verified bytes. The proof derives the
assignment from explicit exhaustivity, exclusivity and utterance premises.
Strict replay reports zero custom axioms because these premises are local and
discharged. Model witnesses come from Python search. The checker verifies the
conditional derivation, while model existence is a separate claim.

For domain authors, the [manual proof example](../checker/examples/knights_knaves.py)
shows how to attach evidence to `KnightsKnaves.theorem(conclusion)` using the
same premises and proof format.

## Authoring and certification

Use `logos.var(name, bool)` for proposition symbols or `logos.var(name, int)`
for integer symbols. Use `@logos.theorem` with typed parameters and
`t.intro(...)` for scoped universal proofs. `t.ring()` constructs evidence
from integer polynomial normalization. Its certificates contain instances
of the eight core laws and explicit equality and congruence steps. Distinct Python symbol
objects keep distinct IDs even when their labels match. In this fragment,
each theorem's declaration context starts from its statement's symbols in
first-occurrence order. Shared symbol objects use the same ID across the
bundle. `proof.declarations` controls the symbols available to that proof.

Use `P | Q` for disjunction, `~P` for negation, and `logos.lit(False)`
for falsehood. The `left` and `right` tactics introduce a disjunct.
`cases` opens one scoped subgoal per disjunct. On a negation goal,
`intro` assumes its operand and opens a goal of falsehood.
`contradiction` constructs a proof of falsehood from the available
hypotheses, and `have` applies a local implication to its antecedent.
A custom tactic can return the corresponding terms from `logos.kernel`
(`OrIntroL`, `OrIntroR`, `CaseAnalysis`, `NotIntro`, `NotElim`,
`ExFalso`, and `ImpliesElim`).

`logos.tactics.apply` takes a local hypothesis name, an `Axiom`, or a
`Theorem`. To compose a custom tactic, use `AxiomRef(axiom)` or
`TheoremRef(lemma)` from `logos.kernel`. Attach a proof to every referenced
theorem. The exporter bundles the current evidence and Rust checks the
reachable lemma evidence even when the lemma has a separate receipt. A
dependency's name is its ID, with a generated ID assigned to unnamed
dependencies.

`logos.check` runs the target tactics and invokes `logos check --json -`
via the installed checker on PATH. Named, anonymous, and automatic entry
points share this verifier. A successful check records a `ProofReceipt` with
the immutable bytes and digest. `proof.certified` tracks whether the current
statement, declarations, evidence, and transitive dependencies still match
the receipt. A changed dependency can clear current certification before
another checker call. After invalidation, `logos.check` must verify the
corrected bundle to attach a new receipt. Previously saved receipts still
identify their original bytes. `logos.export_proof(proof, path)` writes the
current checked bytes. Python raises `LogosProofError` when verification
fails or evidence cannot be exported.

## Migration status

The pre-checker baseline had 91 passing Python tests. The propositional
slice added portable replay for scoped projection proofs. The dependency
slice added checked conditional proofs and assumption accounting.

The integer slice removes strict expected failures for
`test_prove_add_comm`, `test_theorem_certified_after_check`,
`test_check_idempotent`, `test_full_abs_nonneg`,
`test_proof_decorator_style`, `test_check_returns_theorem`,
`test_full_double_proof`, and `test_ground_proof`. Each check verifies the
current proof evidence. Arithmetic tests exercise the actual checker
judgment for the target.

| Remaining legacy test | Required work |
| --- | --- |
| `test_prove_linarith` | Inequalities and linear inequality automation. |
| `test_builtins_are_axiom_objects` | The legacy assertion treats the flag on an author-declared axiom as certification. The checked core laws are selected by theory ID and instantiated by the verifier. |

The portable checker also supports conjunction, disjunction, negation,
falsehood, implication, local hypotheses, and checked dependencies.
Existential rules and other domains remain milestone work.
