# Portable proof format, version 1

A `.logos` file is a UTF-8 JSON object. All fields shown below are required
unless marked optional. Unknown fields, versions and tags are rejected.
`logos commands --json` includes the format and result contract in the
installed checker. Earlier v1 files with empty dependency lists still replay.

| Object | Fields |
| --- | --- |
| Proof file | `format: "logos-proof-v1"`, `theory: "logos-core-v1"`, optional `name: string or null` (author label), `declarations: [Declaration]`, `custom_axioms: [CustomAxiom]`, `lemmas: [Lemma]`, `target: Proposition`, `proof: Evidence` |
| Declaration | `id: string`, `name: string` (display label), `sort: "prop" \| "int"` |
| CustomAxiom | `id: string`, `statement: Proposition` |
| Lemma | `id: string`, `statement: Proposition`, `proof: Evidence` |
| Proposition | `{"tag":"symbol","id":string}` or `{"tag":"and"\|"implies","left":Proposition,"right":Proposition}` |
| Evidence | `{"tag":"implies_intro","binder":string,"premise":Proposition,"body":Evidence}`, `{"tag":"hyp_ref","binder":string}`, `{"tag":"and_intro","left":Evidence,"right":Evidence}`, `{"tag":"and_elim_l"\|"and_elim_r","proof":Evidence}` or `{"tag":"axiom_ref"\|"theorem_ref","id":string}` |

IDs and binder names are nonempty strings. IDs are unique across the three
bundle lists. Display labels may repeat. A proposition symbol must resolve to
a declaration of sort `prop`. The `int` sort can be declared and has no term
constructors in this fragment. A symbol declaration alone assumes no truth.

Each lemma proof starts with an empty hypothesis scope. Rust checks bundled
lemmas in dependency order, rejects cycles and checks every derived
conclusion against its declared statement. A `theorem_ref` resolves to a
checked lemma. An `axiom_ref` resolves to an author-declared custom axiom.
These lookups use their own kinds and are independent of local binders.

The target also starts with an empty hypothesis scope. Implication
introduction adds a local hypothesis while checking its body, then discharges
it. Lookup resolves the nearest enclosing binder. Conjunction introduction
checks both children. Each projection requires a checked conjunction. The
derived conclusion must equal the target as syntax over declaration IDs.

## Results and policy

`logos check FILE` verifies the proof. Exit 0 includes conditional proofs.
`logos check --strict FILE` and `logos inspect --strict FILE` verify the
same evidence and exit 3 if it uses a custom axiom. Exit 1 indicates invalid
input or I/O failure. Exit 2 indicates invalid command usage.

A result includes the derived statement tree, a display string, core theory,
and `custom_axioms`. Each used custom axiom appears once with its `id`, full
`statement` tree, typed `statement_text` and `path` from the target proof to a
use of that axiom. Unused custom axioms and discharged local hypotheses are
excluded. Inspection adds the reachable checked rule applications in
premise-first order. Step IDs are structural paths rooted at `proof` or
`lemma["ID"].proof`. Reference steps have a `reference_id`. Local introductions
have `.assumption` and `.body` paths, projections have a `.proof` child, and
conjunction introductions have `.left` and `.right` children. The author
label is unverified metadata. The SHA-256 digest identifies the checked file
bytes.

With `--json`, successful judgments and policy denials both go to stdout.
Their statuses are `verified` and `policy_denied`, respectively. Policy denial
still carries the assumptions and, for `inspect`, the checked steps. An
invalid proof emits an `error` diagnostic to stderr without a judgment.

Run `logos example` for the unconditional authorization proof. Run
`logos example dependencies` for both `dependencies.logos`, a ready-to-replay
proof of `Q` from `P ∧ Q`, and its Python source. Both examples ship in the
executable. The reference invalid authorization fixture swaps the projection
and derives the other conclusion.

## Authoring and certification

Use `logos.var(name, bool)` for proposition symbols. Distinct Python symbol
objects keep distinct IDs even when their labels match. In this fragment,
each theorem's declaration context starts from its statement's symbols in
first-occurrence order. Shared symbol objects use the same ID across the
bundle. `proof.declarations` controls the symbols available to that proof.

`logos.tactics.apply` takes a local hypothesis name, an `Axiom`, or a
`Theorem`. To compose a custom tactic, use `AxiomRef(axiom)` or
`TheoremRef(lemma)` from `logos.kernel`. Attach a proof to every referenced
theorem. The exporter bundles the current evidence and Rust checks it even
when the lemma has a separate receipt. A dependency's name is its ID, with a
generated ID assigned to unnamed dependencies.

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

The pre-checker baseline had 91 passing Python tests. The first portable
slice added 15 Python tests. The dependency slice replaces the first-slice
external-reference rejection with checked conditional proof coverage. It
retains the stale-flag negative and the malformed Rust dependency inputs as
rejection tests. The legacy positive certification assertions still run with
strict expected failures for the following dependencies and behavior.

| Legacy tests | Checker work still required |
| --- | --- |
| `test_prove_add_comm`, `test_theorem_certified_after_check`, `test_check_idempotent`, `test_full_abs_nonneg`, `test_proof_decorator_style` | Quantified integer equality and ring derivations. Each recheck now runs the verifier. |
| `test_prove_linarith` | Quantifiers, inequalities, and linear inequality automation. |
| `test_check_returns_theorem` | Quantified equality. The portable success test exercises the return value. |
| `test_full_double_proof` | Transparent definitions, quantified equality, and ring derivations. |
| `test_ground_proof` | Exact integer computation and equality. |
| `test_builtins_are_axiom_objects` | Python declarations are still axiom objects. The legacy assertion treated a declaration's flag as certification. A future checker-owned core law can justify a checked use. |

The portable rules now cover symbols, implication introduction, local
hypotheses, conjunction introduction and projections, custom axioms, and
checked lemma references. Other logical rules, definitions and conversion,
quantifiers, arithmetic and checker-owned integer laws remain milestone work.
