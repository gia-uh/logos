# Portable proof format, version 1

A `.logos` file is a UTF-8 JSON object. All fields shown below are required
unless marked optional. Unknown fields, versions and tags are rejected.

| Object | Fields |
| --- | --- |
| Proof file | `format: "logos-proof-v1"`, `theory: "logos-core-v1"`, optional `name: string or null` (author label), `declarations: [Declaration]`, `custom_axioms: []`, `lemmas: []`, `target: Proposition`, `proof: Evidence` |
| Declaration | `id: string`, `name: string` (display label), `sort: "prop" \| "int"` |
| Proposition | `{"tag":"symbol","id":string}` or `{"tag":"and"\|"implies","left":Proposition,"right":Proposition}` |
| Evidence | `{"tag":"implies_intro","binder":string,"premise":Proposition,"body":Evidence}`, `{"tag":"hyp_ref","binder":string}` or `{"tag":"and_elim_l"\|"and_elim_r","proof":Evidence}` |

IDs and binder names are nonempty strings. Declaration IDs must be unique;
display labels need not be unique. A proposition reference must resolve to a
declaration of sort `prop`. The `int` sort can be declared but has no term
constructors in this fragment. References use IDs. No declarations assume truth.

The initial local scope is empty. Implication introduction checks the body
with its premise bound to the given binder, then discharges the binding.
Within nested introductions, the nearest enclosing binding of a name wins.
Hypothesis lookup resolves only in this scope. Both projections require a
checked conjunction. The derived conclusion must equal the target as syntax
over declaration IDs. The initial fragment admits no external evidence,
definitions, axioms or lemma dependencies.

The checked judgment includes the derived statement tree, a display string,
theory, and an empty list of custom axioms. Inspection adds ordered
applications of the rules with structural path references rooted at
`proof`. A binder introduction has an `.assumption` path and a `.body`
child. A projection has a `.proof` child. The author label is unverified
metadata. A SHA-256 digest identifies the exact verified file bytes, whereas
statement and step equality compare the checked syntax and references.

See `checker/tests/fixtures/portable/authorization.logos` and
`checker/tests/fixtures/portable/wrong-projection.logos` for the reference files.
The second changes only the projection tag and derives the other conclusion.

## Authoring and certification

Run `logos example` to extract the prebuilt file and the runnable Python
source. The source uses two `logos.var(name, bool)` objects as proposition
symbols and a zero-argument `@logos.theorem`. Its tactics introduce a named
premise and return `AndElimR(HypRef("h"))` from a user-written tactic.
Distinct Python symbol objects become separate declaration IDs even when
their names match. The declaration context is available as
`proof.declarations`, initialized with the statement's free symbols in order
of first occurrence in this fragment.

`logos.check` runs the tactics, encodes the resulting evidence and invokes
`logos check --json --deny-custom-axioms -` after discovering the installed
checker and its protocol on PATH. The named, anonymous, and automatic entry
points all call the same verifier. A successful check attaches a
`ProofReceipt` to the proof. It holds the immutable bytes and the digest
returned by the checker. `proof.certified` reflects whether the current
statement, declaration context, and attached and generated evidence still
match that receipt. `logos.export_proof(proof, path)` writes those exact
bytes. Python raises `LogosProofError` without certifying if the checker is
missing, a construct is unsupported, or verification fails.

## Migration status

The baseline Python suite had 91 passing tests. Existing positive
certification assertions are retained as strict expected failures for the
following dependencies and behavior:

| Legacy tests | Checker work still required |
| --- | --- |
| `test_prove_add_comm`, `test_theorem_certified_after_check`, `test_check_idempotent`, `test_full_abs_nonneg`, `test_proof_decorator_style` | Quantified integer equality and ring derivations. Each recheck now runs the verifier. |
| `test_prove_linarith` | Quantifiers, inequalities, and linear inequality automation. |
| `test_check_returns_theorem` | Quantified equality. The portable success test exercises the return value. |
| `test_full_double_proof` | Transparent definitions, quantified equality, and ring derivations. |
| `test_ground_proof` | Exact integer computation and equality. |
| `test_builtins_are_axiom_objects` | Python declarations are still axiom objects. The legacy assertion treated a declaration's flag as certification. A future checker-owned core law can justify a checked use. |

Legacy tactics can still produce terms for authoring, including axiom terms.
The portable exporter only encodes the rules above and rejects every
external dependency. Full core logic, conversion, axioms, checked lemmas,
and ring derivations are milestone work. Keep this branch as the integration
destination until the intended public release scope passes.
