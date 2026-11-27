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
| `lt` | Strict integer order over `left` and `right`, both of sort `int` |
| `and`, `or`, `implies` | Propositions `left` and `right` |
| `not` | Proposition `operand` |
| `false` | No fields. The proposition falsehood (⊥). |
| `forall`, `exists` | Display `name`, binder `sort`, and proposition `body` |
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
| `exists_intro` | Existential `goal`, same-sort `witness`, and `proof` of the predicate after capture-avoiding substitution. The witness and proof use the surrounding scope. |
| `exists_elim` | Proof of an existential, display `name`, hypothesis `binder`, and `body`. The body runs under a fresh variable and the assumption that the predicate holds for it. The conclusion must not mention the eigenvariable. |
| `eq_subst` | Proof of an equality, a proposition `context` with one extra innermost integer binder, and `proof` of the instance at the equality’s left side. Derives the instance at its right side. |
| `induction` | Integer `bound`, display `name`, a proposition `predicate` with one extra innermost integer binder, a `base` proof of the predicate at the bound, and a `step` proof of `forall k, k >= bound -> P(k) -> P(k + 1)`. Derives `forall n, n >= bound -> P(n)`. |
| `least` | Integer `bound`, display `name`, a proposition `predicate` with one extra innermost integer binder, and a `nonempty` proof of `exists m, m >= bound and P(m)`. Derives a least such `m` with its minimality clause. |
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

Ten further core laws are checker-owned propositions over integers. They
use the same `core_law` evidence tag and the same ordered integer
substitution; only the conclusion is a proposition rather than an equality.

| Core law | Checker-owned proposition over integers |
| --- | --- |
| `lt_irrefl` | `¬(a < a)` |
| `lt_trans` | `a < b → (b < c → a < c)` |
| `lt_add` | `a < b → a + c < b + c` |
| `lt_neq` | `a < b → ¬(a = b)` |
| `mul_pos` | `0 < a → (0 < b → 0 < a · b)` |
| `mul_eq_one` | `a · b = 1 → (a = 1 ∨ a = −1)` |
| `lt_succ_fwd` | `a < b + 1 → ¬(b < a)` |
| `lt_succ_rev` | `¬(b < a) → a < b + 1` |
| `eq_of_not_lt_not_lt` | `¬(a < b) → (¬(b < a) → a = b)` |
| `lt_dne` | `¬¬(a < b) → a < b` |

### Soundness of existential elimination and equality substitution

`exists_elim` is the usual natural-deduction rule. Once a proof of
`∃x.P(x)` has been checked, the body may use a fresh variable `c` and the
assumption `P(c)`. The checker lowers the body’s conclusion only when it
contains no occurrence of the innermost bound variable, so the conclusion
cannot depend on the chosen witness. The assumption is discharged at the
rule, and the eigenvariable is removed from the returned scope.

`eq_subst` is Leibniz elimination. Given checked `a = b` and the instance
`P(a)` of a proposition template, it returns `P(b)`. The checker compares
the supplied premise with `P(a)` under the ordinary conversion and
instantiates the template at the equality’s two sides. No rewriting
direction is assumed: the premise must establish the left instance.

### Soundness of induction and least elements

`induction` is ordinary induction on the integers at or above `bound`.
The checker verifies the base instance `P(bound)` and the step
`∀k. k ≥ bound → P(k) → P(k + 1)`, then builds
`∀n. n ≥ bound → P(n)`. This is the standard induction principle for the
well-ordered set `{bound, bound + 1, …}`. It is an arithmetic principle,
not a schematic shortcut: the predicate is an explicit proposition template,
the two premises are checked evidence, and the conclusion is built from the
same template.

`least` is the well-ordering principle for the same set. From a checked
witness of `∃m. m ≥ bound ∧ P(m)`, it builds the least such `m` together
with `∀k. k ≥ bound → k < m → ¬P(k)`. If a smaller admissible witness
existed, it would contradict minimality; the conclusion follows from the
order of the integers. Both rules are general over the predicate and the
bound. Neither introduces a custom axiom into a judgment.

### Soundness of the order laws

`lt` is interpreted as the usual strict order on the mathematical integers.
Each law is true for every substitution of integer terms, so replaying a
law instance is sound without any decision procedure:

- `lt_irrefl` states that no integer is less than itself.
- `lt_trans` composes two inequalities with a shared middle term.
- `lt_add` adds the same term to both sides; the converse also holds in the
  integers, but the fragment exposes only the direction a proof needs.
- `lt_neq` follows because `a < b` and `a = b` cannot both hold.
- `mul_pos` says the product of two positive integers is positive.
- `mul_eq_one` lists the units of the integers: a product equal to one has
  a first factor equal to one or minus one.
- `lt_succ_fwd` and `lt_succ_rev` are the two directions of
  `a < b + 1 ↔ ¬(b < a)`, the successor characterization of the integer
  order.
- `eq_of_not_lt_not_lt` is trichotomy in the form needed for case analysis:
  two integers that are not strictly ordered either way are equal.
- `lt_dne` is double-negation elimination for a strict integer comparison.
  It is constructively justified because `a < b` is decidable: either it
  holds or it does not, so stability follows by case analysis. The checker
  owns the case analysis rather than a general classical axiom.

The checker verifies the law ID, the arity and that every argument has sort
`int`, then builds exactly the proposition above. It never trusts a tactic.
There is no order elimination or decision rule: any other order fact must
come from one of these laws, equality rewriting, or an explicit assumption.
The complement of `x < y` is encoded as `not` of the same `lt` proposition,
so equality and `y < x` both satisfy the complement used by an else branch.

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
- For `exists_intro`, `substitutions` holds the witness in the step’s
  variable scope, `binder_sort` gives its required sort, and `premises`
  links to the proof that establishes the instantiated predicate. Markdown
  inspection shows the witness and refers to that proof by its step number.
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
construction budget. Use `timeout=None` for an unbounded search. Search and
evidence size can grow exponentially with inhabitants. Adding an inhabitant or
an utterance invalidates the previous result.

`puzzle.export_proof(path)` sends the generated evidence for a unique result
to the Rust checker and writes the verified bytes. The proof derives the
assignment from explicit exhaustivity, exclusivity and utterance premises.
Strict replay reports zero custom axioms because these premises are local and
discharged. Model witnesses come from Python search. The checker verifies the
conditional derivation, while model existence is a separate claim. The checker
applies its existing proof size and nesting limits when exporting or replaying.

### Describe a claim before proving it

After emitting the examples, run `python guide_knights_knaves.py` with no
arguments. The preview needs only the Python wheel. It prints the reported
utterance and a proposed conclusion.

```text
A says, “A is a knave and B is a knave.”
Proposed conclusion — A is a knave.
```

`puzzle.describe(claim)` returns one English sentence for claim content.
The caller supplies wording such as “A says” or “Proposed conclusion.”

```python
from logos.domains.logic_puzzles import KnightsKnaves

puzzle = KnightsKnaves()
a, b = puzzle.entity("A"), puzzle.entity("B")
print(puzzle.describe(a.is_knave() & b.is_knight()))     # A is a knave and B is a knight.
print(puzzle.describe(~(a.is_knave() & b.is_knave())))  # A and B are not both knaves.
print(puzzle.describe(~(a.is_knave() | b.is_knave())))  # Neither A nor B is a knave.
print(puzzle.describe(~a.is_knave() & ~b.is_knave()))    # Neither A nor B is a knave.
```

The renderer uses inclusive “or” and groups nested clauses with parentheses.
Labels such as `A` and `B2` appear as written. Other names are quoted with
JSON string escaping. It accepts the same expressions as the puzzle solver and
raises `ValueError` for foreign atoms and unsupported expressions.

### Guide a proof of a chosen claim

Run `python guide_knights_knaves.py guided.logos` after emitting the examples,
then `logos check --strict guided.logos`. The [guided script](../checker/examples/guide_knights_knaves.py)
uses the same puzzle and checks that A is a knave given the role and utterance
premises. The exported implication retains those premises.

```python
from logos import export_proof, tactics as t

proof = puzzle.prove(a.is_knave(), by=[
    puzzle.cases_on_role(a),
    [puzzle.use_statements(), puzzle.auto()],
    [t.assumption()],
])
export_proof(proof, "guided.logos")
```

`prove` introduces the puzzle premises and returns a Rust-checked theorem.
`cases_on_role(a)` opens a knight branch followed by a knave branch.
The nested lists supply the tactics for each branch. `use_statements()`
applies the utterance implications for known speakers and puts the resulting
facts in scope. `puzzle.auto()` runs finite reasoning on the current goal
and its local hypotheses. You can set its budget with `puzzle.auto(timeout=seconds)`.

Replace `puzzle.auto()` in the knight branch with `t.assumption()` to see
how an unsuccessful tactic reports the active branch:

```text
Open goal: A is a knave
Local hypotheses:
  role_of_A: A is a knight
  statement_1_by_A: (A is a knave) and (B is a knave)
```

When finite reasoning finds an assignment that satisfies the premises and
makes the goal false, the diagnostic includes that counterexample. Guided
proofs can establish claims shared by every solution even if the overall
assignment is underdetermined.

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

The order slice adds `lt` and four core laws for strict integer order, plus
source-bound contracts whose guard is `<`. Its else path uses the
propositional complement `~(x < y)`, so the equality boundary and `y < x`
both belong to that path. General inequality automation (`linarith`) and
`<=`, `>`, `>=` remain milestone work.

| Remaining legacy test | Required work |
| --- | --- |
| `test_prove_linarith` | Inequalities and linear inequality automation. |
| `test_builtins_are_axiom_objects` | The legacy assertion treats the flag on an author-declared axiom as certification. The checked core laws are selected by theory ID and instantiated by the verifier. |

The portable checker also supports conjunction, disjunction, negation,
falsehood, implication, local hypotheses, and checked dependencies.
The checker supports existential introduction with checked witnesses.
Existential elimination and other domains remain milestone work.
