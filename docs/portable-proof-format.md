# Portable proof format, version 1

A `.logos` file is a UTF-8 JSON object. All fields shown below are required
unless marked optional. Unknown fields, versions and tags are rejected.
`logos commands --json` includes the format and result contract in the
installed checker. Earlier v1 files with empty dependency lists still replay.

| Object | Fields |
| --- | --- |
| Proof file | `format: "logos-proof-v1"`, `theory: "logos-core-v1"`, optional `name: string or null`, `declarations: [Declaration]`, optional `functions: [Function]`, optional `programs: [Program]`, `custom_axioms: [CustomAxiom]`, `lemmas: [Lemma]`, `target: Expression`, `proof: Evidence` |
| Declaration | `id: string`, `name: string` (display label), `sort: "prop" \| "int" \| "seq"` |
| Function | `id: string`, `name: string`, `params: [Sort]`, `result: Sort`, optional `body: Expression`, optional `recursor: {base: Expression, step: Expression}` |
| CustomAxiom | `id: string`, `statement: Expression` |
| Lemma | `id: string`, `statement: Expression`, `proof: Evidence` |

IDs are nonempty strings and unique across all bundle lists. Checker-owned
core-law IDs are reserved. Display labels may repeat. A symbol declaration
alone assumes no truth. Transparent function bodies can reference earlier
function declarations and take the declared parameters as bound variables.
Omitting a body declares an opaque function. A `recursor` declares a
primitive-recursive function instead; it must take one integer, return an
integer, and may not also have a body.

| Expression tag | Other fields |
| --- | --- |
| `symbol` | `id` of a symbol declaration |
| `bound` | Zero-based `index` counting outward from the nearest binder. In a function body, the last parameter has index 0 at the root. |
| `int` | `value` as a signed decimal string |
| `add`, `sub`, `mul` | Integer `left` and `right` |
| `neg` | Integer `operand` |
| `pow` | Integer `base` and natural literal `exponent` |
| `eq` | `left` and `right` of the same sort |
| `le` | Non-strict integer order over `left` and `right`, both of sort `int` |
| `lt` | Strict integer order over `left` and `right`, both of sort `int` |
| `div` | Integer `left` divided by nonzero integer `right` |
| `len` | Sequence `seq` of sort `seq` |
| `nth` | Sequence `seq` and integer `index` |
| `sorted` | Sequence `seq`; the checker-owned sortedness predicate |
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
| `recursor_base` | Function `id`. Derives `f(0) = base` for a declared primitive-recursive function. |
| `recursor_step` | Function `id`, integer `argument`, and a `proof` of `not (argument < 0)`. Derives `f(argument + 1) = step(argument, f(argument))`. |
| `refl` | A well-sorted `term`. Derives equality of that term with itself. |
| `symm` | Equality `proof`. |
| `trans` | Equality proofs `left` and `right` with convertible middle expressions. |
| `congr` | Equality `proof` and expression `context` with an extra innermost binder of the operands' sort. Substitutes each operand into the context. |
| `core_law` | Law `id` and ordered typed substitution `args`. |
| `linear` | Order `conclusion` and `terms: [{binder, coefficient}]`. Non-negative rational coefficients combine inequality hypotheses with the negated conclusion; equality hypotheses may carry either sign. The combination must cancel every atom and leave falsehood. |
| `have` | `binder`, `statement`, its `proof`, and a `body` checked with the statement as a local hypothesis. |
| `program_ref` | Program `id`. Recomputes every program obligation, checks the supplied proof for each, and derives the program contract. |
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

Core order and sequence laws are checker-owned propositions. They use the
same `core_law` evidence tag and an ordered typed substitution; only the
conclusion is a proposition rather than an equality.

| Core law | Checker-owned proposition |
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
| `lt_decidable` | `a < b ∨ ¬(a < b)` |
| `le_refl`, `le_trans`, `le_antisymm` | Non-strict order is reflexive, transitive and antisymmetric. |
| `le_lt_trans`, `lt_le_trans`, `lt_succ_le`, `lt_add_one_le` | Mixed strict/non-strict transport and integer successor facts. |
| `le_total`, `lt_trichotomy`, `not_lt_le` | Integer totality. |
| `lt_to_le`, `eq_symm`, `le_add` | Basic order and equality consequences. |
| `half_lower`, `half_upper` | `0 <= a`, `a < b` give `a <= (a+b)//2 < b`. |
| `mul_nonneg`, `div_nonneg` | A product of non-negative integers is non-negative, and `0 <= a`, `0 < b` give `0 <= a // b`. |
| `div_lt` | `0 < a`, `1 < b` give `a // b < a`. |
| `length_nonneg` | `0 <= len(xs)`. |
| `sorted_elim` | Sorted `xs` orders every in-range pair `i <= j` with `xs[i] <= xs[j]`. |
| `sorted_lower`, `sorted_upper` | An element on the low side of a smaller in-range element is smaller than the target, and symmetrically on the high side. |
| `sorted_gap` | When the target is below every element left of `low`, above every element right of `high`, and `low >= high`, no in-range element equals the target. |

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

### Soundness of primitive recursion

A `recursor` declaration defines one integer function of one integer
argument on the natural numbers by `f(0) = base` and
`f(k + 1) = step(k, f(k))`. `base` is a closed integer term. `step` is an
integer term with two binders: the argument `k` (outer) and the previous
value `f(k)` (inner). The checker rejects a declaration whose step calls the
function anywhere except at that argument. That syntactic restriction is
what makes the schema a primitive recursion: every recursive call is on the
predecessor of a nonnegative argument, so the equations determine a unique
total function on the naturals. A function is either transparent with a
body or recursive with a recursor, never both. Recursive functions stay
opaque to conversion; proofs use `recursor_base` and `recursor_step`, and
the step rule requires a checked proof that the argument is nonnegative.

### Soundness of the order and sequence laws

`lt` and `le` are the usual integer orders. Each integer law is true for every
integer substitution. `half_lower` and `half_upper` are floor division facts:
for `0 <= a < b`, `a <= (a+b)//2` because `2a <= a+b`, and `(a+b)//2 < b`
because `a+b < 2b`. `length_nonneg` is the range of a finite sequence length.

`mul_nonneg`, `div_nonneg` and `div_lt` are floor-division facts.
For `0 <= a` and `0 <= b`, the product is non-negative. For `0 <= a` and
`b > 0`, the quotient is non-negative. For `a > 0` and `b > 1`, the quotient
is at most `a // 2`, hence strictly below `a`. The checker recomputes each
instance from the law ID and its two integer arguments.

`sorted(xs)` means `xs[i] <= xs[j]` for every `0 <= i <= j < len(xs)`.
`sorted_elim` is that definition. `sorted_lower` follows by transitivity:
`xs[i] <= xs[mid] < target`. `sorted_upper` follows from
`target < xs[mid] <= xs[i]`. `sorted_gap` splits on whether an index is below
`low` or at least `high`; because `low >= high`, every in-range index falls on
one side, where the target is respectively smaller or larger, so it cannot
equal the target. None of these laws mentions a particular search algorithm.

### Soundness of linear certificates

A `linear` term is an exact rational Farkas certificate. An inequality
hypothesis may only receive a non-negative coefficient; an equality is zero
and may be multiplied by either sign. Combining the indicated hypotheses with
the negated conclusion cancels every atom and leaves a false constant relation
(`0 <= c` with `c > 0`, or `0 < c` with `c >= 0`). Every integer solution is a
rational solution, so the contradiction over the rationals excludes all
integer assignments. The checker parses coefficients exactly and never trusts
the tactic that produced them.


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
- `lt_decidable` states that a strict integer comparison holds or does not.
  It is constructively justified: integer terms are compared by a terminating
  computation. The rule exposes that computation's two outcomes as a checked
  disjunction. Double-negation elimination for `<` follows by disjunction
  elimination. The earlier `lt_dne` law states that consequence directly and
  remains available for proofs written against it.

The checker verifies the law ID, the arity and that every argument has sort
`int`, then builds exactly the proposition above. It never trusts a tactic.
There is no order elimination or decision rule: any other order fact must
come from one of these laws, equality rewriting, or an explicit assumption.
The complement of `x < y` is encoded as `not` of the same `lt` proposition,
so equality and `y < x` both satisfy the complement used by an else branch.

The checker rejects inputs beyond its replay resource limits, including
proof files over 8 MiB and integer computations over 65,536 bits. A limit
error is a failed replay. Integer results are exact within the limits.

### Executable programs

A `Program` describes one source-bound executable function. Expressions use
declaration IDs for its parameters, locals, ghost variant variable and result.
Its `body` is a list of `assign`, `if`, `while`, `call` and `return`
statements. A `while` carries its `invariant` and `variant`, plus optional
`invariants: [{name, proposition}]` and `decreases_name`. A program may also
carry `requires_clauses` and `ensures_clauses` in the same named form, and a
`calls` table.

Named clauses are labels over the proposition they denote, not extra axioms.
When `requires_clauses` is non-empty, the checker recomputes their
right-associated conjunction and requires it to equal `requires` exactly. The
same rule applies to `ensures_clauses` and to a loop's `invariants` against its
`invariant`. A missing, reordered or forged label therefore fails closed.

`program_ref` recomputes these closed obligations and requires exactly one
checked proof for each ID:

- `main`: the precondition implies the weakest precondition of the body and
  the postcondition;
- `loopN.preserve` (or `loopN.preserve.CLAUSE` for each named invariant): the
  conjoined invariant and guard imply the body's weakest precondition of the
  invariant (or of that clause);
- `loopN.exit`: invariant and negated guard imply the continuation;
- `loopN.variant_nonnegative` (suffix `.NAME` when the variant is named):
  invariant implies `0 <= variant`;
- `loopN.variant_decreases` (same suffix): with the ghost equal to the old
  variant, invariant and guard imply the body either leaves the guard or
  strictly decreases the variant;
- `callK.requires` (or `callK.requires.CLAUSE`): the path condition implies the
  callee's precondition with the call's actual arguments substituted for its
  formal parameters;
- `readN`: every evaluated `nth` index is inside `[0, len(seq))` on its path.

The function declaration used by a program must be opaque, so the program is
its only definition. The contract is
`pre -> (result = f(params) -> post)`.

#### Checked calls

A `call` statement names a call-site ID and a target local. Its `args` are
expressions in the caller's scope. The program's `calls` table maps the ID to a
callee program `id`, the source line, and the callee's `requires`, `ensures`
and named clauses, all written over the callee's formal symbols. The checker:

1. verifies every program in the bundle, callees before callers, from a
   topological order of the `calls` graph; a self-call or any cycle is
   rejected, so recursion and mutual recursion are outside the fragment;
2. rejects an unknown, missing or duplicate callee program ID, a call-site ID
   with no call statement, a call statement with no call site, an arity
   mismatch, or a target that is not a declared local;
3. recomputes the callee's contract from the callee program and requires the
   call-site copy to equal it exactly, including the named clauses;
4. substitutes the actual arguments for the callee's formals and the
   callee's result for `App(callee, actuals)` in the weakest-precondition rule
   `R[a] and (E[a, App] -> Q[target := App])`, and adds the per-clause
   `callK.requires` obligations under the path condition.

The callee's postcondition is used only after the callee program's obligations
have been checked in the same artifact. A caller cannot introduce a callee by
naming an opaque function: without a matching verified program, the call site
is rejected. The artifact is self-contained; the Rust checker verifies the
program identities and contracts it finds there, not the Python module they
were extracted from.

#### Trust boundary and restrictions

The Python decorators translate the module source and propose clauses, programs
and proof terms. The Rust checker trusts none of those proposals: it
recomputes every condition from the program bytes and checks every proof term
with the core rules. The source binding is Python's responsibility. On every
`check`, `inspect` and `export` the authoring layer re-reads the defining
module, recompiles it, compares the imported code object and source segment
with the declaration, re-evaluates every clause, and revisits every transitive
callee. A changed source, clause or callee binding refuses with a redeclaration
diagnostic before any artifact is produced. The recipient of a verified `.logos`
file trusts the artifact's function definitions as given; the checker verifies
their internal consistency and every proof, and `inspect` shows the names and
clauses the author supplied.

The supported fragment is `int` and `list[int]`, straight-line assignments,
one `if`/`else` tree, one `while` loop with a final return, direct calls to
module-level functions declared with `@logos.function`, and the integer and
sequence operations described in this manual. Recursion, calls through values
or arbitrary globals, list mutation, early returns inside a loop, nested loops
and unchecked declarations used as axioms are outside it. Unsupported syntax is
refused at its source line when `@logos.function` is applied, before any clause
is declared. Contracts never run: the decorated object is the original Python
function, with no wrapper and no runtime check.
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
of the checker-owned core laws and explicit equality and congruence steps. Distinct Python symbol
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
both belong to that path. The loop fragment adds checked linear certificates,
`<=`, and sequence programs; the legacy `linarith` tactic remains outside the
checked fragment.

The sequence and program slice adds finite integer sequences, sortedness,
checked linear arithmetic, `<=`, and executable loop programs with
`program_ref`. It proves the source-bound binary search contract over every
sorted sequence and integer target, including the empty sequence, duplicates
and absence. Legacy tests remain in the suite; the binary search example and
its mutation tests are new.

| Remaining legacy test | Required work |
| --- | --- |
| `test_prove_linarith` | Inequalities and linear inequality automation. |
| `test_builtins_are_axiom_objects` | The legacy assertion treats the flag on an author-declared axiom as certification. The checked core laws are selected by theory ID and instantiated by the verifier. |

The portable checker also supports conjunction, disjunction, negation,
falsehood, implication, local hypotheses, checked definitions, checked
dependencies, existential introduction and existential elimination with a
fresh eigenvariable. The `exists_elim` rule and its soundness argument are
described above. Other theories remain milestone work.

The core-law inventory printed by `logos commands --json` is the published
list. It is compared with the checker table, this manual and the Python schema
by tests, so a law cannot be accepted by the verifier and omitted from the
inventory. Adding a law ID is additive inside `logos-proof-v1`: an older file
does not mention the new ID and still replays with the same digest. Changing a
law's statement or the meaning of an expression tag requires a new theory or
format ID.
