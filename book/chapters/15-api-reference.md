---
theme: book
title: Public API Reference
stem: api-reference
---

# Public API Reference

Use this chapter to find the supported import, call signature, and result of a
Logos operation. It covers exports from `logos` and `logos.tactics` plus the
documented proof-context and tactic-extension interfaces. Class members are
called on the returned object or on the context provided by Logos. Signatures
come from Python source, so a missing type annotation has the same meaning
here as in Python. Implementation inventory lives in
[the maintainer file](https://github.com/gia-uh/logos/blob/main/book/maintenance/api-inventory.md).

- [Existential lookup](#existential-lookup)
- [Expressions](#expressions)
- [Theorems and evidence](#theorems-and-evidence)
- [Definitions](#definitions)
- [Program contracts](#program-contracts)
- [Proof context](#proof-context)
- [Tactics](#tactics)
- [Tactic extensions](#tactic-extensions)

## Existential lookup

| What you have | Operation | Result |
| --- | --- | --- |
| A predicate and a type | [`logos.exists`](#logosexists) | The symbolic statement ∃x. P(x). |
| An existential tactic goal and a candidate value | [`logos.tactics.witness`](#logostacticswitness) | A tactic that replaces ∃x. P(x) with P(value). |
| A current existential goal and evidence for the candidate | [`ProofContext.witness`](#proofcontextwitness) | Proof term to return from the proof function. |
| An existential statement you want as an intermediate fact and evidence for the candidate | [`ProofContext.exists`](#proofcontextexists) | A fact for ∃x. P(x). The current goal stays open. |
| An existential fact you want to use | [`ProofContext.obtain`](#proofcontextobtain) | A fresh local symbol and a fact about it. |

### Complete existential examples

To show that an integer greater than four exists, choose five. In a tactic
proof, `witness` leaves `4 < 5`, the same comparison as `5 > 4`. Prove that
comparison as a separate lemma and use `apply` to close the subgoal. Write
`lit(4) < x` so the symbolic comparison has the same shape as the lemma.

```python {run}
from logos import Int, check, exists, lit, prove, theorem
from logos.tactics import apply, witness

@theorem
def five_above_four():
    return lit(4) < 5

@five_above_four.proof
def prove_five_above_four(p):
    return p.linear(lit(4) < 5)

check(five_above_four)
statement = exists(Int, lambda x: lit(4) < x)
assert check(prove(statement, [witness(lit(5)), apply(five_above_four)])).certified
print("Tactic witness certified")
```

In a proof function, establish `5 > 4` first. If the existential is the
current goal, return `p.witness`. When the existential is needed as one part of
a conjunction, build it with `p.exists` and combine the resulting facts.

```python {run}
from logos import Int, check, exists, lit, theorem

@theorem
def above_four():
    return exists(Int, lambda x: x > 4)

@above_four.proof
def prove_above_four(p):
    return p.witness(5, p.linear(lit(5) > 4))

@theorem
def two_claims():
    return exists(Int, lambda x: x > 4) & (lit(4) < 6)

@two_claims.proof
def prove_two_claims(p):
    above_four = p.exists(
        exists(Int, lambda x: x > 4), 5, p.linear(lit(5) > 4)
    )
    return p.and_intro(above_four, p.linear(lit(4) < 6))

assert check(above_four).certified
assert check(two_claims).certified
print("Proof-context witness and existential fact certified")
```

See [Witnesses and Their Scope](witnesses-and-their-scope.html) for a complete
proof that opens an existential with `p.obtain`.

## Expressions

[Complete checked example](quick-start.html)

### logos.Int

Import with `from logos import Int`.

Alias for Python `int`, the integer sort in portable statements.

### logos.Prop

Import with `from logos import Prop`.

Alias for Python `bool`, the proposition sort in portable statements.

### logos.Expr

Import with `from logos import Expr`.

Base class for all expression nodes. Operators build expression trees.

### logos.Var constructor

Import with `from logos import Var`.

`Var(name: str, type: type)`

Construct a symbolic variable. Its identity distinguishes it from other variables with the same name.

### logos.Lit constructor

Import with `from logos import Lit`.

`Lit(value: Any)`

Construct a symbolic literal from a Python value. Use integers or Booleans for portable proofs.

### logos.Forall constructor

Import with `from logos import Forall`.

`Forall(*args: Var | Expr) -> Expr`

Forall(x, y, body) → nested ForallNode(x, ForallNode(y, body)).

### logos.Exists constructor

Import with `from logos import Exists`.

`Exists(var: Var, body: Expr) -> Expr`

Bind one symbolic variable in the supplied predicate expression. Nest calls for multiple variables.

### logos.Implies

Import with `from logos import Implies`.

`Implies(antecedent: Expr, consequent: Expr)`

Build the symbolic implication from its antecedent and consequent, as with `A >> B`.

### logos.var

Import with `from logos import var`.

`var(name: str, type_: type) -> Var`

Return a fresh symbolic variable of the supplied type. Reuse the returned object to refer to the same symbol.

### logos.vars

Import with `from logos import vars`.

`vars(names: str, type_: type) -> tuple[Var, ...]`

Split whitespace-separated names and return one fresh symbolic variable per name.

### logos.lit

Import with `from logos import lit`.

`lit(value) -> Lit`

Lift a Python value into a symbolic literal. Use an integer or Boolean for portable proofs.

### logos.forall

Import with `from logos import forall`.

`forall(type_: type, *rest) -> Expr`

Pass one sort per parameter followed by a callable that returns a symbolic predicate. Return the universally quantified expression. A noncallable predicate argument is rejected.

### logos.exists

Import with `from logos import exists`.

`exists(type_: type, fn) -> Expr`

Pass a sort and a unary callable returning a symbolic predicate. Return an existential expression. The callable is evaluated on a fresh symbolic variable.

### logos.chain

Import with `from logos import chain`.

`chain(*props: Expr) -> Expr`

Build a right-associated implication from one or more propositions. `chain(A, B, C)` builds `A >> (B >> C)`. An empty chain has no conclusion and raises `IndexError`.

### logos.format_expr

Import with `from logos import format_expr`.

`format_expr(expr: Expr) -> str`

Render an expression the way a reader writes it in the book.

### logos.Seq

Import with `from logos import Seq`.

The sort marker for a sequence of integers in program contracts.

### logos.seq_var

Import with `from logos import seq_var`.

`seq_var(name: str) -> Var`

Create a fresh symbolic variable of sequence sort.

### logos.length

Import with `from logos import length`.

`length(xs: Expr) -> Len`

Build the symbolic length of a sequence.

### logos.nth

Import with `from logos import nth`.

`nth(xs: Expr, index) -> Nth`

Build a symbolic zero-based element access. Program proofs must establish both index bounds.

### logos.sorted

Import with `from logos import sorted`.

`sorted(xs: Expr) -> Sorted`

The checker-owned sortedness predicate over a sequence.

### logos.absent

Import with `from logos import absent`.

`absent(xs: Expr, target: Expr) -> Expr`

Every in-range index holds something other than `target`.

### logos.occurrence

Import with `from logos import occurrence`.

`occurrence(xs: Expr, target: Expr) -> Expr`

Some in-range index holds `target`.

## Theorems and evidence

[Complete checked example](writing-your-first-proof.html)

### logos.theorem

Import with `from logos import theorem`.

`theorem(fn=None, *, about=None)`

@logos.theorem decorator — creates a Theorem object (no proof yet).

### logos.axiom

Import with `from logos import axiom`.

`axiom(fn_or_stmt)`

@logos.axiom decorator or logos.axiom(expr) — creates a trusted Axiom.

### logos.prove

Import with `from logos import prove`.

`prove(thm_or_stmt, tactics=None, *, hints=None, depth: int=5, timeout: float | None=None)`

With an expression and explicit tactics, return an anonymous proof for `check` to certify. With a `Theorem`, run bounded automatic search using `hints`, `depth` and `timeout` and return the certified theorem or raise `LogosProofError`.

### logos.check

Import with `from logos import check`.

`check(thm)`

Run the proof and certify its evidence with the Rust checker. Return the theorem, anonymous proof, or checked Python function. Missing proofs, unclosed goals and rejected evidence raise `LogosProofError`.

### logos.Theorem constructor

Import with `from logos import Theorem`.

`Theorem(statement: Expr, *, name: str='', declarations=None)`

A statement with tactics that can be verified by logos.check().

### Theorem.proof

`proof(*args)` on `Theorem`.

Attach tactics as positional arguments or as a list, and return the theorem. As a decorator, accept a zero-argument tactic-producing function or a proof function whose first argument is `p`, followed by the quantified theorem parameters. Replacing the proof clears its receipt.

### Theorem.check

`check()` on `Theorem`.

Check this theorem now and certify its actual evidence.

### Theorem.inspect

`inspect() -> str` on `Theorem`.

Return checker-rendered Markdown for a currently certified proof. A missing or stale receipt raises `LogosProofError`.

### Theorem.receipt

`receipt` on `Theorem`.

The current `ProofReceipt`, or `None` before certification or after the proof changes.

### Theorem.certified

`certified` on `Theorem`.

Whether the theorem has a current checker receipt.

### logos.Axiom constructor

Import with `from logos import Axiom`.

`Axiom(statement: Expr, *, name: str='')`

An author-declared assumption.

### logos.ProofReceipt

Import with `from logos import ProofReceipt`.

A verification result for the exact immutable artifact bytes.

### logos.LogosProofError

Import with `from logos import LogosProofError`.

`LogosProofError(message='', *, details=None)`

A rejected proof.

### logos.export_proof

Import with `from logos import export_proof`.

`export_proof(theorem, path: str | Path) -> ProofReceipt`

Write the current checked artifact for a named or anonymous proof.

## Definitions

[Complete checked example](definitions-that-unfold-lemmas-you-can-name.html)

### logos.define

Import with `from logos import define`.

`define(fn: Callable) -> Function`

@logos.define decorator — creates a Function object.

### logos.definition

Import with `from logos import definition`.

`definition(fn: Callable) -> Function`

The book spelling of :func:`define` for transparent propositions.

### logos.recursor

Import with `from logos import recursor`.

`recursor(name: str, base, step: Callable[..., Expr], *, parameters: Mapping[str, type | SeqType] | None=None) -> Function`

Declare a primitive-recursive integer function on the naturals.

### logos.extern

Import with `from logos import extern`.

`extern(name: str, arg_types: list[type], ret_type: type) -> Callable`

Declare an external (uninterpreted) function symbol.

### logos.cases

Import with `from logos import cases`.

`cases(*branches) -> Expr`

Build a piecewise symbolic expression from condition/value pairs and a default value.

### logos.if_

Import with `from logos import if_`.

`if_(condition: Expr, then_val: Expr, else_val: Expr) -> Expr`

Build a symbolic conditional expression from a condition and its two possible values.

## Program contracts

[Complete checked example](binary-search-all-the-way-down.html)

### logos.contract

Import with `from logos import contract`.

`contract(*, ensures: Expr, requires: Expr | None=None) -> Contract`

Describe a postcondition and an optional explicit precondition.

### logos.Contract constructor

Import with `from logos import Contract`.

The two halves of a function contract, written with signature names.

### logos.LogosContractError

Import with `from logos import LogosContractError`.

A contract, or the source binding behind it, could not be established.

### logos.program_contract

Import with `from logos import program_contract`.

`program_contract(*, requires: Expr, ensures: Expr, invariant: Expr, variant: Expr) -> ProgramContract`

Build a loop contract with precondition, postcondition, invariant and decreasing integer variant.

### logos.ProgramContract

Import with `from logos import ProgramContract`.

The precondition, postcondition, invariant and variant returned by `program_contract`.

### logos.function

Import with `from logos import function`.

`function(fn)`

Decorate an ordinary Python function that uses the supported program fragment. Return the same callable with `requires`, `ensures`, `invariant` and `decreases` clause decorators and bound `check()`, `inspect()`, `export(path)` and `clauses()` methods. Unsupported source raises `LogosContractError`.

### logos.FunctionDeclaration

Import with `from logos import FunctionDeclaration`.

`FunctionDeclaration(fn)`

The source-bound declaration behind one `@logos.function`.

### FunctionDeclaration.check

`check()` on `FunctionDeclaration`.

Translate and verify the decorated function and return the original callable with a current certificate. Invalid source or proof obligations fail verification.

### FunctionDeclaration.inspect

`inspect()` on `FunctionDeclaration`.

Return checker-rendered Markdown for the current certificate. Requires current verification.

### FunctionDeclaration.export

`export(path)` on `FunctionDeclaration`.

Write the current portable artifact to `path` and return its receipt. Requires current verification.

### FunctionDeclaration.receipt

`receipt` on `FunctionDeclaration`.

The current checker receipt, or `None` before verification or after a change invalidates it.

### FunctionDeclaration.certified

`certified` on `FunctionDeclaration`.

Whether the declaration has a current checker receipt.

### FunctionDeclaration.clauses

`clauses()` on `FunctionDeclaration`.

Return a tuple of authored contract clauses in clause-kind order.

### logos.Clause

Import with `from logos import Clause`.

One named clause bound to a declarative function.

## Proof context

[Complete checked proof functions](witnesses-and-their-scope.html). For context managers, use the methods on the object they yield.

### logos.authoring.ProofContext

Import with `from logos.authoring import ProofContext`.

`ProofContext(statement: Expr, binders: tuple[Var, ...], theorem: str, fn=None)`

The `p` argument supplied to a proof function by `@theorem_name.proof`. Its goal and available facts change as you introduce assumptions and enter scopes.

### ProofContext.note

`note(text: str) -> None` on `ProofContext`.

Attach authored commentary after the most recently derived fact.

### ProofContext.assume

`assume(proposition: Expr) -> Fact` on `ProofContext`.

Introduce the antecedent of the current implication as a local fact and leave the consequent as the goal. The supplied proposition must match the antecedent.

### ProofContext.obtain

`obtain(existential: Fact) -> tuple[Var, Fact]` on `ProofContext`.

Open a fact of shape ∃x. P(x), returning a fresh local variable and a fact for its instantiated predicate. The symbol is scoped to the elimination: it cannot appear free in the conclusion.

### ProofContext.apply

`apply(lemma, *arguments) -> Fact` on `ProofContext`.

Instantiate a checked theorem (or local implication fact) step by step.

### ProofContext.and_intro

`and_intro(left: Fact, right: Fact) -> Fact` on `ProofContext`.

Combine two facts for A and B into a fact for A & B.

### ProofContext.exists

`exists(goal: Expr, value: Expr, evidence: Fact) -> Fact` on `ProofContext`.

Given ∃x. P(x), a value, and a `Fact` proving P(value), return a `Fact` for the existential without closing the current goal. A Python literal is lifted. A non-existential target reports `exists_goal`, and an out-of-scope value reports `witness_escape`. Mismatched evidence reports `evidence_mismatch`. See the [complete examples](#complete-existential-examples).

### ProofContext.subst

`subst(fact: Fact, equality: Fact) -> Fact` on `ProofContext`.

Replace one side of an equality throughout a fact.

### ProofContext.refl

`refl(expression: Expr) -> Fact` on `ProofContext`.

Return a fact proving the expression equal to itself.

### ProofContext.symm

`symm(fact: Fact) -> Fact` on `ProofContext`.

Reverse an equality fact. Other fact shapes fail.

### ProofContext.trans

`trans(left: Fact, right: Fact) -> Fact` on `ProofContext`.

Compose two equality facts at their matching middle expression. Non-equalities and mismatched middle expressions fail.

### ProofContext.not_elim

`not_elim(negation: Fact, premise: Fact) -> Fact` on `ProofContext`.

From facts for ¬P and P, return a fact for falsehood. The operands must match.

### ProofContext.ex_falso

`ex_falso(falsehood: Fact) -> Fact` on `ProofContext`.

Use a fact for falsehood to obtain a fact for the current goal. Requires an open goal.

### ProofContext.not_lt_of_lt

`not_lt_of_lt(low: Expr, high: Expr, fact: Fact) -> Fact` on `ProofContext`.

From `low < high` derive `~(high < low)` without a new axiom.

### ProofContext.order

`order(law: str, *args, using=()) -> Fact` on `ProofContext`.

Cite a core order law with explicit integer arguments and premises.

### ProofContext.linear

`linear(goal: Expr, *, using=()) -> Fact` on `ProofContext`.

Prove a linear inequality from named facts with a checked certificate.

### ProofContext.recursor_base

`recursor_base(function, *parameters) -> Fact` on `ProofContext`.

Return the defining equality of the indicated recursor at zero.

### ProofContext.recursor_step

`recursor_step(function, argument: Expr, nonnegative: Fact, *parameters) -> Fact` on `ProofContext`.

Return the defining equality at the successor of the supplied argument. Supply a fact establishing that the argument is nonnegative.

### ProofContext.rewrite

`rewrite(fact: Fact, equality: Fact) -> Fact` on `ProofContext`.

Rewrite the second argument of a transparent `divides` fact.

### ProofContext.least

`least(lower: Expr, nonempty: Fact) -> Fact` on `ProofContext`.

Apply the least-element rule to a nonempty bounded predicate.

### ProofContext.fix

`fix(name: str='x') -> '_Fixed'` on `ProofContext`.

Enter a universal goal with `with p.fix(name) as scope`. Use the fresh symbol `scope.variable` and call `scope.finish(evidence)` inside the block. Read `scope.result` afterward. Other goal shapes fail.

### ProofContext.negate

`negate(statement: Expr | None=None) -> '_Negation'` on `ProofContext`.

Enter a negation goal with its operand as a local assumption. Derive a contradiction inside the block.

### ProofContext.cases

`cases(disjunction: Fact) -> '_Cases'` on `ProofContext`.

Split a disjunction fact into two branches. Prove the same conclusion with the left alternative in one branch and the right in the other.

### ProofContext.contradict

`contradict(proposition: Expr) -> '_Contradiction'` on `ProofContext`.

Enter a branch with the given proposition assumed and derive falsehood to discharge that assumption.

### ProofContext.induction

`induction(variable: Var, lower=0, *, nonnegative: Fact | None=None) -> '_Induction'` on `ProofContext`.

Use integer induction from `lower` on the goal's variable. Prove the goal at the lower bound in `ind.base()`, and prove it at the successor from the induction hypothesis in `ind.step()`. Supply an appropriate lower-bound fact when it is not already available. See [the factorial proof](induction-that-builds-a-factorial.html).

### ProofContext.ring

`ring(equation: Expr, *, using=()) -> Fact` on `ProofContext`.

Return a fact for an integer polynomial equality, optionally using equality facts. If normalization cannot establish the identity, the proof step fails.

### ProofContext.witness

`witness(value: Expr, evidence: Fact | ProofTerm) -> ProofTerm` on `ProofContext`.

For the current goal ∃x. P(x), supply a value and evidence for P(value), then return the resulting proof term. A Python literal is lifted. Diagnostics include `witness_goal` for the wrong goal shape, `witness_escape` for an out-of-scope value, and `witness_mismatch` for a fact that proves the wrong predicate. See the [complete examples](#complete-existential-examples).

### logos.authoring.Fact

Import with `from logos.authoring import Fact`.

Evidence for a symbolic proposition in a proof context. Read `statement` for the proposition; obtain facts from context operations.

### Fact.left

`left() -> 'Fact'` on `Fact`.

Project the left conjunct from a conjunction fact.

### Fact.right

`right() -> 'Fact'` on `Fact`.

Project the right conjunct from a conjunction fact.

## Tactics

A tactic receives a `Goal` and returns evidence or subgoals with a function to compose their evidence. Supply tactics in order to the runner. A failed step raises `TacticFailed` and a sequence with unclosed goals fails certification. See the [complete examples](#complete-existential-examples).

### logos.tactics.all_goals

Import with `from logos.tactics import all_goals`.

`all_goals(tactic_fn)`

Apply tactic_fn to each open subgoal (for use after a splitting tactic).

### logos.tactics.andL

Import with `from logos.tactics import andL`.

`andL(hyp_name: str, result_name: str)`

Extract left conjunct: from h: A & B, add result_name: A.

### logos.tactics.andR

Import with `from logos.tactics import andR`.

`andR(hyp_name: str, result_name: str)`

Extract right conjunct: from h: A & B, add result_name: B.

### logos.tactics.apply

Import with `from logos.tactics import apply`.

`apply(ref)`

Apply a theorem/axiom/hypothesis to close or transform the goal.

### logos.tactics.assumption

Import with `from logos.tactics import assumption`.

`assumption()`

Return a tactic that closes a goal with a matching local hypothesis, or fails if none matches.

### logos.tactics.auto

Import with `from logos.tactics import auto`.

`auto(*hints, depth: int=5, timeout: float | None=None)`

Automatic tactic. Tries a cascade of strategies up to `depth` search levels.

### logos.tactics.cases

Import with `from logos.tactics import cases`.

`cases(hyp_name: str, case_name: str='h')`

Build a piecewise symbolic expression from condition/value pairs and a default value.

### logos.tactics.conj

Import with `from logos.tactics import conj`.

`conj(h1: str, h2: str, result_name: str)`

Conjunction intro: from h1: A and h2: B, add result_name: A & B.

### logos.tactics.contradiction

Import with `from logos.tactics import contradiction`.

`contradiction()`

Return a tactic that closes a goal using a contradiction derivable from its local hypotheses. Fails if it cannot find one.

### logos.tactics.decide

Import with `from logos.tactics import decide`.

`decide()`

Test a closed Boolean proposition as a tactic. False or unsupported propositions fail. A successful test returns legacy evidence that does not certify the proposition under Rust replay. For portable integer inequalities use `ProofContext.linear`.

### logos.tactics.eval_

Import with `from logos.tactics import eval_`.

`eval_()`

Evaluate ground (variable-free) arithmetic sub-expressions, then close with Refl.

### logos.tactics.exact

Import with `from logos.tactics import exact`.

`exact(term: ProofTerm)`

Return a tactic that supplies the given proof term for checker validation against the current goal.

### logos.tactics.first

Import with `from logos.tactics import first`.

`first(*tactics)`

Try each tactic in order; succeed with the first that doesn't raise TacticFailed.

### logos.tactics.have

Import with `from logos.tactics import have`.

`have(new_name: str, impl_hyp: str, ant_hyp: str)`

Forward modus ponens: from impl_hyp: A→B and ant_hyp: A, add new_name: B.

### logos.tactics.intro

Import with `from logos.tactics import intro`.

`intro(*names: str)`

Return a tactic that opens one universal binder, implication, or negation per supplied name. Continue with the body or consequent, or with falsehood for a negation. Unsupported goal shapes fail.

### logos.tactics.left

Import with `from logos.tactics import left`.

`left(right_type: Expr)`

Return a tactic that chooses the left side of a disjunction and leaves that side as a goal. Pass the right proposition as `right_type`.

### logos.tactics.linarith

Import with `from logos.tactics import linarith`.

`linarith()`

Search for a linear arithmetic consequence of local hypotheses. Unsupported goals or failed searches raise `TacticFailed`. The legacy evidence returned on success does not certify the inequality under Rust replay. Use `ProofContext.linear` for portable certificates.

### logos.tactics.norm_num

Import with `from logos.tactics import norm_num`.

`norm_num()`

Normalize numeric literals and close if equal.

### logos.tactics.order

Import with `from logos.tactics import order`.

`order(law: str)`

Close a strict-order goal with one core order law.

### logos.tactics.refl

Import with `from logos.tactics import refl`.

`refl()`

Return a tactic that closes an equality with structurally identical sides. Other goal shapes fail.

### logos.tactics.repeat

Import with `from logos.tactics import repeat`.

`repeat(tactic_fn)`

Apply tactic_fn until it fails; apply all successful steps.

### logos.tactics.rewrite

Import with `from logos.tactics import rewrite`.

`rewrite(ref)`

Rewrite left-to-right using a named equation or Axiom/Theorem object.

### logos.tactics.rewrite_rev

Import with `from logos.tactics import rewrite_rev`.

`rewrite_rev(ref)`

Rewrite right-to-left using a named equation or Axiom/Theorem object.

### logos.tactics.right

Import with `from logos.tactics import right`.

`right(left_type: Expr)`

Return a tactic that chooses the right side of a disjunction and leaves that side as a goal. Pass the left proposition as `left_type`.

### logos.tactics.ring

Import with `from logos.tactics import ring`.

`ring()`

Return a tactic that closes integer polynomial equalities such as `a*m + b*m == (a+b)*m`. A non-equality or distinct polynomial normal forms fail. See [the complete divisibility proof](what-divides-two-neighbours.html) for the corresponding proof-context operation.

### logos.tactics.split

Import with `from logos.tactics import split`.

`split()`

Return a tactic for A & B that opens A and B as subgoals in that order. Other goal shapes fail.

### logos.tactics.then

Import with `from logos.tactics import then`.

`then(*tactics)`

Apply tactics in sequence to the current goal (as a single compound tactic).

### logos.tactics.try_

Import with `from logos.tactics import try_`.

`try_(tactic_fn)`

Apply tactic_fn; if it fails, return a no-op (transforms goal to itself).

### logos.tactics.unfold

Import with `from logos.tactics import unfold`.

`unfold(*refs)`

Replace App(name, args) nodes with the function's definition body.

### logos.tactics.witness

Import with `from logos.tactics import witness`.

`witness(val: Expr)`

Return a tactic for an existential goal ∃x. P(x). Pass a symbolic value such as `lit(5)`. The tactic opens one subgoal P(value) with the same hypotheses; the next tactic supplies its evidence. Other goal shapes raise `TacticFailed` with `witness: expected Exists`. The checker validates the witness sort and evidence. See the [complete examples](#complete-existential-examples).

## Tactic extensions

[Complete custom tactic](extend-the-checked-language-with-a-domain.html).

### logos.goal.Goal

Import with `from logos.goal import Goal`.

`Goal(context: dict[str, Expr], statement: Expr)`

Construct a tactic input containing `context` (named hypotheses) and `statement` (the conclusion to prove).

### Goal.with_hyp

`with_hyp(name: str, hyp: Expr) -> 'Goal'` on `Goal`.

Return a new goal with the same conclusion and an added or replaced named hypothesis.

### Goal.with_statement

`with_statement(stmt: Expr) -> 'Goal'` on `Goal`.

Return a new goal with the same hypotheses and the supplied conclusion.

### logos.kernel.ProofTerm

Import with `from logos.kernel import ProofTerm`.

Base type for evidence returned by tactics and checked by the verifier.

### logos.runner.TacticFailed

Import with `from logos.runner import TacticFailed`.

Signal that a tactic cannot handle its current goal. The proof runner reports the failure, and tactic alternatives can catch it.

### logos.runner.TacticResult

Import with `from logos.runner import TacticResult`.

A closing `ProofTerm` or a pair of subgoals and a function composing their proofs into evidence for the original goal.

## Finite transition systems

[Complete checked lock model](can-two-clients-hold-the-lock.html).

### logos.domains.transition_systems.FiniteTransitionSystem

Import with `from logos.domains.transition_systems import FiniteTransitionSystem`.

`FiniteTransitionSystem(universe: Iterable[State], initial: Iterable[State], transitions: Mapping[str, Iterable[Edge]], safe: Callable[[State], bool])`

Snapshot an explicit universe, initial states, named relations and safety table.

### FiniteTransitionSystem.export_safety

`export_safety(invariant: Iterable[State], path: str | Path) -> ProofReceipt` on `FiniteTransitionSystem`.

Check initiation, closure and safety with Rust, then write the certificate.

### FiniteTransitionSystem.verify_safety

`verify_safety(invariant: Iterable[State], path: str | Path) -> ProofReceipt` on `FiniteTransitionSystem`.

Require strict evidence for this table and this proposed invariant.

### FiniteTransitionSystem.replay_violation

`replay_violation(start: State, steps: Iterable[tuple[str, State]]) -> State` on `FiniteTransitionSystem`.

Require a legal named run from an initial state to an unsafe state.
