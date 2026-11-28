---
theme: book
title: Extend the Checked Language with a Domain
stem: developer-guide
---

# Extend the Checked Language with a Domain

## Architecture overview

Start with `have_q = p.apply(p_to_q, given_p)` from [Writing Your First Proof](writing-your-first-proof.html#write-the-argument). `Q` is a statement. `have_q` is a local fact carrying evidence for that statement. Follow it from the Python call to the checked reading.

### Construct the statement and evidence in Python

`@logos.theorem` runs the statement function with symbolic arguments and universally quantifies over them. In `logos.expr`, `P >> Q` constructs an `Implies` expression. At check time the proof function receives a `ProofContext`, which tracks the current goal and the facts in scope.

```python {run}
from pathlib import Path

import logos
from logos import Prop

@logos.theorem
def compose(P: Prop, Q: Prop, R: Prop):
    """Two implications compose."""
    return (P >> Q) >> ((Q >> R) >> (P >> R))

@compose.proof
def prove_compose(p, P, Q, R):
    """Use Q as the intermediate proposition."""
    p_to_q = p.assume(P >> Q)
    q_to_r = p.assume(Q >> R)
    given_p = p.assume(P)
    have_q = p.apply(p_to_q, given_p)
    p.note("The first implication supplies Q for the second.")
    return p.apply(q_to_r, have_q)
```

Each `p.assume` introduces the next implication premise as a local hypothesis. In `logos.authoring`, `p.apply` checks that the argument proves the antecedent and constructs an `ImpliesElim` term from two pieces of evidence. In the first application, both pieces are hypothesis references. The last application reaches `R` inside the proof. The context wraps this evidence in introductions that discharge the three hypotheses and generalize over `P`, `Q` and `R`. Case branches and opened existential witnesses also have local scopes. A branch fact or fresh witness cannot escape its block.

Proof terms live in `logos.proofs`. `logos.kernel.infer` computes a term's statement in a context, and `check` compares it with the expected statement. Local checks give authors feedback before replay. For example, `p.apply(q_to_r, given_p)` reports that the step expected `Q` and got `P`. Authoring errors can include the theorem, source location, goal and local facts. A replay error comes from the verifier's own checks.

### Encode, replay, and read the proof

`logos.portable` encodes declarations, the target, dependencies and proof terms in a JSON certificate with format `logos-proof-v1` and theory `logos-core-v1`. The application becomes an `implies_elim` node.

`checker/src/syntax.rs` defines the Rust statement syntax and its sorts, including propositions, integers and integer sequences. `checker/src/lib.rs` defines evidence and replays it. For `implies_elim`, Rust infers each child's statement in scope, checks that the argument establishes the antecedent, and returns the consequent. It enforces hypothesis scope and quantifier and witness freshness, then compares the inferred conclusion with the target. Induction checks the base and step against the induction schema. A `core_law` step instantiates a checker-owned schema with sorted arguments. Arithmetic evidence is checked, for example by verifying the supplied coefficients of a linear combination with exact arithmetic. Program evidence has its own recomputed obligations.

The verifier reports the custom axioms used by the derivation, including through its dependencies. `logos check --strict` refuses a proof that verifies with a custom axiom. An unused declaration adds no dependency. The local premises of `compose` are discharged by implication introduction, so it uses zero custom axioms.

```python {run continue}
compose.check()
certificate = Path("compose.logos")
receipt = logos.export_proof(compose, certificate)
assert certificate.read_bytes() == receipt.artifact
reading = compose.inspect()
assert "Uses zero custom axioms." in reading
assert "The first implication supplies Q for the second." in reading
print("compose: Rust replay verified and the checked reading includes the note")
```

::: proof
```python {run continue echo=false}
print(reading)
```
:::

Python records a `ProofReceipt` after the Rust response matches the target, format, theory and SHA-256 of the submitted bytes. Export writes those exact bytes. The digest identifies the artifact, and successful replay establishes its judgment. `inspect()` requires a current receipt and asks Rust to replay its artifact and render the checked trace. Read the derived `Q` in the scope that contains `given_p`, then read the final universally quantified implication. The theorem and proof docstrings supply the author's claim and strategy. `p.note` annotates the last derived fact. All three travel as author commentary and contribute no inference. The checked conclusion comes from the evidence.

Send `compose.logos` to another reader with a compatible Rust executable. These commands run offline with only that executable and the file. Keep the certificate alongside the Markdown so the recipient can replay it.

```bash
logos check --strict compose.logos
logos inspect --markdown --strict compose.logos > compose.md
```

### Mix manual steps with tactics and domains

A tactic consumes a `Goal` containing a statement and context. It returns a `ProofTerm` or a list of subgoals paired with a function that builds the original proof term from the subgoal proofs. See `logos.goal` and `logos.runner`. An introduction tactic exposes a smaller goal and supplies the builder that wraps its proof in an introduction. `TacticFailed` means the attempt did not produce evidence. The goal may still have a proof.

In `logos.domains.number_theory.common_divisor`, the author opens the two divisibility hypotheses, chooses the witness `j - k`, then calls `p.ring` with the two quotient equations to establish the witness equation. The arithmetic search leaves the witness choice to the author. [What Divides Two Neighbours](what-divides-two-neighbours.html) develops the argument.

A domain packages reusable work. `number_theory` defines `divides` and `prime` with transparent bodies and supplies checked lemmas such as `divides_trans`. `logos.domains.intervals` defines `contains` and `overlaps`, proves lemmas such as `common_point_overlaps`, and supplies `interval`, an evidence-producing tactic. The worked extension below follows its two linear certificates back to the facts in scope.

### Bind a contract to code and replay its obligations

The [binary-search chapter](binary-search-all-the-way-down.html) uses `@logos.function` with named `requires`, `ensures`, `invariant` and `decreases` clauses. Python reads and compiles the source and checks that it matches the imported function's code object. It translates supported syntax to a restricted program IR with typed variables, assignments, branches, loops, returns and direct calls. A call carries the callee program and the call-site contract into the artifact. Python attaches the clauses and searches for evidence. `checker/src/program.rs` derives obligations from the serialized IR; the checker verifies callees before callers, rejects cycles and recomputes each call-site precondition from the actual arguments. Rust checks the supplied proofs against those obligations, including safety, every named invariant, termination, the postcondition and each callee contract. Independent replay establishes the contract for the IR. Python source binding and translation connect that IR to the Python function, and the artifact's programs define the function identities the checker verifies.

Shifting the midpoint in the binary-search source makes the preservation obligation fail during Python proof construction. The installed replay test in `tests/installed_portable.py` instead forges the exported bundle by replacing an assignment inside the loop with a constant and leaving the obligation proofs in place. The recipient runs the Rust verifier directly and gets a rejection. The smaller replay tests in `checker/tests/programs.rs` isolate the same check. A valid bundle assigns `y = x + 0` and returns `y`. The rejection test changes the assignment to `x + 1` while retaining the old obligation proof. Rust rejects the evidence offered for the changed program. Another test removes the obligation proof entirely and Rust refuses that bundle too.

[Issue #61](https://github.com/gia-uh/logos/issues/61) tracks the in-progress declarative function and checked-callee design. It proposes checking a callee separately and replaying its dependency when checking the caller. The walkthrough above describes the explicit contract API on main.

The rest of this guide develops the interval extension for closed integer intervals, from transparent definitions to offline replay.

## Before you start

**Prerequisites.** Chapters 6, 7 and 11 for transparent definitions, checked lemmas and witnesses; Chapter 13 for the distinction between a Python search and a checked certificate. You should be able to read a `Goal`, a `ProofTerm` and a `core_law` step.

**Outcomes.** You will add domain vocabulary as transparent definitions, prove reusable lemmas, write a goal-level tactic that returns checked evidence, read its failures, test the domain, and replay the certificate with only the Rust executable. You will also decide whether a new general law belongs in Rust or in Python.

## Vocabulary is a definition, not an axiom

The first decision is what the words mean. `contains` and `overlaps` are definitions with bodies. The checker may unfold them during conversion, so a proof never needs a custom axiom to relate the name to its meaning.

Use ordered endpoints: `a_lo <= a_hi` and `b_lo <= b_hi`. A point lies
in an interval when both endpoints bound it. Two valid intervals share
a point exactly when the later start is at or before the earlier end.
Each start is already at or before its own end, leaving two comparisons
to check: `a_lo <= b_hi` and `b_lo <= a_hi`. If both hold, the later start
itself belongs to both intervals.

```text
Intersecting   A: [0-------3]
               B:     [2-------5]

Separated      A: [0---1]
               B:           [2---3]
```

For `[0,3]` and `[2,5]`, both cross-bounds hold and 2 is common.
For `[0,1]` and `[2,3]`, the second cross-bound would require `2 <= 1`.
The definitions leave endpoint validity to the caller. With reversed
endpoints, `[3,1]` contains no point, yet both its cross-bounds with
`[0,4]` hold. The docstring's “share a point” interpretation assumes
valid endpoints for both intervals.

<!-- source: contains -->
```python
@logos.definition
def contains(lo: Int, hi: Int, x: Int):
    """The closed interval [lo, hi] contains x."""
    return (lo <= x) & (x <= hi)
```

<!-- source: overlaps -->
```python
@logos.definition
def overlaps(a_lo: Int, a_hi: Int, b_lo: Int, b_hi: Int):
    """The closed intervals [a_lo, a_hi] and [b_lo, b_hi] share a point."""
    return (a_lo <= b_hi) & (b_lo <= a_hi)
```

The source blocks in this chapter are quoted from the module and a test compares them, so the guide cannot drift from the code. The important difference from an axiom is that an axiom would be an opaque fact the checker accepts without a body. A definition has a body, and the checker can replace the name with it whenever two statements are compared. No custom axiom enters the judgment.

## Check the lemmas once, reuse them everywhere

Four lemmas carry the mathematics. The first says a nonempty interval overlaps itself. The second swaps the conjuncts. The third turns a common point into an overlap. The fourth says an interval entirely to the left of another shares no point with it.

<!-- source: overlap_self -->
```python
@logos.theorem
def overlap_self(lo: Int, hi: Int):
    """A nonempty interval overlaps itself."""
    return (lo <= hi) >> overlaps(lo, hi, lo, hi)

@overlap_self.proof
def prove_overlap_self(p, lo, hi):
    """Both sides of the overlap are the same non-strict bound."""
    nonempty = p.assume(lo <= hi)
    return p.and_intro(nonempty, nonempty)
```

<!-- source: overlap_comm -->
```python
@logos.theorem
def overlap_comm(a_lo: Int, a_hi: Int, b_lo: Int, b_hi: Int):
    """Overlap is symmetric."""
    return overlaps(a_lo, a_hi, b_lo, b_hi) >> overlaps(b_lo, b_hi, a_lo, a_hi)

@overlap_comm.proof
def prove_overlap_comm(p, a_lo, a_hi, b_lo, b_hi):
    """Swap the two conjuncts."""
    shared = p.assume(overlaps(a_lo, a_hi, b_lo, b_hi))
    return p.and_intro(shared.right(), shared.left())
```

Unfold the two containment premises to get `a_lo <= x <= a_hi` and
`b_lo <= x <= b_hi`. A common point already forces both intervals to
be valid. Work backward from each overlap goal:

| Goal | Chain | Facts passed to `p.linear` |
|---|---|---|
| `a_lo <= b_hi` | `a_lo <= x <= b_hi` | `left.left()`, `right.right()` |
| `b_lo <= a_hi` | `b_lo <= x <= a_hi` | `right.left()`, `left.right()` |

Here `left` is the containment in A and `right` is the containment in
B. The second call needs B's lower bound to connect `b_lo` to `x`.

<!-- source: common_point -->
```python
@logos.theorem
def common_point_overlaps(a_lo: Int, a_hi: Int, b_lo: Int, b_hi: Int, x: Int):
    """A point contained in both intervals witnesses an overlap."""
    return (contains(a_lo, a_hi, x) & contains(b_lo, b_hi, x)) >> overlaps(
        a_lo, a_hi, b_lo, b_hi
    )

@common_point_overlaps.proof
def prove_common_point_overlaps(p, a_lo, a_hi, b_lo, b_hi, x):
    """Chain the two containment bounds through x."""
    both = p.assume(contains(a_lo, a_hi, x) & contains(b_lo, b_hi, x))
    left, right = both.left(), both.right()
    first = p.linear(a_lo <= b_hi, using=[left.left(), right.right()])
    second = p.linear(b_lo <= a_hi, using=[right.left(), left.right()])
    return p.and_intro(first, second)
```

<!-- source: disjoint -->
```python
@logos.theorem
def disjoint_no_common_point(a_lo: Int, a_hi: Int, b_lo: Int, b_hi: Int, x: Int):
    """An interval entirely to the left shares no point with one to its right."""
    return (a_hi < b_lo) >> (contains(a_lo, a_hi, x) >> ~contains(b_lo, b_hi, x))

@disjoint_no_common_point.proof
def prove_disjoint_no_common_point(p, a_lo, a_hi, b_lo, b_hi, x):
    """A common point would force a_hi < b_lo <= x <= a_hi."""
    before = p.assume(a_hi < b_lo)
    inside_left = p.assume(contains(a_lo, a_hi, x))
    with p.negate() as suppose:
        inside_right = suppose.assumption
        suppose.finish(p.linear(
            False,
            using=[before, inside_left.right(), inside_right.left()],
        ))
    return suppose.result
```

Run them all. `check_all` checks each theorem with the installed verifier and returns the tuple. The `certified` flag is not the checker's word: it is true only while the current statement, evidence and dependencies still match the receipt bytes.

```python {run}
import logos
from logos import Int, tactics as t
from logos.domains import intervals

for theorem in intervals.check_all():
    print(f"{theorem.name}: {theorem.certified}")
```

## Reuse compiled evidence across processes

A fresh Python process normally runs every proof body before it builds the
certificate. For a library of many small lemmas that work repeats itself. The
persistent evidence cache lets `check()` reuse the compiled proof term of an
unchanged lemma, while Rust still replays the complete certificate.

A cache record is not a certificate and not a verdict. It holds one compiled
`ProofTerm` graph, keyed by:

- the theorem name and the declared statement;
- the declarations and their sorts;
- the source text, code object, bytecode globals and module path of the
  authored proof function;
- the live theorem and axiom objects the evidence references, including their
  statements and declarations;
- a digest of the Logos Python sources plus `logos-proof-v1` and
  `logos-core-v1`.

The cache is enabled by default under the user cache directory. These
environment variables control it:

| Variable | Meaning |
|---|---|
| `LOGOS_CACHE=off` | Execute every proof body; read and write no records. |
| `LOGOS_CACHE_DIR=/path` | Use exactly this directory as the evidence cache. |
| `LOGOS_CACHE=on` | The default. |

A record is used only when all of those inputs still match. When a proof
source changes, its key changes, so the old record is ignored. When a
dependency statement or declaration changes, the parent record no longer
matches its live binding, so the parent executes again. An edit to a
dependency's *proof* keeps the parent record eligible: the parent still cites
the live theorem by name, and the artifact carries the dependency's current
proof, which Rust checks.

The eligibility rule is deliberately narrow. A proof uses the cache only when:

- it is a book-style authored proof function (`@thm.proof def prove_x(p)`);
- the function is module-level, has an empty closure, no default arguments,
  no nested code objects or lambdas and readable source;
- its bytecode neither writes globals or attributes, imports, yields nor
  awaits, and it does not use stateful builtins such as `open`, `eval` or
  `getattr`;
- every global it reads is an immutable value, a tuple of such values, a
  theorem or axiom declaration, or a Logos library function;
- its compiled evidence uses only the portable vocabulary: arithmetic,
  comparisons, connectives, quantifiers and the ordinary proof terms. Function
  applications, primitive-recursion terms, program references and `Subst`
  terms keep executing.

Everything else executes as before. That includes plain tactic lists,
closures, mutable or opaque globals, missing source, `@logos.function`
declarations, program contracts and source-bound revalidation. Those paths do
not silently become cache hits.

Loads are untrusted. After reviving a record, `check()` builds the full artifact
and invokes the installed Rust checker exactly as it would for freshly executed
evidence. A record whose evidence proves the wrong statement fails the Rust
check. Records are written only after Rust accepted the artifact that used
them. A malformed, incompatible or unreadable record is ignored and the proof
executes; an unwritable cache leaves `check()` working. Writes use a temporary
file and an atomic rename, so concurrent processes cannot read a partial
record. The record is JSON with an explicit constructor whitelist; there is no
pickle and no executable deserialization.

On a balanced tree of 1,022 integer-equality lemmas, with leaves proved by
`p.ring` and joins by `p.trans`, one host produced these median wall times for
the `check()` call after import (three runs per row):

| Operation | Without cache | First run with cache | Repeated with cache | Proof bodies executed | Rust checks |
|---|---:|---:|---:|---:|---:|
| Cold seed of both roots | 4.7 s | 6.7 s | 1.6 s | 1,022 then 0 | 2 |
| Add a theorem citing two roots through a tuple | 4.6 s | 1.6 s | 1.8 s | 1 then 0 | 1 |
| Edit one branch of the new proof | 4.9 s | 1.6 s | 1.7 s | 1 then 0 | 1 |
| Change one base lemma proof | 4.8 s | 1.7 s | 1.7 s | 1 then 0 | 1 |
| Narrow subset of three lemmas | 0.038 s | 0.055 s | 0.025 s | 3 then 0 | 1 |

The first cold seed pays about two seconds to fingerprint and write 1,022
records. Every later run spends about 1.6 seconds in Python instead of 4.7 to
5.0, and executes only the proof that changed. The artifact is byte-identical
with and without a warm cache. The Rust checker sees the same 1,022 lemma
records every time. The remaining Python cost is the portable artifact
assembly and the receipt freshness check, not proof search. On the narrow
subset the cache is nearly break-even: three tiny proofs do not repay the
record I/O.

The cache does not make Rust faster, does not store per-lemma Rust verdicts and
does not change the portable format. A recipient who receives a `.logos` file
still needs only the Rust checker and sees no cache metadata. If a record is
suspicious, set `LOGOS_CACHE=off` or point `LOGOS_CACHE_DIR` at a new directory;
the proof executes and a fresh record is written after the next successful
check.

## A tactic returns evidence, not trust

The four lemmas are enough to write proofs by hand, but a developer will meet the same overlap goal repeatedly. The `interval` tactic closes an overlap goal by unfolding it and building two linear certificates from the order facts in the local context. It uses the same exact Farkas routine as `p.linear`; it does not search for a truth it cannot certify.

### Extract bounds and their proofs

After introducing the common-point premise, the context contains the five
integer variables followed by the premise `both`. The variables
yield no order facts. The premise has index 5 and gets prefix
`__interval_5`. Unfold it and its two containments, then project the
leaves. Each left or right projection appends `l` or `r`.

| Name | Statement | Projections from `both` |
|---|---|---|
| `__interval_5ll` | `a_lo <= x` | left, left |
| `__interval_5lr` | `x <= a_hi` | left, right |
| `__interval_5rl` | `b_lo <= x` | right, left |
| `__interval_5rr` | `x <= b_hi` | right, right |

Each recursive call carries the evidence for its part of the conjunction.
Start here when an expected bound is absent from the solver's input.

<!-- source: order-facts -->
```python
def _orders(expression, proof, name):
    """Yield the order conjuncts of a fact, with evidence for each one."""
    expression = unfold(expression)
    if isinstance(expression, And):
        yield from _orders(expression.left, AndElimL(proof), name + "l")
        yield from _orders(expression.right, AndElimR(proof), name + "r")
    elif isinstance(expression, (Le, Lt, Eq)):
        yield name, expression, proof
```

### Bind facts before replaying the linear step

For the first chain, the solver assigns coefficient 1 to each of the
`ll` and `rr` facts. Their sum cancels `x`:
`(a_lo - x) + (x - b_hi) <= 0`. Rust adds the negated goal,
`b_hi < a_lo`, and checks that the sum yields the contradiction
`0 < 0`.

Each `Have` checks its projection from `both` and binds the fact in
its body. The first side has this structure:

```text
Have __interval_5ll  (a_lo <= x)
  Have __interval_5lr  (x <= a_hi)
    Have __interval_5rl  (b_lo <= x)
      Have __interval_5rr  (x <= b_hi)
        Linear a_lo <= b_hi  [__interval_5ll: 1, __interval_5rr: 1]
```

The loop builds from the inside out. It iterates in reverse so replay
sees the bindings in extraction order. All four projections refer
directly to `both`, so their order does not affect the arithmetic.
The `Linear` node must sit inside the bindings it uses. The tactic
builds the other side the same way and joins them with `AndIntro`.

<!-- source: tactic -->
```python
def _fraction_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def interval(goal: Goal):
    """Close an overlap goal with a checked linear certificate.

    The tactic unfolds the goal, flattens every order conjunct in the local
    context, and asks the exact Farkas routine for each side of the overlap.
    A side it cannot derive raises ``TacticFailed`` with that side in the
    message; it never returns unchecked evidence.
    """
    statement = unfold(goal.statement)
    if not isinstance(statement, And):
        raise TacticFailed(
            "interval: expected an overlap after unfolding, got "
            f"{format_expr(statement)}"
        )
    facts = []
    for index, (binder, proposition) in enumerate(goal.context.items()):
        facts.extend(_orders(proposition, HypRef(binder), f"__interval_{index}"))

    def close(side):
        bounds = [(name, expression) for name, expression, _ in facts]
        labels = farkas(unfold(side), bounds)
        if labels is None:
            raise TacticFailed(
                f"interval: no linear certificate for {format_expr(side)}"
            )
        proof = Linear(
            side,
            tuple((name, _fraction_text(value)) for name, value in labels.items()),
        )
        for name, expression, subproof in reversed(facts):
            proof = Have(name, expression, subproof, proof)
        return proof

    return AndIntro(close(statement.left), close(statement.right))
```

Use it on the common-point claim. The proof introduces the five variables and the conjunction, then hands the goal to the tactic.

```python {run continue}
@logos.theorem
def common_point_by_tactic(a_lo: Int, a_hi: Int, b_lo: Int, b_hi: Int, x: Int):
    return (intervals.contains(a_lo, a_hi, x) & intervals.contains(b_lo, b_hi, x)) >> (
        intervals.overlaps(a_lo, a_hi, b_lo, b_hi)
    )

logos.check(common_point_by_tactic.proof(
    t.intro("a_lo", "a_hi", "b_lo", "b_hi", "x", "both"),
    intervals.interval,
))
print("common_point_by_tactic:", common_point_by_tactic.certified)
logos.export_proof(common_point_by_tactic, "intervals.logos")
tactic_reading = common_point_by_tactic.inspect()
print("zero custom axioms:", "Uses zero custom axioms." in tactic_reading)
print("certificate: intervals.logos")
```

## When a step fails

A failed tactic is not a refutation. It says the evidence you supplied does not establish this goal. The distinction matters when the goal is true but the context is too weak, and when the goal is false.

First try to prove overlap from `a_hi < b_lo`. The intervals
`[0,1]` and `[2,3]` satisfy the premise but violate `b_lo <= a_hi`.
The tactic stops at the first side it cannot derive, `a_lo <= b_hi`,
which happens to hold for these particular endpoints.

```python {run continue}
@logos.theorem
def impossible(a_lo: Int, a_hi: Int, b_lo: Int, b_hi: Int):
    return (a_hi < b_lo) >> intervals.overlaps(a_lo, a_hi, b_lo, b_hi)

try:
    logos.check(impossible.proof(
        t.intro("a_lo", "a_hi", "b_lo", "b_hi", "before"),
        intervals.interval,
    ))
except logos.LogosProofError as error:
    print("diagnostic:", error)
else:
    raise AssertionError("separated intervals should defeat the tactic")
```

Compare this with a failed attempt at the true common-point claim.
Giving the second call A's lower bound instead of B's drops the link
from `b_lo` to `x`. The conjunction is in scope, but this call to
`p.linear` receives only A's projected bounds.

```python {run continue}
@common_point_by_tactic.proof
def missing_bound(p, a_lo, a_hi, b_lo, b_hi, x):
    both = p.assume(intervals.contains(a_lo, a_hi, x) &
                    intervals.contains(b_lo, b_hi, x))
    left, right = both.left(), both.right()
    first = p.linear(a_lo <= b_hi, using=[left.left(), right.right()])
    second = p.linear(b_lo <= a_hi, using=[left.left(), left.right()])
    return p.and_intro(first, second)

try:
    common_point_by_tactic.check()
except logos.LogosProofError as error:
    print("construction diagnostic:", error)
else:
    raise AssertionError("the selected bounds should be insufficient")
```

Both diagnostics report a failure to construct evidence. The separated
intervals refute the first claim. The two valid chains prove the
second claim when both lower bounds are supplied.

Another failure is the wrong shape. A negation is not an overlap, so the tactic refuses before it builds any certificate:

```python {run continue}
@logos.theorem
def wrong_shape(a_lo: Int, a_hi: Int, b_lo: Int, b_hi: Int, x: Int):
    return (intervals.contains(a_lo, a_hi, x) & intervals.contains(b_lo, b_hi, x)) >> (
        ~intervals.overlaps(a_lo, a_hi, b_lo, b_hi)
    )

try:
    logos.check(wrong_shape.proof(
        t.intro("a_lo", "a_hi", "b_lo", "b_hi", "x", "both"),
        intervals.interval,
    ))
except logos.LogosProofError as error:
    print("diagnostic:", error)
else:
    raise AssertionError("the interval tactic should reject a negation")
```

The message says `interval: expected an overlap after unfolding`.
The tactic requires an unfolded conjunction before trying arithmetic.

## Test the domain, not only the examples

The domain tests check each lemma, replay a certificate and assert the tactic diagnostics. The chapter tests also render the examples, replay the exported tactic proof and check the exit solutions. Run them with Scriptorium and the Rust checker on `PATH`:

```bash
python -m pytest -q tests/test_intervals.py tests/test_developer_guide.py
```

The important assertions are not the printed `True` values. They are:

- every lemma's inspection says `Uses zero custom axioms`;
- the exported certificate exits 0 under `logos check --strict`;
- a missing order fact fails with `interval: no linear certificate for`;
- a negated overlap fails with `interval: expected an overlap after unfolding`;
- the JSON trace contains a `linear` step, so the proof really used the checked certificate.

The insufficient-bound mutation fails during Python proof construction.
To test Rust directly, the replay test changes one coefficient in the
exported working tactic proof and runs `logos check --strict` on both
files. Rust accepts the original and rejects the changed combination.

## Replay it without Python

In the checked reading below, follow step 18 back to steps 5 and 17.
These are the two bound hypotheses named `__interval_5ll` and
`__interval_5rr` in the certificate. Step 39 checks the other chain
and step 44 joins the two results after their local bindings close.

::: proof
```python {run continue echo=false}
print(tactic_reading)
```
:::

The recipient needs only the Rust executable and the file. No Python, no module, no tactic script, no repository checkout:

```bash
logos check --strict intervals.logos
logos inspect --markdown --strict intervals.logos > intervals.md
```

The first command prints the verified statement and `Verified with 0 custom axioms`; the second writes a Markdown derivation from the checked trace. The `--strict` flag is meaningful because the proof uses no custom axioms. A theorem with discharged premises can verify and exit 0. A proof that depends on a custom axiom exits 3 under strict policy. The file's SHA-256 identifies the exact bytes, and the format and theory IDs are `logos-proof-v1` and `logos-core-v1`.

The extension did not change either ID. A recipient with an older binary can still replay an older certificate, and this certificate replays on a binary that predates the interval module because the module produced only existing evidence tags.

## Where should a change live?

| Change | Edit here |
|---|---|
| Explain a step, name a fact, or improve an error about a misplaced hypothesis | Proof docstrings and `p.note`, or contexts and diagnostics in `logos.authoring` |
| Change Python's representation of a statement or how it constructs and checks an existing inference | `logos.expr`, `logos.proofs` and `logos.kernel`. Check the mapping in `logos.portable`. |
| Find a witness, choose a lemma, or automate arithmetic | A proof function or a tactic under `logos.tactics` that returns evidence for the existing verifier |
| Add mathematical vocabulary or a reusable argument | A transparent definition, checked lemma or tactic in the relevant `logos.domains` module |
| Translate more Python syntax to an existing IR operation | Source binding and translation in `logos.contracts`. Test imported source and replay. |
| Change program semantics, accepted evidence or checked explanations | The corresponding Rust code in `checker/src/program.rs`, `lib.rs`, `syntax.rs` or `markdown.rs`. Test direct replay and update the wire mapping if it changes. |

## When is a general Rust rule warranted?

The interval domain did not need a new core law. Its facts are consequences of integer order and the definitions, and `p.linear` already emits a general certificate. That is the default: keep the mathematics in Python and let the existing verifier check it.

A new checker-owned law is warranted only when all of these hold:

1. **More than one domain needs the same schema.** `le_refl` is used wherever a non-strict bound closes a goal; `sorted_gap` states a fact about sorted sequences, not about one search algorithm. `overlap_comm` is used by the interval domain and by nothing else, so it belongs in Python.
2. **It states a semantic fact about the core fragment, not a domain definition.** A law may quantify over integers, sequences, propositions and the existing connectives. It may not introduce a room, a booking or a time zone into the theory.
3. **It can be written with the existing sorts and tags.** A new expression tag or a changed meaning of an old one is a format change, not an additive law.
4. **It has a soundness argument and exact negative tests.** Every substitution of the stated sorts must make the conclusion true. The tests must reject the wrong arity, the wrong sort, an unknown ID, a forged instance and a declaration that tries to reuse the law ID.
5. **It reduces proof size or search time materially.** If a Python lemma is short and reusable, the kernel does not need the schema.

When the answer is yes, the change crosses four published surfaces. Add the schema and its builder to the checker's law table. Add the positive instance and every negative case to the Rust suite. Publish the ID in `logos commands --json` and in the proof-format manual. If the Python tactics need to construct the law, add the same schema to `logos/core_laws.py`. A drift test compares the three inventories, so a law cannot exist in one place and be missing from another.

The compatibility rule is stricter than the tests. Adding a law ID to `logos-core-v1` is additive: old certificates do not mention it and still replay byte for byte. Changing a law's statement, removing an ID, adding an expression tag or changing conversion semantics requires a new theory or format ID. A recipient must be able to tell which semantics a file was checked under without guessing from the producer's version.

## Limits

The domain models closed integer intervals. It does not model real time, time zones, durations, exclusive endpoints, recurring bookings or the database that stores them. A checked overlap claim is a statement about the model, not a guarantee that the booking service is deployed correctly.

The tactic is a certificate builder, not a decision procedure. It closes overlap goals whose sides follow from order facts by exact linear arithmetic. It does not search for a witness, split on cases, or prove a negated overlap. A failed call leaves the theorem uncertified; it does not prove the negation.

## Exit exercise

1. Define `touches` on valid closed intervals by endpoint equality:
   `a_hi == b_lo` or `b_hi == a_lo`. Prove symmetry and prove that
   the singleton interval `[x,x]` touches itself. Test separated
   intervals and refute “every nonempty interval touches itself.”
2. Define `inside` with two explicit endpoint bounds. Prove that if
   A lies inside B and A overlaps C, then B overlaps C. Find a
   counterexample to the reverse implication. Identify both bound
   chains before writing Python.
3. Export the three proofs and replay them with `logos check --strict`.
   Use the layer table to choose where this extension belongs. Explain
   how Python constructs evidence and what Rust checks independently.

After attempting the exercises, compare your argument with the
[instructor proofs and counterexample tests](https://github.com/gia-uh/logos/blob/main/tests/test_developer_guide.py).
