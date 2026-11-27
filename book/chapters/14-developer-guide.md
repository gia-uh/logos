---
theme: book
title: Extend the Checked Language with a Domain
stem: developer-guide
---

# Extend the Checked Language with a Domain

The User Guide solved one problem per chapter. This chapter is for the developer who wants to add the next problem. The worked extension is a small theory of closed integer intervals for a room-booking system: two intervals overlap when they share a point, an interval contains a point, and disjoint intervals have no common point.

The extension is one Python module, `logos.domains.intervals`. It adds no Rust rule and no proof-format tag. Everything it proves is checked by the existing verifier. The chapter ends with the question a developer must ask before changing the checker: when is a general Rust rule warranted, and what must accompany it?

## Before you start

**Prerequisites.** Chapters 6, 7 and 11 for transparent definitions, checked lemmas and witnesses; Chapter 13 for the distinction between a Python search and a checked certificate. You should be able to read a `Goal`, a `ProofTerm` and a `core_law` step.

**Outcomes.** You will add domain vocabulary as transparent definitions, prove reusable lemmas, write a goal-level tactic that returns checked evidence, read its failures, test the domain, and replay the certificate with only the Rust executable. You will also decide whether a new general law belongs in Rust or in Python.

## Vocabulary is a definition, not an axiom

The first decision is what the words mean. `contains` and `overlaps` are definitions with bodies. The checker may unfold them during conversion, so a proof never needs a custom axiom to relate the name to its meaning.

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

The cost is that every lemma is about the unfolded form. A reader who wants to know why `overlaps(a, b)` follows from a point in both intervals has to read the two order atoms, not trust a table.

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

## A tactic returns evidence, not trust

The four lemmas are enough to write proofs by hand, but a developer will meet the same overlap goal repeatedly. The `interval` tactic closes an overlap goal by unfolding it and building two linear certificates from the order facts in the local context. It uses the same exact Farkas routine as `p.linear`; it does not search for a truth it cannot certify.

<!-- source: tactic -->
```python
def _fraction_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _orders(expression, proof, name):
    """Yield the order conjuncts of a fact, with evidence for each one."""
    expression = unfold(expression)
    if isinstance(expression, And):
        yield from _orders(expression.left, AndElimL(proof), name + "l")
        yield from _orders(expression.right, AndElimR(proof), name + "r")
    elif isinstance(expression, (Le, Lt, Eq)):
        yield name, expression, proof


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
            f"interval: expected an overlap after unfolding, got {format_expr(statement)}"
        )
    facts = []
    for index, (binder, proposition) in enumerate(goal.context.items()):
        facts.extend(_orders(proposition, HypRef(binder), f"__interval_{index}"))

    def close(side):
        labels = farkas(unfold(side), [(name, expression) for name, expression, _ in facts])
        if labels is None:
            raise TacticFailed(f"interval: no linear certificate for {format_expr(side)}")
        proof = Linear(
            side,
            tuple((name, _fraction_text(value)) for name, value in labels.items()),
        )
        for name, expression, subproof in reversed(facts):
            proof = Have(name, expression, subproof, proof)
        return proof

    return AndIntro(close(statement.left), close(statement.right))
```

Read the last three lines of `close`. `farkas` returns coefficients for the facts it used; `Linear` is the checker-owned certificate; each derived order fact is bound with `Have` before the certificate. The tactic's only job is to propose a certificate. The Rust checker parses it, recomputes the arithmetic and rejects a wrong combination. A tactic bug can make a proof fail; it cannot make a false proof pass.

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
```

## When a step fails

A failed tactic is not a refutation. It says the evidence you supplied does not establish this goal. The distinction matters when the goal is true but the context is too weak, and when the goal is false.

The first failure is a claim with no certificate. The hypothesis says the left interval ends before the right one starts; the goal says they overlap. The tactic finds no linear combination for the first side and names it.

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
```

The message is

```text
Theorem 'impossible': interval: no linear certificate for a_lo <= b_hi
```

It names the side, not a step number. If the goal is true, the repair is to add the missing order fact to the context or to prove an intermediate lemma. If the goal is false, the message is the evidence that the domain model and the claim disagree.

The second failure is the wrong shape. A negation is not an overlap, so the tactic refuses before it builds any certificate:

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
```

The message says `interval: expected an overlap after unfolding`. A tactic that silently returned an unchecked term, or a checker that trusted the tactic, would turn either diagnostic into a false success. Neither happens here.

A third failure is a wrong bound inside a hand-written lemma. Change the sign in `prove_common_point_overlaps`, or pass the wrong containment fact to `p.linear`, and the authoring layer reports `linear arithmetic could not derive the goal from these facts` with the goal and the facts it was given. The checker never sees a certificate, so the theorem is not certified.

## Test the domain, not only the examples

The domain has two kinds of tests. The positive tests check every lemma and replay a certificate. The negative tests construct the failures above and require the exact diagnostic. A test that only checks the happy path would not notice a tactic that returned a plausible term.

The repository test file is `tests/test_intervals.py`. Run it with the checker on `PATH`:

```bash
python -m pytest -q tests/test_intervals.py
```

The important assertions are not the printed `True` values. They are:

- every lemma's inspection says `Uses zero custom axioms`;
- the exported certificate exits 0 under `logos check --strict`;
- a missing order fact fails with `interval: no linear certificate for`;
- a negated overlap fails with `interval: expected an overlap after unfolding`;
- the JSON trace contains a `linear` step, so the proof really used the checked certificate.

A mutation test is the next step. Change one bound in `common_point_overlaps` from `a_lo <= b_hi` to `b_hi <= a_lo`, or swap the two facts passed to `p.linear`, and the proof must fail. If it still passes, the domain's tests are testing Python, not the checker.

## Replay it without Python

The certificate is the artifact a recipient uses. Export the common-point theorem and inspect the bytes:

```python {run continue}
logos.export_proof(intervals.common_point_overlaps, "intervals.logos")
reading = intervals.common_point_overlaps.inspect()
print("zero custom axioms:", "Uses zero custom axioms." in reading)
print("certificate: intervals.logos")
```

The recipient needs only the Rust executable and the file. No Python, no module, no tactic script, no repository checkout:

```bash
logos check --strict intervals.logos
logos inspect --markdown --strict intervals.logos > intervals.md
```

The first command prints the verified statement and `Verified with 0 custom axioms`; the second writes a Markdown derivation from the checked trace. The `--strict` flag is meaningful because the proof uses no custom axioms. A conditional proof would verify and exit 0; a proof that needed an author assumption would exit 3 under strict policy. The file's SHA-256 identifies the exact bytes, and the format and theory IDs are `logos-proof-v1` and `logos-core-v1`.

The extension did not change either ID. A recipient with an older binary can still replay an older certificate, and this certificate replays on a binary that predates the interval module because the module produced only existing evidence tags.

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

This chapter's only checker change is a trace fix: a `have` binder that the body never uses is still part of the checked derivation, so the Markdown reading can name the discharged assumption. The fixture certificates replay with the same SHA-256 and the same zero custom axioms. No law was added.

## Limits

The domain models closed integer intervals. It does not model real time, time zones, durations, exclusive endpoints, recurring bookings or the database that stores them. A checked overlap claim is a statement about the model, not a guarantee that the booking service is deployed correctly.

The tactic is a certificate builder, not a decision procedure. It closes overlap goals whose sides follow from order facts by exact linear arithmetic. It does not search for a witness, split on cases, or prove a negated overlap. A failed call leaves the theorem uncertified; it does not prove the negation.

The Python layer is trusted to propose definitions, witnesses and coefficients. The Rust checker recomputes the conclusion, checks every premise and rejects a certificate it cannot replay. The trust boundary is the translation from Python expressions to the bundle, which is the same boundary every other chapter uses.

## Exit exercise

Add a `touches` definition for closed intervals that meet at one endpoint: `a_hi = b_lo` or `b_hi = a_lo`. Prove that `touches` is symmetric. Then add a lemma that says a nonempty interval touches itself, and decide whether either fact warrants a new Rust law. Write the negative test for the case where the intervals are separated, export the positive certificate and replay it with `logos check --strict`.

As a second exercise, add a `contained` lemma: if `[a_lo, a_hi]` is inside `[b_lo, b_hi]` and the outer interval overlaps `[c_lo, c_hi]`, then the inner one overlaps it too. State the two containment hypotheses explicitly. If the proof needs a new order fact, add it as a `p.linear` certificate; if it needs a new definition, keep the definition transparent. Do not add a Rust law unless the same schema is needed by a second domain.
