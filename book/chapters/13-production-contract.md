---
theme: book
title: A Contract on Code That Ships
stem: production-contract
---

# A Contract on Code That Ships

The previous chapter proved a function written for the book. This one proves a function that ships with Python. The subject is `adapt`, the bias adaptation step of the punycode codec in the standard library. It is small, it is maintained, and it is used by the `idna` codec when a label is encoded.

The claim is deliberately modest: for every non-negative `delta` and every positive `numchars`, `adapt` terminates and returns a non-negative bias. That is the property the RFC 3492 digit thresholds depend on. The chapter does not claim that the whole IDNA implementation is verified, and it does not present the book's copy as a replacement for the standard library. It verifies one identifiable component and states exactly what the certificate binds.

## Before you start

**Prerequisites.** Chapter 12, and the contract fragment from the README: a module-level function with integer and sequence parameters, one loop, one final return, and no early returns. You should be able to read a verification condition and a variant.

**Outcomes.** You will bind a theorem to a real standard-library function, compare the verified body with the interpreter's code object, prove a non-negativity invariant through augmented assignments and floor division, and see a mutation that the recomputed obligations refuse.

## The component and its provenance

CPython 3.12 ships `Lib/encodings/punycode.py`. Its `adapt` function implements the bias adaptation of RFC 3492 §6.1. The call chain is concrete: `encodings.idna.ToASCII` calls `label.encode("punycode")`; the punycode codec calls `punycode_encode`; `punycode_encode` calls `adapt` for each delta it emits.

The installed function has no type annotations. Logos binds statements to annotated parameters, so `examples/punycode_adapt.py` carries a copy with the annotations added and the executable body unchanged. The block below is that file; the page writes it and imports it. The copy is not a rewrite: CI compares its code object with the one the interpreter installed. The comparison covers the bytecode, constants, names, local names and flags, but not the annotations, which do not affect execution.

```python {export=examples/punycode_adapt.py}
# Body of encodings.punycode.adapt from CPython 3.12.3, Lib/encodings/punycode.py.
# Only the type annotations are added; the executable statements are unchanged.
def adapt(delta: int, first: int, numchars: int) -> int:
    if first:
        delta //= 700
    else:
        delta //= 2
    delta += delta // numchars
    divisions = 0
    while delta > 455:
        delta = delta // 35
        divisions += 36
    bias = divisions + (36 * delta // (delta + 38))
    return bias
```

`first` is a truth flag in the original call (`points == 0`). Python treats a nonzero integer as true, so the contract quantifies over every integer and the translation uses `first != 0`. Nothing in the proof depends on `first` being exactly zero or one.

## The assumptions and the contract

The function assumes two things. `delta` must not be negative, because the divisions and the final numerator are meant to produce a bias. `numchars` must be positive, because the body divides by it. The contract makes both assumptions explicit; it does not hide them in a test.

```python {run}
import logos
from logos.expr import Lit, Var
from examples.punycode_adapt import adapt

@logos.theorem(about=adapt)
def adapt_bias_nonnegative(delta, first, numchars, *, result):
    divisions = Var("divisions", int)
    return logos.program_contract(
        requires=(Lit(0) <= delta) & (Lit(0) < numchars),
        ensures=(Lit(0) <= result),
        invariant=(Lit(0) <= delta) & (Lit(0) <= divisions),
        variant=delta,
    )
```

The invariant is one line because the function keeps one scalar and one counter. `delta` starts non-negative by the precondition and is only ever divided or increased by a non-negative quotient. `divisions` starts at zero and only ever receives `36`. The variant is `delta` itself: the loop divides it by 35, and a positive integer divided by 35 is strictly smaller.

The final expression is

$$\text{bias} = \text{divisions} + \left\lfloor \frac{36 \cdot \text{delta}}{\text{delta} + 38} \right\rfloor.$$

Both summands are non-negative under the invariant: `divisions` by the invariant, and the quotient because its numerator is a product of non-negative integers and its denominator is positive.

## The floor-division laws

Three small core laws make the floor divisions visible to the checker. They are checker-owned, not custom axioms:

| Law | Statement |
| --- | --- |
| `mul_nonneg` | `0 <= a` and `0 <= b` give `0 <= a * b` |
| `div_nonneg` | `0 <= a` and `0 < b` give `0 <= a // b` |
| `div_lt` | `0 < a` and `1 < b` give `a // b < a` |

The soundness argument is the usual one for floor division. If $a \ge 0$ and $b > 0$, the quotient is at least zero. If $a > 0$ and $b > 1$, then $a // b \le a/2 < a$. The checker owns the schemas and recomputes every instance from the law ID and its integer arguments; the Python side only supplies the substitution.

This is the authoring improvement the production contract needed. Before it, the proof search could see `// 2` in the midpoint laws but not a general floor division. The new laws are general over integer terms, and the proof search uses them for products and quotients wherever they appear in a verification condition.

## Check the contract

The checker recomputes four loop obligations and the main condition. The `main` condition covers the two pre-loop branches (`if first` and its `else`) and the entry to the loop. The `preserve` obligation covers the loop body. The `exit` obligation is the final bias expression. The variant obligations are the non-negativity and strict decrease of `delta`.

```python {run continue}
adapt_bias_nonnegative.check()
print("adapt_bias_nonnegative:", adapt_bias_nonnegative.certified)
print("obligations:", ", ".join(adapt_bias_nonnegative.program.obligations))
logos.export_proof(adapt_bias_nonnegative, "adapt.logos")
print("certificate: adapt.logos")
```

The certificate is checked without Python:

```bash
logos check --strict adapt.logos
```

The expected last line is `Verified with 0 custom axioms`. The statement is

$$\forall \delta, f, n, r.\ \ 0 \le \delta \rightarrow 0 < n \rightarrow
  \bigl(r = \operatorname{adapt}(\delta, f, n) \rightarrow 0 \le r\bigr).$$

The `first` argument is universally quantified, as it should be: the bias property does not depend on which branch the flag selects.

## What the certificate binds, and what it does not

The source binding is the point of this chapter. The theorem stores the translated program and re-reads the module on every check, export and receipt read. If the file changes after the theorem is declared, the translation no longer matches and the check raises a binding error instead of certifying stale code.

The CI regression does three things:

1. It renders the chapter, which writes `examples/punycode_adapt.py`, and compares that module's code object with `encodings.punycode.adapt` from the interpreter that runs the book. The comparison is bytecode and constants, not the annotations.
2. It checks the exported certificate with `logos check --strict` and requires zero custom axioms.
3. It mutates the body and requires the proof to fail.

The limits are as important as the claim:

- The verified subject is the Python body of `adapt`, not the C fast path of the interpreter and not the `idna` codec around it.
- The postcondition is non-negativity and termination. It is not a proof that the encoded string is RFC-conformant.
- `first` is any integer. The Python truthiness rule makes that faithful, but a caller that passes a value other than a boolean is outside the intended use even though the contract covers it.
- The copy is annotated. The executable body is compared with the interpreter's; the annotations are the contract, not part of CPython's source.

On a different Python minor version the code object may change. That is a feature, not a nuisance: the drift test fails, and the book must re-copy and re-check the function rather than silently verifying an old body.

## When a step fails

Change the last assignment from

```python
bias = divisions + (36 * delta // (delta + 38))
```

to

```python
bias = divisions - 1
```

The loop still terminates and the invariant still holds, but the exit condition no longer implies `0 <= result`. The checker refuses the `exit` obligation:

```text
logos.proofs.ProofSearchError: loop0.exit: cannot prove order atom 0 <= divisions - 1
```

The message points at the expression that lost its lower bound. It does not say that the function is wrong for every input; it says that the invariant and the loop condition do not establish the postcondition. The repair is either to restore the non-negative expression or to strengthen the invariant with a lower bound on `divisions` that survives the branch, which the original body does not need.

The second failure is the source binding. Edit `examples/punycode_adapt.py` after the theorem is declared, for example by changing `455` to `456`, and call `adapt_bias_nonnegative.check()` again. The theorem re-reads the module, sees that the fresh code object no longer matches the imported function, and raises `source of 'adapt' in ... does not match the imported code object; the module is stale or the file changed after import`. The certificate is not written. A proof about a body that no longer exists is not a proof about the installed library.

## Exit exercise

Prove a stronger bound: for `delta >= 0` and `numchars > 0`, `adapt` returns a bias of at least 72 when `delta` is at least 72. Is that true for the body as written? Evaluate the `first` branch at `delta = 72`, then the `else` branch. If the bound is not true, state the counterexample and explain which branch breaks it. If it is true, which invariant conjunct must be strengthened, and does the variant still decrease?

As a second exercise, run the same contract against a second maintained function in the fragment. A good candidate is another pure-Python standard-library helper with one loop and integer parameters. Before you write the theorem, list its assumptions, its loop variant and the one postcondition you can actually justify. If the function needs list mutation, early returns or a function call, say so and stop: the fragment does not cover it, and the right answer is to report the limit rather than weaken the claim.
