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

Start at the last assignment. What facts at loop exit make each summand of `divisions + (36 * delta // (delta + 38))` non-negative? The first summand needs `divisions >= 0`. For the second, `delta >= 0` gives a non-negative numerator and a denominator of at least 38. We can aim to keep these two lower bounds at every loop head, including the last one when the guard is false.

Before writing the contract, check that the bounds hold even if the loop runs zero times. Assume the input `delta >= 0` and `numchars > 0`. Both branches divide by a positive constant, and `delta += delta // numchars` adds a non-negative quotient. Thus the loop starts with `delta >= 0` and `divisions = 0`. Each iteration keeps the bounds by dividing `delta` by 35 and adding 36 to `divisions`.

To prove termination, look for a non-negative integer that gets smaller. Before an iteration, the guard gives `delta > 455`, so `delta // 35 < delta`. The invariant already gives the lower bound for using `delta` itself as the variant.

In Logos, the parameters and `result` are supplied to the theorem. Name the loop local `divisions` with `Var` so the invariant refers to that local at the loop head.

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

## The arithmetic behind the obligations

| Checker law | What it gives | Where to use it |
| --- | --- | --- |
| `mul_nonneg` | `0 <= a` and `0 <= b` imply `0 <= a * b` | At exit, show that `36 * delta` is non-negative. |
| `div_nonneg` | `0 <= a` and `0 < b` imply `0 <= a // b` | At entry, justify the quotients in both branches and the one by `numchars`. Use it again for preservation with divisor 35 and at exit with denominator `delta + 38`. |
| `div_lt` | `0 < a` and `1 < b` imply `a // b < a` | Under the guard, show that `delta // 35` decreases the variant. |

The checker owns these integer laws. Python proof search chooses the law and supplies its integer arguments. The checker reconstructs the instance from those arguments and checks its premises.

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

The checker reports `Verified with 0 custom axioms`. The statement is

$$\forall \delta, f, n, r.\ \ 0 \le \delta \rightarrow 0 < n \rightarrow
  \bigl(r = \operatorname{adapt}(\delta, f, n) \rightarrow 0 \le r\bigr).$$

The `first` argument is universally quantified, as it should be: the bias property does not depend on which branch the flag selects.

## What the certificate binds, and what it does not

The source binding is the point of this chapter. The theorem stores the translated program and re-reads the module on check and export, and when validating a cached receipt. If the file changes after the theorem is declared, the translation no longer matches and check and export raise a binding error. Reading the receipt of a previously certified theorem returns `None`.

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

### Declare a theorem against an edited body

In a scratch directory, copy the function listing into `examples/punycode_adapt.py` and the theorem declaration (the block ending with `variant=delta`) into `prove_adapt.py`. Keep the import in that declaration. Before importing either file, replace the last assignment in the copied function with:

```python
bias = divisions - 1
```

Predict what happens with input `delta=0` and `numchars=1`. Then start a fresh Python process from the scratch directory, so the import and theorem declaration both see the edited body.

```bash
python -B -i prove_adapt.py
```

At the prompt, run:

```python
print(adapt(0, 0, 1), adapt(0, 1, 1))
adapt_bias_nonnegative.check()
```

The output is `-1 -1`: the loop is skipped and `divisions` is zero. The source binding succeeds, and proof search reports a failed exit obligation. The diagnostic starts with:

```text
logos.proofs.ProofSearchError: loop0.exit: cannot prove order atom 0 <= divisions - 1
```

The invariant still holds, but the postcondition is false for allowed inputs on the changed body. An invariant that required `divisions >= 1` would already fail at loop entry. Restore the original bias expression to keep the original claim.

### Edit the source of an existing theorem

Exit Python, restore the copied function, then start `python -B -i prove_adapt.py` again. Run `adapt_bias_nonnegative.check()` and check that `adapt_bias_nonnegative.certified` is true.

Leave that process open. In your editor, change only the loop guard in the copy from `delta > 455` to `delta > 456`. Save the file, then call `adapt_bias_nonnegative.check()` again in the same process. The binding diagnostic names the source file and includes this message:

```text
does not match the imported code object; the module is stale
```

In that process, `logos.export_proof(adapt_bias_nonnegative, "stale.logos")` raises the same binding error before writing a file. Reading `adapt_bias_nonnegative.receipt` yields `None`. To check a contract on the new body, start a fresh process and declare it against the new import. To check the original body, restore the source.

## Exit exercise

1. Consider the claim that `adapt` returns at least 72 whenever the input `delta >= 72` and `numchars > 0`. Trace `adapt(72, 1, 1)` and `adapt(72, 0, 1)` on the original body. For each call, record `delta` after the branch and after augmentation, whether the loop runs, and the result. Decide whether the claim holds.
2. Construct and check a total-correctness contract for the small halving loop below. Assume `value >= 0` and claim that the result is non-negative. Work backward from the return. Choose an invariant and a variant, then justify entry, preservation, exit and strict decrease before writing the theorem.

```python {export=examples/halving_total.py}
def halving_total(value: int) -> int:
    total = 0
    while value > 0:
        total += value
        value //= 2
    return total
```

## Instructor solutions

For the first trace, `72 // 700` is 0 and augmentation leaves it at 0. For the second, `72 // 2` is 36 and augmentation takes it to 72. Both skip the loop, so the results are `0` and `2592 // 110 = 23`, respectively. Each call refutes the claim.

```python {run continue}
assert (adapt(72, 1, 1), adapt(72, 0, 1)) == (0, 23)
```

The return needs `total >= 0`. It starts at zero and increases because the guard gives `value > 0`. Use `value` as the variant. It starts non-negative, halving keeps it non-negative, and the guard gives strict decrease. Keep both bounds in the invariant. At exit, `total >= 0` proves the result.

```python {run continue}
from examples.halving_total import halving_total

@logos.theorem(about=halving_total)
def halving_total_nonnegative(value, *, result):
    total = Var("total", int)
    return logos.program_contract(
        requires=Lit(0) <= value,
        ensures=Lit(0) <= result,
        invariant=(Lit(0) <= total) & (Lit(0) <= value),
        variant=value,
    )

halving_total_nonnegative.check()
print("halving_total_nonnegative:", halving_total_nonnegative.certified)
```
