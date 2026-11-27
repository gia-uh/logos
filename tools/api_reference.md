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

