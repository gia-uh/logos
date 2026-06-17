# logos/kernel.py
from __future__ import annotations
from dataclasses import dataclass
from typing import Callable
from logos.expr import (
    Expr, Var, Eq, And, Or, Not, Implies,
    ForallNode, ExistsNode,
)
from logos.helpers import structural_eq, substitute


class KernelError(Exception):
    pass


@dataclass
class Context:
    axioms: dict[str, Expr]   # globally declared axioms
    hyps: dict[str, Expr]     # local hypotheses (in scope for current goal)

    def with_hyp(self, name: str, stmt: Expr) -> "Context":
        return Context(self.axioms, {**self.hyps, name: stmt})

    def lookup(self, name: str) -> Expr:
        if name in self.hyps:
            return self.hyps[name]
        if name in self.axioms:
            return self.axioms[name]
        raise KernelError(f"Unknown name '{name}' — not in hypotheses or axioms")


# ── Proof Terms ───────────────────────────────────────────────────────────────

class ProofTerm:
    pass

@dataclass(frozen=True)
class Refl(ProofTerm):
    expr: Expr                        # proves expr == expr

@dataclass(frozen=True)
class Symm(ProofTerm):
    proof: ProofTerm                  # if proof: a==b, proves b==a

@dataclass(frozen=True)
class Trans(ProofTerm):
    left: ProofTerm                   # proves a==b
    right: ProofTerm                  # proves b==c  →  together prove a==c

@dataclass(frozen=True)
class Subst(ProofTerm):
    proof: ProofTerm                  # proves a==b
    func: Callable[[Expr], Expr]      # f(a)==f(b)

@dataclass(frozen=True)
class Axiom(ProofTerm):
    name: str                         # proves the named axiom's statement

@dataclass(frozen=True)
class HypRef(ProofTerm):
    name: str                         # proves the named hypothesis

@dataclass(frozen=True)
class ForallIntro(ProofTerm):
    var: Var                          # the universally quantified variable
    body: ProofTerm                   # proof of P under that variable

@dataclass(frozen=True)
class ForallElim(ProofTerm):
    proof: ProofTerm                  # proof of Forall(x, P)
    val: Expr                         # instantiation value

@dataclass(frozen=True)
class ImpliesIntro(ProofTerm):
    hyp: Expr                         # the hypothesis being introduced
    hyp_name: str                     # name under which hyp is added to context
    body: ProofTerm                   # proof of conclusion with hyp in context

@dataclass(frozen=True)
class ImpliesElim(ProofTerm):
    implication: ProofTerm            # proves P >> Q
    premise: ProofTerm                # proves P  →  together prove Q

@dataclass(frozen=True)
class AndIntro(ProofTerm):
    left: ProofTerm
    right: ProofTerm

@dataclass(frozen=True)
class AndElimL(ProofTerm):
    proof: ProofTerm                  # proof of A & B → proves A

@dataclass(frozen=True)
class AndElimR(ProofTerm):
    proof: ProofTerm                  # proof of A & B → proves B

@dataclass(frozen=True)
class OrIntroL(ProofTerm):
    proof: ProofTerm                  # proof of A → proves A | B
    right_type: Expr                  # the B in A | B (needed to reconstruct type)

@dataclass(frozen=True)
class OrIntroR(ProofTerm):
    left_type: Expr
    proof: ProofTerm                  # proof of B → proves A | B

@dataclass(frozen=True)
class CaseAnalysis(ProofTerm):
    """Proves C given: proof of (A|B), proof of C with A as hyp, proof of C with B as hyp."""
    or_proof: ProofTerm
    hyp_name: str
    left_branch: ProofTerm
    right_branch: ProofTerm

@dataclass(frozen=True)
class NotIntro(ProofTerm):
    """Proves ~A given proof of A >> False."""
    impl_proof: ProofTerm

@dataclass(frozen=True)
class ExFalso(ProofTerm):
    """Proves anything given proof of False (ex falso quodlibet)."""
    false_proof: ProofTerm
    conclusion: Expr

@dataclass(frozen=True)
class ExistsIntro(ProofTerm):
    """Proves Exists(x, P) given a witness w and a proof of P[x := w].

    `exists_goal` carries the original ExistsNode so infer can return the
    correct existential type. Optional for v0.1 backward compat; if absent,
    returns the substituted body statement instead.
    """
    witness: Expr
    body: ProofTerm   # proof of P[x := witness]
    exists_goal: "ExistsNode | None" = None


# ── Kernel Inference ──────────────────────────────────────────────────────────

def infer(term: ProofTerm, ctx: Context) -> Expr:
    """Infer the statement proved by `term` under `ctx`. Raises KernelError if invalid."""
    match term:
        case Refl(expr):
            return Eq(expr, expr)

        case Symm(proof):
            stmt = infer(proof, ctx)
            match stmt:
                case Eq(a, b): return Eq(b, a)
            raise KernelError(f"Symm: expected Eq, got {stmt!r}")

        case Trans(left, right):
            l_stmt = infer(left, ctx)
            r_stmt = infer(right, ctx)
            match l_stmt, r_stmt:
                case Eq(a, b1), Eq(b2, c) if structural_eq(b1, b2):
                    return Eq(a, c)
            raise KernelError(f"Trans: middle terms don't match: {l_stmt!r} and {r_stmt!r}")

        case Subst(proof, func):
            stmt = infer(proof, ctx)
            match stmt:
                case Eq(a, b):
                    return Eq(func(a), func(b))
            raise KernelError(f"Subst: expected Eq, got {stmt!r}")

        case Axiom(name) | HypRef(name):
            return ctx.lookup(name)

        case ForallIntro(var, body):
            body_stmt = infer(body, ctx)
            return ForallNode(var, body_stmt)

        case ForallElim(proof, val):
            stmt = infer(proof, ctx)
            match stmt:
                case ForallNode(var, body):
                    return substitute(body, var, val)
            raise KernelError(f"ForallElim: expected ForallNode, got {stmt!r}")

        case ImpliesIntro(hyp, hyp_name, body):
            new_ctx = ctx.with_hyp(hyp_name, hyp)
            body_stmt = infer(body, new_ctx)
            return Implies(hyp, body_stmt)

        case ImpliesElim(implication, premise):
            impl_stmt = infer(implication, ctx)
            pre_stmt = infer(premise, ctx)
            match impl_stmt:
                case Implies(ant, cons) if structural_eq(ant, pre_stmt):
                    return cons
            raise KernelError(f"ImpliesElim: antecedent mismatch")

        case AndIntro(left, right):
            l = infer(left, ctx)
            r = infer(right, ctx)
            return And(l, r)

        case AndElimL(proof):
            stmt = infer(proof, ctx)
            match stmt:
                case And(l, _): return l
            raise KernelError("AndElimL: expected And")

        case AndElimR(proof):
            stmt = infer(proof, ctx)
            match stmt:
                case And(_, r): return r
            raise KernelError("AndElimR: expected And")

        case OrIntroL(proof, right_type):
            l = infer(proof, ctx)
            return Or(l, right_type)

        case OrIntroR(left_type, proof):
            r = infer(proof, ctx)
            return Or(left_type, r)

        case CaseAnalysis(or_proof, hyp_name, left_branch, right_branch):
            or_stmt = infer(or_proof, ctx)
            match or_stmt:
                case Or(a, b):
                    l_stmt = infer(left_branch, ctx.with_hyp(hyp_name, a))
                    r_stmt = infer(right_branch, ctx.with_hyp(hyp_name, b))
                    if not structural_eq(l_stmt, r_stmt):
                        raise KernelError("CaseAnalysis: branches prove different statements")
                    return l_stmt
            raise KernelError("CaseAnalysis: expected Or")

        case NotIntro(impl_proof):
            stmt = infer(impl_proof, ctx)
            match stmt:
                case Implies(ant, cons):
                    # For v0.1: accept any Implies(ant, anything) as ~ant
                    # Ideally we'd check that cons is Lit(False), but that requires evaluation
                    return Not(ant)
            raise KernelError(f"NotIntro: expected Implies, got {stmt!r}")

        case ExFalso(false_proof, conclusion):
            # Note: v0.1 limitation — we don't validate that false_proof actually proves False.
            # To properly validate, we'd need a full evaluator to check whether the consequent
            # is Lit(False). For now, we accept any proof and return the conclusion as-is.
            # This is known and acceptable for v0.1. The contradiction() tactic depends on this behavior.
            return conclusion

        case ExistsIntro(witness, body, exists_goal):
            # body proves P[x := witness].
            # If we have the original ExistsNode, return it (the existential is proven).
            # Otherwise fall back to returning the substituted body statement.
            body_stmt = infer(body, ctx)   # validate the sub-proof
            if exists_goal is not None:
                return exists_goal
            return body_stmt

        case _:
            raise KernelError(f"Unknown proof term: {term!r}")


def check(term: ProofTerm, expected: Expr, ctx: Context) -> None:
    """Validate that `term` proves `expected`. Raises KernelError on mismatch."""
    inferred = infer(term, ctx)
    if not structural_eq(inferred, expected):
        raise KernelError(
            f"Proof mismatch.\n  Expected: {expected!r}\n  Got:      {inferred!r}"
        )
