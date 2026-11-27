# logos/kernel.py
from __future__ import annotations
from dataclasses import dataclass
from typing import TYPE_CHECKING, Callable
from logos.expr import (
    Expr, Lit, Var, App, Eq, And, Or, Not, Implies, Lt,
    ForallNode, ExistsNode,
)
from logos.helpers import free_vars, structural_eq, substitute, substitute_symbols

if TYPE_CHECKING:
    from logos.theorem import Axiom as AuthorAxiom, Theorem


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
class CoreLaw(ProofTerm):
    id: str
    args: tuple[Expr, ...]


@dataclass(frozen=True)
class Congr(ProofTerm):
    var: Var
    context: Expr
    proof: ProofTerm


@dataclass(frozen=True)
class Block(ProofTerm):
    steps: tuple[ProofTerm, ...]
    result: int


@dataclass(frozen=True)
class StepRef(ProofTerm):
    index: int


@dataclass(frozen=True)
class Subst(ProofTerm):
    proof: ProofTerm                  # proves a==b
    func: Callable[[Expr], Expr]      # f(a)==f(b)

@dataclass(frozen=True)
class Axiom(ProofTerm):
    name: str                         # proves the named axiom's statement

@dataclass(frozen=True)
class AxiomRef(ProofTerm):
    axiom: AuthorAxiom


@dataclass(frozen=True)
class TheoremRef(ProofTerm):
    theorem: Theorem


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
class NotElim(ProofTerm):
    """Proves False from proofs of ~A and A."""
    negation: ProofTerm
    premise: ProofTerm

@dataclass(frozen=True)
class ExFalso(ProofTerm):
    """Proves anything given proof of False (ex falso quodlibet)."""
    false_proof: ProofTerm
    conclusion: Expr

@dataclass(frozen=True)
class ExistsIntro(ProofTerm):
    """Proves Exists(x, P) given a witness w and a proof of P[x := w].

    `exists_goal` carries the existential statement. Portable verification
    checks the witness sort and substitution in the active variable scope.
    """
    witness: Expr
    body: ProofTerm   # proof of P[x := witness]
    exists_goal: "ExistsNode | None" = None

@dataclass(frozen=True)
class ExistsElim(ProofTerm):
    """Proves C from Exists(x, P) and a proof of C under P[x := var].

    ``var`` is the eigenvariable and must not escape the conclusion or any
    enclosing hypothesis. ``hyp_name`` names the local assumption
    ``P[x := var]`` inside ``body``.
    """
    proof: ProofTerm          # proves Exists(x, P)
    var: Var                  # fresh eigenvariable
    hyp_name: str             # local name of P[var]
    body: ProofTerm           # proves C using var and the hypothesis

@dataclass(frozen=True)
class EqSubst(ProofTerm):
    """Leibniz elimination: from a == b and P[a], derive P[b].

    ``template`` is the proposition P with ``var`` free; ``proof`` proves
    the instance P[a] for the left side of ``equality``.
    """
    equality: ProofTerm       # proves a == b
    var: Var                  # template variable
    template: Expr            # P with var free
    proof: ProofTerm          # proves P[a]

@dataclass(frozen=True)
class Induction(ProofTerm):
    """Ordinary induction on integers at or above ``lower``.

    ``base`` proves P[lower]. ``step`` proves, for an arbitrary k with
    lower <= k, that P[k] implies P[k + 1]. The conclusion is that P holds
    for every integer at or above ``lower``.
    """
    lower: Expr
    var: Var                  # induction variable, free in predicate
    predicate: Expr           # P
    base: ProofTerm
    step: ProofTerm

@dataclass(frozen=True)
class Least(ProofTerm):
    """Least element of a nonempty integer predicate at or above ``lower``.

    ``nonempty`` proves Exists(m, lower <= m & P[m]). The conclusion adds
    minimality: no smaller admissible integer satisfies P.
    """
    lower: Expr
    var: Var
    predicate: Expr
    nonempty: ProofTerm

@dataclass(frozen=True)
class RecursorBase(ProofTerm):
    """The base equation f(0) = base of a primitive-recursive function."""
    function: object

@dataclass(frozen=True)
class RecursorStep(ProofTerm):
    """The step equation f(k + 1) = step(k, f(k)) for k >= 0."""
    function: object
    argument: Expr
    proof: ProofTerm          # proves not (argument < 0)


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

        case AxiomRef(axiom):
            return ctx.lookup(axiom.name)

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
            match infer(impl_proof, ctx):
                case Implies(ant, Lit(value)) if value is False:
                    return Not(ant)
            raise KernelError("NotIntro: expected an implication to False")

        case NotElim(negation, premise):
            given = infer(premise, ctx)
            match infer(negation, ctx):
                case Not(operand) if structural_eq(operand, given):
                    return Lit(False)
            raise KernelError("NotElim: expected a negation and its matching premise")

        case ExFalso(false_proof, conclusion):
            match infer(false_proof, ctx):
                case Lit(value) if value is False:
                    return conclusion
            raise KernelError("ExFalso: expected a proof of False")

        case ExistsIntro(witness, proof, ExistsNode(var, body) as goal):
            check(proof, substitute_symbols(body, {id(var): witness}), ctx)
            return goal

        case ExistsIntro():
            raise KernelError("ExistsIntro: expected an existential goal")

        case ExistsElim(proof, var, hyp_name, body):
            stmt = infer(proof, ctx)
            match stmt:
                case ExistsNode(bound, predicate):
                    if not isinstance(var, Var):
                        raise KernelError("ExistsElim: eigenvariable must be a Var")
                    if var.type is not bound.type:
                        raise KernelError("ExistsElim: eigenvariable sort does not match the binder")
                    occupied = set()
                    for outer in list(ctx.hyps.values()) + list(ctx.axioms.values()):
                        occupied |= free_vars(outer)
                    if var.name in occupied:
                        raise KernelError(
                            f"ExistsElim: eigenvariable {var.name!r} already occurs in the context"
                        )
                    assumption = substitute_symbols(predicate, {id(bound): var})
                    conclusion = infer(body, ctx.with_hyp(hyp_name, assumption))
                    if var.name in free_vars(conclusion):
                        raise KernelError(
                            f"ExistsElim: eigenvariable {var.name!r} escapes the conclusion"
                        )
                    return conclusion
            raise KernelError(f"ExistsElim: expected an existential premise, got {stmt!r}")

        case EqSubst(equality, var, template, proof):
            stmt = infer(equality, ctx)
            match stmt:
                case Eq(left, right):
                    expected = substitute_symbols(template, {id(var): left})
                    check(proof, expected, ctx)
                    return substitute_symbols(template, {id(var): right})
            raise KernelError(f"EqSubst: expected an equality, got {stmt!r}")

        case Induction(lower, var, predicate, base, step):
            if not isinstance(var, Var):
                raise KernelError("Induction: induction variable must be a Var")
            at_lower = substitute_symbols(predicate, {id(var): lower})
            check(base, at_lower, ctx)
            k = Var(var.name, var.type)
            here = substitute_symbols(predicate, {id(var): k})
            next_ = substitute_symbols(predicate, {id(var): k + 1})
            step_expected = ForallNode(
                k, Implies(Not(Lt(k, lower)), Implies(here, next_))
            )
            check(step, step_expected, ctx)
            return ForallNode(
                k, Implies(Not(Lt(k, lower)), substitute_symbols(predicate, {id(var): k}))
            )

        case Least(lower, var, predicate, nonempty):
            if not isinstance(var, Var):
                raise KernelError("Least: witness variable must be a Var")
            m = Var(var.name, var.type)
            k = Var(var.name + "_smaller", var.type)
            membership = And(Not(Lt(m, lower)), substitute_symbols(predicate, {id(var): m}))
            check(nonempty, ExistsNode(m, membership), ctx)
            minimal = ForallNode(
                k,
                Implies(
                    And(Not(Lt(k, lower)), Lt(k, m)),
                    Not(substitute_symbols(predicate, {id(var): k})),
                ),
            )
            return ExistsNode(m, And(membership, minimal))

        case RecursorBase(function):
            if getattr(function, "recursor", None) is None:
                raise KernelError("RecursorBase: function is not recursive")
            base, _, _ = function.recursor
            return Eq(App(function.name, [Lit(0)], function), base)

        case RecursorStep(function, argument, proof):
            if getattr(function, "recursor", None) is None:
                raise KernelError("RecursorStep: function is not recursive")
            _, step, previous = function.recursor
            check(proof, Not(Lt(argument, Lit(0))), ctx)
            value = App(function.name, [argument], function)
            instantiated = substitute_symbols(
                step,
                {id(function.params[0]): argument, id(previous): value},
            )
            return Eq(App(function.name, [argument + 1], function), instantiated)

        case _:
            raise KernelError(f"Unknown proof term: {term!r}")


def check(term: ProofTerm, expected: Expr, ctx: Context) -> None:
    """Validate that `term` proves `expected`. Raises KernelError on mismatch."""
    inferred = infer(term, ctx)
    if not structural_eq(inferred, expected):
        raise KernelError(
            f"Proof mismatch.\n  Expected: {expected!r}\n  Got:      {inferred!r}"
        )
