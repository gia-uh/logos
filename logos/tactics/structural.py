# logos/tactics/structural.py
from logos.expr import (
    Expr, Var, ForallNode, ExistsNode, And, Or, Not, Implies,
)
from logos.goal import Goal
from logos.kernel import (
    ProofTerm, KernelError,
    Refl, HypRef, ForallIntro, ForallElim,
    ImpliesIntro, ImpliesElim,
    AndIntro, AndElimL, AndElimR,
    OrIntroL, OrIntroR, CaseAnalysis, ExFalso,
    ExistsIntro, Axiom as KernelAxiom,
)
from logos.helpers import substitute, structural_eq, try_unify
from logos.runner import TacticFailed


def intro(*names: str):
    def tactic(goal: Goal):
        stmt = goal.statement
        ctx = dict(goal.context)
        steps = []   # track what was introduced for compose

        for name in names:
            match stmt:
                case ForallNode(var, body):
                    new_var = Var(name, var.type)
                    ctx[name] = new_var   # note the var in context
                    stmt = substitute(body, var, new_var)
                    steps.append(("forall", name, new_var))
                case Implies(ant, cons):
                    ctx[name] = ant
                    stmt = cons
                    steps.append(("implies", name, ant))
                case _:
                    raise TacticFailed(f"intro '{name}': cannot introduce into {stmt!r}")

        new_goal = Goal(ctx, stmt)

        def compose(proofs: list[ProofTerm]) -> ProofTerm:
            [body_proof] = proofs
            result = body_proof
            for kind, name, info in reversed(steps):
                if kind == "forall":
                    result = ForallIntro(info, result)
                else:
                    result = ImpliesIntro(info, name, result)
            return result

        return [new_goal], compose
    return tactic


def assumption():
    def tactic(goal: Goal) -> ProofTerm:
        for name, hyp in goal.context.items():
            if structural_eq(hyp, goal.statement):
                return HypRef(name)
        raise TacticFailed(f"assumption: {goal.statement!r} not in context")
    return tactic


def exact(term: ProofTerm):
    def tactic(goal: Goal) -> ProofTerm:
        return term
    return tactic


def apply(ref):
    """Apply a theorem/axiom/hypothesis to close or transform the goal.

    ref can be:
    - str: local hypothesis name only
    - Axiom or Theorem object: use ref.statement directly
    """
    def tactic(goal: Goal):
        from logos.theorem import Theorem, Axiom as LogosAxiom, check as logos_check, LogosProofError

        if isinstance(ref, str):
            # Local hypothesis only
            if ref not in goal.context:
                raise TacticFailed(f"apply '{ref}': not in local context")
            stmt = goal.context[ref]
            proof_base = HypRef(ref)
        elif isinstance(ref, (LogosAxiom, Theorem)):
            # Axiom or Theorem object — auto-check uncertified theorems
            if isinstance(ref, Theorem) and not ref.certified:
                try:
                    logos_check(ref)
                except LogosProofError as e:
                    raise TacticFailed(f"apply: dependency '{ref.name}' failed: {e}") from e
            stmt = ref.statement
            proof_base = KernelAxiom(ref.name)
        else:
            raise TacticFailed(f"apply: expected str, Axiom, or Theorem, got {type(ref).__name__!r}")

        # Direct structural match
        if structural_eq(stmt, goal.statement):
            return proof_base

        # Strip forall binders and unify
        flex_ordered = []
        inner = stmt
        while isinstance(inner, ForallNode):
            flex_ordered.append(inner.var)
            inner = inner.body

        if not flex_ordered:
            raise TacticFailed(
                f"apply '{getattr(ref, 'name', ref)}': "
                f"{stmt!r} does not match goal {goal.statement!r}"
            )

        flex_names = {v.name for v in flex_ordered}
        sub = try_unify(inner, goal.statement, flex_names)
        if sub is None:
            raise TacticFailed(
                f"apply '{getattr(ref, 'name', ref)}': "
                f"cannot unify {inner!r} with {goal.statement!r}"
            )

        result = proof_base
        for var in flex_ordered:
            if var.name not in sub:
                raise TacticFailed(
                    f"apply '{getattr(ref, 'name', ref)}': "
                    f"unconstrained variable {var.name!r}"
                )
            result = ForallElim(result, sub[var.name])
        return result
    return tactic


def split():
    def tactic(goal: Goal):
        match goal.statement:
            case And(left, right):
                return (
                    [Goal(goal.context, left), Goal(goal.context, right)],
                    lambda ps: AndIntro(ps[0], ps[1])
                )
            case _:
                raise TacticFailed(f"split: expected A & B, got {goal.statement!r}")
    return tactic


def left(right_type: Expr):
    def tactic(goal: Goal):
        match goal.statement:
            case Or(l, _):
                return [Goal(goal.context, l)], lambda ps: OrIntroL(ps[0], right_type)
            case _:
                raise TacticFailed(f"left: expected A | B, got {goal.statement!r}")
    return tactic


def right(left_type: Expr):
    def tactic(goal: Goal):
        match goal.statement:
            case Or(_, r):
                return [Goal(goal.context, r)], lambda ps: OrIntroR(left_type, ps[0])
            case _:
                raise TacticFailed(f"right: expected A | B, got {goal.statement!r}")
    return tactic


def witness(val: Expr):
    def tactic(goal: Goal):
        match goal.statement:
            case ExistsNode(var, body):
                new_stmt = substitute(body, var, val)
                exists_goal = goal.statement
                return (
                    [Goal(goal.context, new_stmt)],
                    lambda ps: ExistsIntro(val, ps[0], exists_goal)
                )
            case _:
                raise TacticFailed(f"witness: expected Exists, got {goal.statement!r}")
    return tactic


def cases(hyp_name: str, case_name: str = "h"):
    """Case analysis on a hypothesis A | B in context."""
    def tactic(goal: Goal):
        ctx_dict = goal.context
        if hyp_name not in ctx_dict:
            raise TacticFailed(f"cases '{hyp_name}': not in context")
        stmt = ctx_dict[hyp_name]
        match stmt:
            case Or(left, right):
                left_goal = goal.with_hyp(case_name, left)
                right_goal = goal.with_hyp(case_name, right)
                def compose(proofs):
                    return CaseAnalysis(HypRef(hyp_name), case_name, proofs[0], proofs[1])
                return [left_goal, right_goal], compose
            case _:
                raise TacticFailed(f"cases '{hyp_name}': expected A | B, got {stmt!r}")
    return tactic


def contradiction():
    def tactic(goal: Goal) -> ProofTerm:
        stmts = list(goal.context.values())
        names = list(goal.context.keys())
        for i, s in enumerate(stmts):
            for j, t in enumerate(stmts):
                if i != j and (structural_eq(s, Not(t)) or structural_eq(Not(s), t)):
                    # We have P and ~P in context
                    return ExFalso(HypRef(names[i]), goal.statement)
        raise TacticFailed("contradiction: no contradictory hypotheses found")
    return tactic
