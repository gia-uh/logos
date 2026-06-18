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
    """Case analysis on a hypothesis A | B in context.

    Removes the split hypothesis from subgoal contexts to prevent re-splitting.
    """
    def tactic(goal: Goal):
        ctx_dict = goal.context
        if hyp_name not in ctx_dict:
            raise TacticFailed(f"cases '{hyp_name}': not in context")
        stmt = ctx_dict[hyp_name]
        match stmt:
            case Or(left, right):
                rest = {k: v for k, v in ctx_dict.items() if k != hyp_name}
                left_goal  = Goal({**rest, case_name: left},  goal.statement)
                right_goal = Goal({**rest, case_name: right}, goal.statement)
                def compose(proofs):
                    return CaseAnalysis(HypRef(hyp_name), case_name, proofs[0], proofs[1])
                return [left_goal, right_goal], compose
            case _:
                raise TacticFailed(f"cases '{hyp_name}': expected A | B, got {stmt!r}")
    return tactic


def have(new_name: str, impl_hyp: str, ant_hyp: str):
    """Forward modus ponens: from impl_hyp: A→B and ant_hyp: A, add new_name: B."""
    def tactic(goal: Goal):
        if impl_hyp not in goal.context:
            raise TacticFailed(f"have: '{impl_hyp}' not in context")
        if ant_hyp not in goal.context:
            raise TacticFailed(f"have: '{ant_hyp}' not in context")
        match goal.context[impl_hyp]:
            case Implies(ant, cons):
                if not structural_eq(goal.context[ant_hyp], ant):
                    raise TacticFailed(
                        f"have: type of '{ant_hyp}' does not match antecedent of '{impl_hyp}'"
                    )
                return [goal.with_hyp(new_name, cons)], lambda ps: ps[0]
            case other:
                raise TacticFailed(
                    f"have: '{impl_hyp}' has type {other!r}, expected an implication"
                )
    return tactic


def andL(hyp_name: str, result_name: str):
    """Extract left conjunct: from h: A & B, add result_name: A."""
    def tactic(goal: Goal):
        if hyp_name not in goal.context:
            raise TacticFailed(f"andL: '{hyp_name}' not in context")
        match goal.context[hyp_name]:
            case And(left, _):
                return [goal.with_hyp(result_name, left)], lambda ps: ps[0]
            case other:
                raise TacticFailed(f"andL: '{hyp_name}' has type {other!r}, expected A & B")
    return tactic


def andR(hyp_name: str, result_name: str):
    """Extract right conjunct: from h: A & B, add result_name: B."""
    def tactic(goal: Goal):
        if hyp_name not in goal.context:
            raise TacticFailed(f"andR: '{hyp_name}' not in context")
        match goal.context[hyp_name]:
            case And(_, right):
                return [goal.with_hyp(result_name, right)], lambda ps: ps[0]
            case other:
                raise TacticFailed(f"andR: '{hyp_name}' has type {other!r}, expected A & B")
    return tactic


def conj(h1: str, h2: str, result_name: str):
    """Conjunction intro: from h1: A and h2: B, add result_name: A & B."""
    def tactic(goal: Goal):
        if h1 not in goal.context:
            raise TacticFailed(f"conj: '{h1}' not in context")
        if h2 not in goal.context:
            raise TacticFailed(f"conj: '{h2}' not in context")
        combined = And(goal.context[h1], goal.context[h2])
        return [goal.with_hyp(result_name, combined)], lambda ps: ps[0]
    return tactic


def contradiction():
    def tactic(goal: Goal) -> ProofTerm:
        ctx   = list(goal.context.items())
        names = [k for k, _ in ctx]
        stmts = [v for _, v in ctx]

        # Direct P / ~P pairs
        for i, s in enumerate(stmts):
            for j, t in enumerate(stmts):
                if i != j and (structural_eq(s, Not(t)) or structural_eq(Not(s), t)):
                    return ExFalso(HypRef(names[i]), goal.statement)

        # ~(A | B) with A or B present in context
        for i, s in enumerate(stmts):
            match s:
                case Not(Or(a, b)):
                    if any(structural_eq(t, a) or structural_eq(t, b) for t in stmts):
                        return ExFalso(HypRef(names[i]), goal.statement)

        # ~(A & B) with both A and B present in context
        for i, s in enumerate(stmts):
            match s:
                case Not(And(a, b)):
                    if (any(structural_eq(t, a) for t in stmts) and
                            any(structural_eq(t, b) for t in stmts)):
                        return ExFalso(HypRef(names[i]), goal.statement)

        raise TacticFailed("contradiction: no contradictory hypotheses found")
    return tactic
