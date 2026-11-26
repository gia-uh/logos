# logos/tactics/structural.py
from logos.expr import (
    Expr, Lit, Var, ForallNode, ExistsNode, And, Or, Not, Implies,
)
from logos.goal import Goal
from logos.kernel import (
    ProofTerm, KernelError,
    Refl, HypRef, ForallIntro, ForallElim,
    ImpliesIntro, ImpliesElim,
    AndIntro, AndElimL, AndElimR,
    OrIntroL, OrIntroR, CaseAnalysis, NotIntro, NotElim, ExFalso,
    ExistsIntro, AxiomRef, TheoremRef,
)
from logos.helpers import substitute, substitute_symbols, structural_eq, try_unify
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
                    stmt = substitute_symbols(body, {id(var): new_var})
                    steps.append(("forall", name, new_var))
                case Implies(ant, cons):
                    ctx[name] = ant
                    stmt = cons
                    steps.append(("implies", name, ant))
                case Not(operand):
                    ctx[name] = operand
                    stmt = Lit(False)
                    steps.append(("not", name, operand))
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
                    if kind == "not":
                        result = NotIntro(result)
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
    - Axiom object: reference the custom assumption
    - Theorem object: reference the lemma and its proof
    """
    def tactic(goal: Goal):
        from logos.theorem import Theorem, Axiom as LogosAxiom

        if isinstance(ref, str):
            # Local hypothesis only
            if ref not in goal.context:
                raise TacticFailed(f"apply '{ref}': not in local context")
            stmt = goal.context[ref]
            proof_base = HypRef(ref)
        elif isinstance(ref, Theorem):
            stmt = ref.statement
            proof_base = TheoremRef(ref)
        elif isinstance(ref, LogosAxiom):
            stmt = ref.statement
            proof_base = AxiomRef(ref)
        else:
            raise TacticFailed(f"apply: expected str, Axiom or Theorem, got {type(ref).__name__!r}")

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
                derived = ImpliesElim(HypRef(impl_hyp), HypRef(ant_hyp))
                return [goal.with_hyp(new_name, cons)], lambda ps: ImpliesElim(
                    ImpliesIntro(cons, new_name, ps[0]), derived
                )
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


def _trivial_proof(expr: Expr, context: dict[str, Expr]) -> ProofTerm | None:
    """Construct evidence for a hypothesis or a conjunction or disjunction of them."""
    for name, statement in context.items():
        if structural_eq(expr, statement):
            return HypRef(name)
    match expr:
        case And(left, right):
            a = _trivial_proof(left, context)
            b = _trivial_proof(right, context)
            if a is not None and b is not None:
                return AndIntro(a, b)
        case Or(left, right):
            a = _trivial_proof(left, context)
            if a is not None:
                return OrIntroL(a, right)
            b = _trivial_proof(right, context)
            if b is not None:
                return OrIntroR(left, b)
    return None


def contradiction():
    def tactic(goal: Goal) -> ProofTerm:
        def close(false_proof: ProofTerm) -> ProofTerm:
            if isinstance(goal.statement, Lit) and goal.statement.value is False:
                return false_proof
            return ExFalso(false_proof, goal.statement)

        for name, statement in goal.context.items():
            match statement:
                case Lit(value) if value is False:
                    return close(HypRef(name))
                case Not(operand):
                    premise = _trivial_proof(operand, goal.context)
                    if premise is not None:
                        return close(NotElim(HypRef(name), premise))
                case Implies(antecedent, Not(operand)):
                    argument = _trivial_proof(antecedent, goal.context)
                    premise = _trivial_proof(operand, goal.context)
                    if argument is not None and premise is not None:
                        return close(NotElim(ImpliesElim(HypRef(name), argument), premise))

        raise TacticFailed("contradiction: no contradictory hypotheses found")
    return tactic
