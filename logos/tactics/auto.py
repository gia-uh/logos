from __future__ import annotations
import time
import itertools
from logos.expr import ForallNode, Implies, And, Or, Not
from logos.goal import Goal
from logos.helpers import structural_eq
from logos.kernel import ProofTerm
from logos.runner import TacticFailed

_counter = itertools.count()


def _fresh() -> str:
    """Globally unique hypothesis name for auto-introduced variables."""
    return f"_a{next(_counter)}"


def auto(*hints, depth: int = 5, timeout: float | None = None):
    """Automatic tactic. Tries a cascade of strategies up to `depth` search levels.

    hints can be mixed:
    - Tactic callables: tried directly against the goal and subgoals
    - Axiom / Theorem objects: tried via apply()
    - Function objects (from @logos.define): tried via unfold() then recurse

    depth: max structural decomposition depth (intros, splits, unfolds).
    timeout: seconds before raising TacticFailed.

    Cascade order per level:
      0. cheap closers: refl, decide, norm_num, assumption, contradiction
      1. arithmetic:    ring, linarith
      2. structural:    intro / split / left|right / not-intro
      3. tactic hints:  each hint callable
      4. apply hints:   apply(axiom_or_theorem) for each hint
      5. unfold hints:  unfold(fn) + recurse for each Function hint
    """
    from logos.tactics.structural import intro, assumption, apply, split, left, right, contradiction, cases
    from logos.tactics.rewrite import refl, unfold, norm_num
    from logos.tactics.arithmetic import ring, linarith, decide
    from logos.define import Function

    # Partition hints by kind
    fn_hints     = [h for h in hints if isinstance(h, Function)]
    ax_hints     = [h for h in hints if hasattr(h, 'statement')]
    tactic_hints = [h for h in hints
                    if callable(h) and not hasattr(h, 'statement') and not isinstance(h, Function)]

    deadline = time.perf_counter() + timeout if timeout is not None else None

    def _check_time():
        if deadline is not None and time.perf_counter() > deadline:
            raise TacticFailed("auto: timeout exceeded")

    def _try(tac_fn, goal, d):
        """Apply tac_fn; on subgoals, recurse at depth d."""
        result = tac_fn(goal)
        if isinstance(result, ProofTerm):
            return result
        subgoals, compose = result
        sub_proofs = [_auto(sg, d) for sg in subgoals]
        return compose(sub_proofs)

    def _auto(goal: Goal, d: int) -> ProofTerm:
        _check_time()

        # ── Preprocess: eagerly flatten And hypotheses ───────────────────
        # Terminates because each And hyp is removed before the two parts are added.
        ctx = dict(goal.context)
        changed = True
        while changed:
            changed = False
            for name, hyp in list(ctx.items()):
                match hyp:
                    case And(l, r):
                        hl, hr = _fresh(), _fresh()
                        del ctx[name]
                        ctx[hl] = l
                        ctx[hr] = r
                        changed = True
                        break
        goal = Goal(ctx, goal.statement)

        # ── Level 0: cheap closers (no depth cost) ───────────────────────
        for closer in [refl, decide, norm_num, assumption, contradiction]:
            try:
                result = closer()(goal)
                if isinstance(result, ProofTerm):
                    return result
            except (TacticFailed, Exception):
                pass

        # ── Level 1: arithmetic decision procedures (tried even at depth 0) ─
        for arith in [ring, linarith]:
            try:
                result = arith()(goal)
                if isinstance(result, ProofTerm):
                    return result
            except TacticFailed:
                pass

        if d <= 0:
            raise TacticFailed(f"auto: depth 0 reached, cannot close {goal.statement!r}")

        # ── Level 2: structural decomposition (goal-level) ──────────────
        stmt = goal.statement

        match stmt:
            case ForallNode() | Implies() | Not():
                # intro is FREE — does not consume depth (always terminates,
                # goal strictly shrinks by one binder each time)
                h = _fresh()
                try:
                    return _try(intro(h), goal, d)
                except TacticFailed:
                    pass

            case And():
                try:
                    return _try(split(), goal, d - 1)
                except TacticFailed:
                    pass

            case Or(l_expr, r_expr):
                for branch_tac in [left(r_expr), right(l_expr)]:
                    try:
                        return _try(branch_tac, goal, d - 1)
                    except TacticFailed:
                        pass

        # ── Level 2b: case analysis on Or hypotheses (costs depth) ───────
        for name, hyp in list(goal.context.items()):
            match hyp:
                case Or():
                    h = _fresh()
                    try:
                        return _try(cases(name, h), goal, d - 1)
                    except TacticFailed:
                        pass

        # ── Level 2c: forward implication application (costs depth) ──────
        for impl_name, hyp in list(goal.context.items()):
            match hyp:
                case Implies(ant, cons):
                    # Skip if the conclusion is already derivable in context
                    if any(structural_eq(cons, v) for v in goal.context.values()):
                        continue
                    for ant_name, ant_hyp in list(goal.context.items()):
                        if ant_name != impl_name and structural_eq(ant_hyp, ant):
                            h = _fresh()
                            try:
                                return _auto(goal.with_hyp(h, cons), d - 1)
                            except TacticFailed:
                                pass

        # ── Level 3: tactic hints ────────────────────────────────────────
        for tac in tactic_hints:
            _check_time()
            try:
                return _try(tac, goal, d - 1)
            except TacticFailed:
                pass

        if d < 2:
            raise TacticFailed(f"auto(depth={d}): exhausted on {stmt!r}")

        # ── Level 4: axiom/theorem hints via apply() ─────────────────────
        for ax in ax_hints:
            _check_time()
            try:
                return _try(apply(ax), goal, d - 1)
            except TacticFailed:
                pass

        # ── Level 5: unfold Function hints then recurse ──────────────────
        for fn in fn_hints:
            _check_time()
            try:
                return _try(unfold(fn), goal, d - 1)
            except TacticFailed:
                pass

        raise TacticFailed(f"auto(depth={d}): all strategies exhausted on {stmt!r}")

    def tactic(goal: Goal) -> ProofTerm:
        return _auto(goal, depth)

    tactic.__name__ = "auto"
    return tactic
