# logos/tactics/combinators.py
from logos.goal import Goal
from logos.kernel import ProofTerm
from logos.runner import TacticFailed, TacticResult


def then(*tactics):
    """Apply tactics in sequence to the current goal (as a single compound tactic)."""
    def tactic(goal: Goal) -> TacticResult:
        from logos.runner import _Runner
        return _Runner(list(tactics)).run(goal)
    return tactic


def first(*tactics):
    """Try each tactic in order; succeed with the first that doesn't raise TacticFailed."""
    def tactic(goal: Goal) -> TacticResult:
        last_err = None
        for t in tactics:
            try:
                return t(goal)
            except TacticFailed as e:
                last_err = e
        raise TacticFailed(f"first: all tactics failed. Last: {last_err}")
    return tactic


def try_(tactic_fn):
    """Apply tactic_fn; if it fails, return a no-op (transforms goal to itself)."""
    def tactic(goal: Goal) -> TacticResult:
        try:
            return tactic_fn(goal)
        except TacticFailed:
            # Return identity: 1 subgoal (same goal), identity compose
            return [goal], lambda ps: ps[0]
    return tactic


def repeat(tactic_fn):
    """Apply tactic_fn until it fails; apply all successful steps."""
    def tactic(goal: Goal) -> TacticResult:
        steps = []
        current = goal
        while True:
            try:
                result = tactic_fn(current)
                if isinstance(result, ProofTerm):
                    if steps:
                        # Build composed result
                        pass  # handled by closure below
                    return result
                subgoals, compose = result
                if len(subgoals) != 1:
                    break  # can't repeat on multi-subgoal tactics
                steps.append(compose)
                current = subgoals[0]
            except TacticFailed:
                break

        if not steps:
            return [goal], lambda ps: ps[0]

        # Chain the compositions
        def compose_all(proofs: list[ProofTerm]) -> ProofTerm:
            result = proofs[0]
            for compose in reversed(steps):
                result = compose([result])
            return result

        return [current], compose_all
    return tactic


def all_goals(tactic_fn):
    """Apply tactic_fn to each open subgoal (for use after a splitting tactic)."""
    # This is a meta-tactic wrapper: when used in a by list after a splitter,
    # the runner will call the returned tactic once per subgoal.
    # For v0.1: all_goals is handled by the runner via _AllGoals sentinel.
    return _AllGoals(tactic_fn)


class _AllGoals:
    """Sentinel that tells the runner to apply tactic to all current subgoals."""
    def __init__(self, tactic_fn):
        self.tactic_fn = tactic_fn

    def __call__(self, goal: Goal) -> TacticResult:
        return self.tactic_fn(goal)
