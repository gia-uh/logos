# logos/tactics/combinators.py
from logos.goal import Goal
from logos.kernel import ProofTerm
from logos.runner import TacticFailed, TacticResult, _AllGoals


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
                        # Closing tactic returned a ProofTerm; compose through accumulated steps
                        def compose_all(proofs: list[ProofTerm], _pt=result, _steps=list(steps)) -> ProofTerm:
                            pt = _pt
                            for compose in reversed(_steps):
                                pt = compose([pt])
                            return pt
                        return [], compose_all
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

        # Chain the compositions: current is the remaining open subgoal
        def compose_chain(proofs: list[ProofTerm], _steps=list(steps)) -> ProofTerm:
            result = proofs[0]
            for compose in reversed(_steps):
                result = compose([result])
            return result

        return [current], compose_chain
    return tactic


def all_goals(tactic_fn):
    """Apply tactic_fn to each open subgoal (for use after a splitting tactic)."""
    return _AllGoals(tactic_fn)
