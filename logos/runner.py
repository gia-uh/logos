# logos/runner.py
from __future__ import annotations
from typing import Callable
from logos.goal import Goal
from logos.kernel import ProofTerm


class TacticFailed(Exception):
    pass


TacticResult = ProofTerm | tuple[list[Goal], Callable[[list[ProofTerm]], ProofTerm]]


class _AllGoals:
    """Sentinel that tells the runner to apply tactic to all current subgoals."""
    def __init__(self, tactic_fn):
        self.tactic_fn = tactic_fn

    def __call__(self, goal: Goal) -> TacticResult:
        return self.tactic_fn(goal)


def run(goal: Goal, by: list) -> ProofTerm:
    """Apply tactics in `by` to `goal`, returning a proof term."""
    return _Runner(list(by)).run(goal)


class _Runner:
    def __init__(self, tactics: list):
        self._tactics = tactics
        self._idx = 0

    def _take(self):
        if self._idx >= len(self._tactics):
            raise TacticFailed("No tactics left; no tactics remain to close open goal")
        item = self._tactics[self._idx]
        self._idx += 1
        return item

    def run(self, goal: Goal) -> ProofTerm:
        item = self._take()

        if isinstance(item, list):
            # Nested list: fresh sub-runner for this goal only
            return _Runner(item).run(goal)

        if isinstance(item, _AllGoals):
            # Apply the wrapped tactic to this goal
            result = item.tactic_fn(goal)
            if isinstance(result, ProofTerm):
                # Goal closed
                if self._idx < len(self._tactics):
                    remaining = len(self._tactics) - self._idx
                    raise TacticFailed(
                        f"Goal closed by _AllGoals "
                        f"but {remaining} tactics remain"
                    )
                return result
            # Multi-goal result: apply tactic to each subgoal
            subgoals, compose = result
            subgoal_proofs = [item.tactic_fn(sg) for sg in subgoals]
            return compose(subgoal_proofs)

        result = item(goal)

        if isinstance(result, ProofTerm):
            # Atomic: goal is closed
            if self._idx < len(self._tactics):
                remaining = len(self._tactics) - self._idx
                raise TacticFailed(
                    f"Goal closed by {item.__name__ if hasattr(item, '__name__') else item!r} "
                    f"but {remaining} tactics remain"
                )
            return result

        # Splitting/transforming: (subgoals, compose)
        subgoals, compose = result

        # Peek ahead to see if next item is _AllGoals
        next_idx = self._idx
        all_goals_tactic = None
        if next_idx < len(self._tactics):
            next_item = self._tactics[next_idx]
            if isinstance(next_item, _AllGoals):
                all_goals_tactic = next_item.tactic_fn
                self._idx += 1  # consume the _AllGoals item

        if all_goals_tactic is not None:
            # Apply the tactic to all subgoals
            subgoal_proofs = [all_goals_tactic(sg) for sg in subgoals]
        else:
            subgoal_proofs = [self.run(sg) for sg in subgoals]
        return compose(subgoal_proofs)
