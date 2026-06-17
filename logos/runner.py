# logos/runner.py
from __future__ import annotations
from typing import Callable
from logos.goal import Goal
from logos.kernel import ProofTerm


class TacticFailed(Exception):
    pass


TacticResult = ProofTerm | tuple[list[Goal], Callable[[list[ProofTerm]], ProofTerm]]


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
        subgoal_proofs = [self.run(sg) for sg in subgoals]
        return compose(subgoal_proofs)
