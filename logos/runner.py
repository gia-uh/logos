# logos/runner.py
from __future__ import annotations
from typing import Callable
from logos.goal import Goal
from logos.kernel import ProofTerm


class TacticFailed(Exception):
    goal: Goal | None = None


class TrailingTactics(TacticFailed):
    """A tactic closed the goal while tactics remained in the list.

    This is a malformed proof, not an unsolved one: the remaining tactics were
    never applied, so the goal must not be reported as open.
    """

    def __init__(self, remaining: int):
        self.remaining = remaining
        plural = "tactic" if remaining == 1 else "tactics"
        verb = "remains" if remaining == 1 else "remain"
        super().__init__(
            f"Goal was already closed, but {remaining} {plural} {verb} unapplied"
        )


def _at_goal(goal: Goal, tactic):
    try:
        return tactic(goal)
    except TacticFailed as error:
        if error.goal is None:
            error.goal = goal
        raise


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

    def _closed(self, proof: ProofTerm) -> ProofTerm:
        remaining = len(self._tactics) - self._idx
        if remaining:
            raise TrailingTactics(remaining)
        return proof

    def run(self, goal: Goal) -> ProofTerm:
        return _at_goal(goal, self._run)

    def _run(self, goal: Goal, *, check_trailing: bool = True) -> ProofTerm:
        item = self._take()

        if isinstance(item, list):
            # Nested list: fresh sub-runner for this goal only. When the
            # enclosing split owns the remaining tactics for later subgoals,
            # it checks for leftovers after all subgoals are closed.
            proof = _Runner(item).run(goal)
            return self._closed(proof) if check_trailing else proof

        if isinstance(item, _AllGoals):
            # Apply the wrapped tactic to this goal
            result = item.tactic_fn(goal)
            if isinstance(result, ProofTerm):
                # Goal closed
                return self._closed(result) if check_trailing else result
            # Multi-goal result: apply tactic to each subgoal
            subgoals, compose = result
            subgoal_proofs = [_at_goal(sg, item.tactic_fn) for sg in subgoals]
            proof = compose(subgoal_proofs)
            return self._closed(proof) if check_trailing else proof

        result = item(goal)

        if isinstance(result, ProofTerm):
            # Atomic: goal is closed
            return self._closed(result) if check_trailing else result

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
            subgoal_proofs = [_at_goal(sg, all_goals_tactic) for sg in subgoals]
            proof = compose(subgoal_proofs)
            return self._closed(proof) if check_trailing else proof

        # Each subgoal consumes the next tactic from this shared list; the
        # trailing check waits until every subgoal is closed.
        subgoal_proofs = [
            _at_goal(sg, lambda g: self._run(g, check_trailing=False))
            for sg in subgoals
        ]
        proof = compose(subgoal_proofs)
        return self._closed(proof) if check_trailing else proof
