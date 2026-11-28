"""Inductive safety certificates for explicit finite transition tables."""
from collections.abc import Callable, Iterable, Mapping
from dataclasses import dataclass
from hashlib import sha256
import json
from pathlib import Path
from types import MappingProxyType

from logos.expr import And, Eq, Expr, Implies, Lit, Not
from logos.kernel import AndIntro, ExFalso, HypRef, ImpliesIntro, NotElim, ProofTerm, Refl
from logos.portable import LogosProofError, ProofReceipt, artifact_bytes, verify_artifact

type State = str | tuple[str, ...]
type Edge = tuple[State, State]


@dataclass(frozen=True, init=False)
class FiniteTransitionSystem:
    """Snapshot an explicit universe, initial states, named relations and safety table.

    Each named relation lists all its edges. A state is a string or a tuple
    of strings. The safety predicate is evaluated once on every declared state.
    """

    universe: tuple[State, ...]
    initial: frozenset[State]
    transitions: Mapping[str, frozenset[Edge]]
    safe_states: frozenset[State]

    def __init__(
        self,
        universe: Iterable[State],
        initial: Iterable[State],
        transitions: Mapping[str, Iterable[Edge]],
        safe: Callable[[State], bool],
    ):
        states = tuple(universe)
        if any(
            not isinstance(state, str) and not (
                isinstance(state, tuple) and all(isinstance(part, str) for part in state)
            )
            for state in states
        ):
            raise ValueError("states must be strings or tuples of strings")
        state_set = frozenset(states)
        if len(state_set) != len(states):
            raise ValueError("the universe contains duplicate states")
        starts = frozenset(initial)
        if not starts <= state_set:
            raise ValueError("an initial state is outside the universe")
        relations = {}
        for name, edges in transitions.items():
            if not isinstance(name, str) or not name:
                raise ValueError("transition names must be nonempty strings")
            relation = frozenset(edges)
            if any(source not in state_set or target not in state_set for source, target in relation):
                raise ValueError(f"transition {name!r} has an endpoint outside the universe")
            relations[name] = relation
        safety = frozenset(state for state in states if safe(state))
        object.__setattr__(self, "universe", states)
        object.__setattr__(self, "initial", starts)
        object.__setattr__(self, "transitions", MappingProxyType(relations))
        object.__setattr__(self, "safe_states", safety)

    def replay_violation(self, start: State, steps: Iterable[tuple[str, State]]) -> State:
        """Require a legal named run from an initial state to an unsafe state."""
        if start not in self.initial:
            raise ValueError(f"trace starts outside the initial set: {start!r}")
        current = start
        for number, (name, target) in enumerate(steps, 1):
            if (current, target) not in self.transitions.get(name, ()):
                raise ValueError(f"illegal step {number}: {current!r} --{name}--> {target!r}")
            current = target
        if current in self.safe_states:
            raise ValueError(f"trace ends in a safe state: {current!r}")
        return current

    def export_safety(self, invariant: Iterable[State], path: str | Path) -> ProofReceipt:
        """Check initiation, closure and safety with Rust, then write the certificate."""
        statement, proof = self._certificate(invariant, prove=True)
        receipt = verify_artifact(artifact_bytes("finite_safety", statement, (), proof))
        Path(path).write_bytes(receipt.artifact)
        return receipt

    def verify_safety(self, invariant: Iterable[State], path: str | Path) -> ProofReceipt:
        """Require strict evidence for this table and this proposed invariant."""
        statement, _ = self._certificate(invariant, prove=False)
        expected = json.loads(artifact_bytes("finite_safety", statement, (), Refl(Lit(0))))
        artifact = Path(path).read_bytes()
        try:
            bundle = json.loads(artifact)
        except (ValueError, UnicodeError) as error:
            raise LogosProofError("invalid finite safety certificate") from error
        if not isinstance(bundle, dict) or bundle.get("target") != expected["target"]:
            raise LogosProofError("certificate statement does not match the model and invariant")
        if bundle.get("custom_axioms") != []:
            raise LogosProofError("finite safety certificates require zero custom axioms")
        return verify_artifact(artifact)

    def _certificate(self, invariant: Iterable[State], *, prove: bool) -> tuple[Expr, ProofTerm]:
        states = self.universe
        member = frozenset(invariant)
        indices = {state: index for index, state in enumerate(states)}
        if not member <= indices.keys():
            raise ValueError("an invariant state is outside the universe")

        initial = [state in self.initial for state in states]
        safe = [state in self.safe_states for state in states]
        relations = {
            name: sorted((indices[source], indices[target]) for source, target in edges)
            for name, edges in sorted(self.transitions.items())
        }
        manifest = json.dumps([states, initial, relations, safe], separators=(",", ":"))
        stamp = Lit(int.from_bytes(sha256(manifest.encode("ascii")).digest(), "big"))

        def obligation(
            label: str, source: int, target: int, premise: bool, conclusion: bool,
        ) -> tuple[Expr, ProofTerm]:
            left = _ground(source, premise)
            right = _ground(target, conclusion)
            statement = Implies(left, right)
            if not prove:
                return statement, Refl(Lit(0))  # Only the statement is used for matching.
            if conclusion:
                body = Refl(Lit(target))
            elif not premise:
                body = ExFalso(NotElim(HypRef("premise"), Refl(Lit(source))), right)
            else:
                raise LogosProofError(f"failed {label}")
            return statement, ImpliesIntro(left, "premise", body)

        initiation = [
            obligation(f"initial inclusion at {state!r}", i, i, initial[i], state in member)
            for i, state in enumerate(states)
        ]
        closure = [
            _conjunction([
                obligation(
                    f"closure under {name!r}: {states[i]!r} -> {states[j]!r}",
                    i, j, states[i] in member, states[j] in member,
                )
                for i, j in edges
            ])
            for name, edges in relations.items()
        ]
        safety = [
            obligation(f"invariant safety at {state!r}", i, i, state in member, safe[i])
            for i, state in enumerate(states)
        ]
        return _conjunction([
            (Eq(stamp, stamp), Refl(stamp)),
            _conjunction(initiation),
            _conjunction(closure),
            _conjunction(safety),
        ])


def _ground(index: int, holds: bool) -> Expr:
    reflexive = Eq(Lit(index), Lit(index))
    return reflexive if holds else Not(reflexive)


def _conjunction(rows: list[tuple[Expr, ProofTerm]]) -> tuple[Expr, ProofTerm]:
    if not rows:
        unit = Lit(0)
        return Eq(unit, unit), Refl(unit)
    if len(rows) == 1:
        return rows[0]
    middle = len(rows) // 2
    left, left_proof = _conjunction(rows[:middle])
    right, right_proof = _conjunction(rows[middle:])
    return And(left, right), AndIntro(left_proof, right_proof)
