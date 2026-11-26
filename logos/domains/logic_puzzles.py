"""logos.domains.logic_puzzles — classic truth/lie puzzle domains."""
from __future__ import annotations

from pathlib import Path
from typing import Literal

import logos

from logos.expr import Expr, Var
from logos.domains import Domain, Entity
from logos.domains._finite import BinaryChoice, solve, validate


SolveStatus = Literal["unique", "underdetermined", "inconsistent", "unknown"]


class KKEntity(Entity):
    """An entity in a Knights-and-Knaves puzzle.

    Exposes:
        entity.is_knight()  →  Expr (the 'knight' proposition)
        entity.is_knave()   →  Expr (the 'knave' proposition)
        entity.says(stmt)   →  self  (records the statement, returns self for chaining)
    """

    def __init__(self, name: str, domain: "KnightsKnaves"):
        super().__init__(name)
        self._domain = domain
        self.kn = Var(f"{name}_kn", bool)   # "name is a knight"
        self.kv = Var(f"{name}_kv", bool)   # "name is a knave"

    def is_knight(self) -> Expr:
        return self.kn

    def is_knave(self) -> Expr:
        return self.kv

    def says(self, stmt: Expr) -> "KKEntity":
        """Record that this entity asserts stmt."""
        self._domain._statements.append((self, stmt))
        self._domain._invalidate_solution()
        return self


class KnightsKnaves(Domain):
    """Domain for knights-and-knaves (truth-teller / liar) puzzles.

    Describe the inhabitants and their utterances, then solve::

        puzzle = KnightsKnaves()
        a, b = puzzle.entity("A"), puzzle.entity("B")
        a.says(a.is_knave() & b.is_knave())
        result = puzzle.solve()  # {"A": "knave", "B": "knight"}
        puzzle.export_proof("puzzle.logos")

    Use theorem(conclusion) to author a proof manually.
    """

    def __init__(self):
        self._entities: list[KKEntity] = []
        self._statements: list[tuple[KKEntity, Expr]] = []
        self._invalidate_solution()

    def _invalidate_solution(self) -> None:
        self._solve_status: SolveStatus | None = None
        self._solution_proof: logos.Theorem | None = None

    @property
    def solve_status(self) -> SolveStatus | None:
        """The status of the last solve for the current puzzle, or None before solving."""
        return self._solve_status

    def entity(self, name: str) -> KKEntity:
        """Add an inhabitant with a distinct name."""
        if any(entity.name == name for entity in self._entities):
            raise ValueError(f"duplicate inhabitant name {name!r}")
        entity = KKEntity(name, self)
        self._entities.append(entity)
        self._invalidate_solution()
        return entity

    def solve(self, *, timeout: float | None = 0.5) -> dict[str, str] | list[dict[str, str]] | None:
        """Return one assignment, all alternatives, or None; see solve_status.

        The timeout in seconds covers search and evidence construction. Pass
        None for no time limit. Use export_proof to verify a unique result.
        """
        self._invalidate_solution()
        atoms = set(self._collect_vars())
        for _, statement in self._statements:
            validate(statement, atoms)
        try:
            models, self._solution_proof = solve(
                self._choices(), self._utterance_premises(), name="knights_knaves", timeout=timeout,
            )
        except TimeoutError:
            self._solve_status = "unknown"
            return None

        if not models:
            self._solve_status = "inconsistent"
            return None
        assignments = [
            {entity.name: "knight" if atom is entity.kn else "knave"
             for entity, atom in zip(self._entities, model)}
            for model in models
        ]
        if len(assignments) == 1:
            self._solve_status = "unique"
            return assignments[0]
        self._solve_status = "underdetermined"
        return assignments

    def export_proof(self, path: str | Path) -> logos.ProofReceipt:
        """Verify the unique result with Rust and write its conditional proof."""
        if self._solution_proof is None:
            raise logos.LogosProofError("export_proof requires solve() to find a unique assignment")
        return logos.export_proof(logos.check(self._solution_proof), path)

    def _collect_vars(self) -> list[Var]:
        return [atom for entity in self._entities for atom in (entity.kn, entity.kv)]

    def _choices(self) -> list[BinaryChoice]:
        return [BinaryChoice(entity.kn, entity.kv) for entity in self._entities]

    def _utterance_premises(self) -> list[Expr]:
        return [
            premise for entity, stmt in self._statements
            for premise in (entity.kn >> stmt, entity.kv >> ~stmt)
        ]

    def _build_premises(self) -> list[Expr]:
        return [
            premise for choice in self._choices() for premise in choice.premises()
        ] + self._utterance_premises()
