"""logos.domains.logic_puzzles — classic truth/lie puzzle domains."""
from __future__ import annotations

from pathlib import Path
from typing import Literal

import logos

from logos import tactics as t
from logos.expr import And, Expr, Implies, Lit, Not, Or, Var
from logos.goal import Goal
from logos.helpers import structural_eq
from logos.runner import TacticFailed, TrailingTactics, run
from logos.domains import Domain, Entity
from logos.domains import _finite
from logos.domains._finite import BinaryChoice


SolveStatus = Literal["unique", "underdetermined", "inconsistent", "unknown"]


class _DomainTacticFailed(TacticFailed):
    pass


def _find_hypothesis(goal: Goal, stmt: Expr) -> str | None:
    return next((name for name, hyp in goal.context.items() if structural_eq(hyp, stmt)), None)


def _fresh_name(goal: Goal, name: str) -> str:
    while name in goal.context:
        name += "_"
    return name


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

    Use prove(claim, by=[...]) to guide a proof with tactics, or
    theorem(conclusion) to author evidence manually.
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
        self._validate_statements()
        try:
            models, self._solution_proof = _finite.solve(
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

    def prove(self, claim: Expr, *, by: list) -> logos.Theorem:
        """Introduce the puzzle premises, run tactics, and return a Rust-checked theorem."""
        self._validate_statements()
        _finite.validate(claim, set(self._collect_vars()))
        goal = Goal(_finite.bind(self._build_premises()), claim)
        try:
            evidence = run(goal, by)
        except TrailingTactics as error:
            plural = "tactic" if error.remaining == 1 else "tactics"
            raise logos.LogosProofError(
                f"Invalid tactic sequence: {error}. Remove the {error.remaining} extra "
                f"{plural} after the one that closed the goal."
            ) from error
        except TacticFailed as error:
            remaining = error.goal or goal
            lines = [f"Open goal: {self._describe(remaining.statement)}"]
            locals_ = [
                f"  {name}: {self._describe(statement)}"
                for name, statement in remaining.context.items()
                if goal.context.get(name) is not statement
            ]
            lines.append("Local hypotheses:" if locals_ else "Local hypotheses: none")
            lines.extend(locals_)
            if isinstance(error, _DomainTacticFailed):
                lines.append(str(error))
            raise logos.LogosProofError("\n".join(lines)) from None
        return logos.check(_finite.theorem(goal, evidence, name="knights_knaves_guided"))

    def cases_on_role(self, entity: KKEntity):
        """Open the knight branch first and the knave branch second."""
        if entity not in self._entities:
            raise ValueError("cases_on_role requires an inhabitant of this puzzle")

        def tactic(goal: Goal):
            exhaustive = _find_hypothesis(goal, entity.kn | entity.kv)
            if exhaustive is None:
                raise _DomainTacticFailed(f"The role premise for {entity.name} is unavailable here.")
            return t.cases(exhaustive, _fresh_name(goal, f"role_of_{entity.name}"))(goal)

        return tactic

    def use_statements(self):
        """Add the truth or negation of utterances by speakers with a known role."""
        def tactic(goal: Goal):
            current = goal
            steps = []
            for number, (entity, stmt) in enumerate(self._statements, 1):
                for role, consequence in ((entity.kn, stmt), (entity.kv, ~stmt)):
                    known_role = _find_hypothesis(current, role)
                    rule = _find_hypothesis(current, role >> consequence)
                    if (known_role is None or rule is None
                            or _find_hypothesis(current, consequence) is not None):
                        continue
                    name = _fresh_name(current, f"statement_{number}_by_{entity.name}")
                    [current], compose = t.have(name, rule, known_role)(current)
                    steps.append(compose)
            if not steps:
                raise _DomainTacticFailed(
                    "No new statements follow from the speaker roles in this branch."
                )

            def compose(proofs):
                for step in reversed(steps):
                    proofs = [step(proofs)]
                return proofs[0]

            return [current], compose

        return tactic

    def auto(self, *, timeout: float | None = 0.5):
        """Use finite role reasoning to finish the current open goal."""
        def tactic(goal: Goal):
            choices = self._choices()
            atoms = set(self._collect_vars())
            try:
                for statement in (*goal.context.values(), goal.statement):
                    _finite.validate(statement, atoms)
                return _finite.certify(goal, choices, _finite.budget(timeout))
            except ValueError as error:
                raise _DomainTacticFailed(str(error)) from None
            except TimeoutError:
                raise _DomainTacticFailed("Finite search exhausted its time budget.") from None
            except _finite.MissingRolePremise:
                raise _DomainTacticFailed("A role premise needed by finite search is missing.") from None
            except _finite.Counterexample as error:
                roles = ", ".join(self._describe(atom) for atom in error.assignment)
                raise _DomainTacticFailed(f"A valid assignment leaves the goal false: {roles}.") from None

        return tactic

    def _validate_statements(self) -> None:
        atoms = set(self._collect_vars())
        for _, statement in self._statements:
            _finite.validate(statement, atoms)

    def _describe(self, expr: Expr) -> str:
        match expr:
            case Var():
                for entity in self._entities:
                    if expr is entity.kn:
                        return f"{entity.name} is a knight"
                    if expr is entity.kv:
                        return f"{entity.name} is a knave"
                return expr.name
            case Lit(value) if value is False:
                return "contradiction"
            case Not(operand):
                return f"it is false that ({self._describe(operand)})"
            case And(left, right):
                return f"({self._describe(left)}) and ({self._describe(right)})"
            case Or(left, right):
                return f"({self._describe(left)}) or ({self._describe(right)})"
            case Implies(left, right):
                return f"if {self._describe(left)}, then {self._describe(right)}"
            case _:
                return type(expr).__name__

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
