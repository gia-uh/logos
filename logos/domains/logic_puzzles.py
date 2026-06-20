"""logos.domains.logic_puzzles — classic truth/lie puzzle domains."""
from __future__ import annotations

from itertools import product

from logos.expr import Expr, Var
from logos.domains import Domain, Entity


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
        return self


class KnightsKnaves(Domain):
    """Domain for knights-and-knaves (truth-teller / liar) puzzles.

    Usage::

        d = KnightsKnaves()
        a = d.entity("A")
        b = d.entity("B")

        a.says(b.is_knight())

        result = d.solve()
        # {"A": "knave", "B": "knight"}

    For manual proof access::

        thm = d.theorem(a.is_knave() & b.is_knight())
        logos.check(thm.proof(...))
    """

    def __init__(self):
        self._entities: list[KKEntity] = []
        self._statements: list[tuple[KKEntity, Expr]] = []

    def entity(self, name: str) -> KKEntity:
        """Add a new entity to the puzzle."""
        e = KKEntity(name, self)
        self._entities.append(e)
        return e

    # ── Domain protocol ───────────────────────────────────────────────

    def _collect_vars(self) -> list[Var]:
        vars_: list[Var] = []
        for e in self._entities:
            vars_.extend([e.kn, e.kv])
        return vars_

    def _build_premises(self) -> list[Expr]:
        premises: list[Expr] = []
        for e in self._entities:
            premises.append(e.kn | e.kv)      # exhaustivity: knight or knave
            premises.append(e.kn >> ~e.kv)    # exclusivity
            premises.append(e.kv >> ~e.kn)
        for e, stmt in self._statements:
            premises.append(e.kn >> stmt)      # knight: statement is true
            premises.append(e.kv >> ~stmt)     # knave:  statement is false
        return premises

    def _all_conclusions(self):
        """Yield (label_dict, conclusion_expr) for every role assignment."""
        roles = ["knight", "knave"]
        names = [e.name for e in self._entities]
        for assignment in product(roles, repeat=len(self._entities)):
            parts = [
                e.kn if role == "knight" else e.kv
                for e, role in zip(self._entities, assignment)
            ]
            conclusion = parts[0]
            for p in parts[1:]:
                conclusion = conclusion & p
            label = dict(zip(names, assignment))
            yield label, conclusion
