"""logos.domains — high-level domain DSLs built on the logos kernel.

Each domain manages entities, auto-generates structural axioms, and
exposes theorem() / solve() without requiring users to write logos.vars
or logos.chain by hand.
"""
from __future__ import annotations

from logos.expr import Expr, Var, ForallNode
from logos.kernel import ProofTerm
from logos.theorem import Theorem


class Entity:
    """Base class for a domain entity."""
    name: str

    def __init__(self, name: str):
        self.name = name


class Domain:
    """Abstract base for constraint domains over typed entities.

    Subclasses must implement:
        _collect_vars()      → list of Var used in the theorem
        _build_premises()    → list of Expr (structural axioms + rules)
        _all_conclusions()   → iterable of (label, Expr) for solve()
    """

    def _collect_vars(self) -> list[Var]:
        raise NotImplementedError

    def _build_premises(self) -> list[Expr]:
        raise NotImplementedError

    def _all_conclusions(self):
        """Yield (label, conclusion_expr) for every candidate solution."""
        raise NotImplementedError

    # ── Public API ────────────────────────────────────────────────────

    def theorem(self, conclusion: Expr, *, name: str = "puzzle") -> Theorem:
        """Build a logos Theorem encoding all domain axioms as premises.

        Deliberately NOT universally quantified over the entity variables.
        ForallNode would let auto.intro() place them directly in context,
        making assumption() trivially close every sub-goal — i.e., any
        conclusion would be 'provable'.  Keeping them as free proposition
        variables forces the proof to use actual logical reasoning from
        the implication premises.
        """
        import logos
        premises = self._build_premises()
        body = logos.chain(*premises, conclusion) if premises else conclusion
        return Theorem(body, name=name)

    def solve(self, *, timeout: float = 0.5):
        """Try every candidate conclusion; return the unique consistent one.

        Each candidate is attempted with `logos.prove()` under `timeout` seconds.
        Wrong assignments are abandoned at the timeout; the correct one typically
        proves in milliseconds.

        Returns:
            label        if exactly one solution exists
            list[label]  if multiple (underdetermined)
            None         if none (inconsistent constraints)
        """
        import logos
        solutions = []
        for label, conclusion in self._all_conclusions():
            try:
                logos.prove(self.theorem(conclusion), timeout=timeout)
                solutions.append(label)
            except logos.LogosProofError:
                pass
        if len(solutions) == 1:
            return solutions[0]
        return solutions or None
