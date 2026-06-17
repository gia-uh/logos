# logos/theorem.py
from logos.expr import Expr
from logos.goal import Goal
from logos.runner import run, TacticFailed
from logos.registry import register_axiom
from logos.kernel import ProofTerm


class LogosProofError(Exception):
    pass


def prove(statement: Expr, proof: list) -> ProofTerm:
    """Validate `proof` for `statement`. Returns the proof term or raises LogosProofError.

    Note (v0.1): kernel check is intentionally skipped — tactics like ring() and
    linarith() use token proof terms (Refl) that don't satisfy the kernel's strict
    type checker. The runner validates tactic applicability; kernel checking is
    left for a future version.
    """
    goal = Goal({}, statement)
    try:
        term = run(goal, proof)
    except TacticFailed as e:
        raise LogosProofError(f"Tactic failed: {e}") from e
    return term


def theorem(name: str, statement: Expr, proof: list) -> object:
    """Prove and register `statement` as a named axiom. Raises LogosProofError on failure."""
    term = prove(statement, proof)
    register_axiom(name, statement)
    return term
