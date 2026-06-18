from __future__ import annotations
import inspect
from typing import get_type_hints
from logos.expr import Expr, Var, ForallNode
from logos.goal import Goal
from logos.runner import run, TacticFailed


class LogosProofError(Exception):
    pass


class Axiom:
    """A trusted statement — no proof required."""
    def __init__(self, statement: Expr, *, name: str = ""):
        self.name = name
        self.statement = statement
        self.certified = True

    def __repr__(self):
        return f"Axiom({self.name!r})"


class Theorem:
    """A statement to be proved. Attach proof with .proof(...), validate with logos.check()."""
    def __init__(self, statement: Expr, *, name: str = ""):
        self.name = name
        self.statement = statement
        self._proof_spec: list | None = None
        self.certified = False

    def proof(self, *args):
        """Attach proof spec.
        - .proof(tactic1, tactic2, ...)  varargs
        - .proof([t1, t2, ...])  list
        - @thm.proof def _(): return [...]  decorator (0-param fn returning list)
        Returns self for chaining with logos.check().
        """
        if len(args) == 1 and callable(args[0]) and not isinstance(args[0], list):
            fn = args[0]
            # Distinguish decorator (0 params) from tactic (1+ params)
            try:
                n_params = len(inspect.signature(fn).parameters)
            except (ValueError, TypeError):
                n_params = 1  # assume tactic if we can't inspect
            if n_params == 0:
                result = fn()
                self._proof_spec = result if isinstance(result, list) else [result]
                return fn
            # Otherwise treat as a single tactic in varargs
            self._proof_spec = [fn]
            return self
        elif len(args) == 1 and isinstance(args[0], list):
            self._proof_spec = args[0]
        else:
            self._proof_spec = list(args)
        return self

    def __repr__(self):
        status = "certified" if self.certified else "unverified"
        return f"Theorem[{status}]({self.name!r})"


def _build_from_fn(fn, cls):
    try:
        hints = get_type_hints(fn)
    except Exception:
        hints = {}
    params = [p for p in inspect.signature(fn).parameters if p != 'return']
    vars_ = [Var(p, hints.get(p, object)) for p in params]
    stmt = fn(*vars_)
    if not isinstance(stmt, Expr):
        raise TypeError(
            f"@logos.{cls.__name__.lower()} body must return an Expr, "
            f"got {type(stmt).__name__!r}"
        )
    for v in reversed(vars_):
        stmt = ForallNode(v, stmt)
    return cls(stmt, name=fn.__name__)


def axiom(fn_or_stmt):
    """@logos.axiom decorator or logos.axiom(expr) — creates a trusted Axiom."""
    if callable(fn_or_stmt):
        return _build_from_fn(fn_or_stmt, Axiom)
    return Axiom(fn_or_stmt)


def theorem(fn):
    """@logos.theorem decorator — creates a Theorem object (no proof yet)."""
    return _build_from_fn(fn, Theorem)


class _GroundProof:
    """Intermediate result of logos.prove() — pass to logos.check() to validate."""
    def __init__(self, statement: Expr, proof: list):
        self.statement = statement
        self._proof_spec = proof
        self.certified = False
        self.name = "<anonymous>"


def check(thm):
    """Validate a Theorem or _GroundProof. Raises LogosProofError on failure."""
    if isinstance(thm, _GroundProof):
        goal = Goal({}, thm.statement)
        try:
            run(goal, thm._proof_spec)
        except TacticFailed as e:
            raise LogosProofError(f"Proof failed: {e}") from e
        thm.certified = True
        return thm
    if isinstance(thm, Theorem):
        if thm.certified:
            return thm
        if thm._proof_spec is None:
            raise LogosProofError(f"Theorem '{thm.name}' has no proof attached")
        goal = Goal({}, thm.statement)
        try:
            run(goal, thm._proof_spec)
        except TacticFailed as e:
            raise LogosProofError(f"Theorem '{thm.name}': {e}") from e
        thm.certified = True
        return thm
    raise TypeError(
        f"logos.check: expected Theorem or _GroundProof, got {type(thm).__name__!r}"
    )


def prove(statement: Expr, proof: list) -> _GroundProof:
    """One-shot: create a _GroundProof. Pass to logos.check() to validate."""
    return _GroundProof(statement, proof)
