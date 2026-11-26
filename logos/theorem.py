from __future__ import annotations
import inspect
from typing import get_type_hints
from logos.expr import Expr, Var, ForallNode
from logos.goal import Goal
from logos.runner import run, TacticFailed
from logos.portable import (
    LogosProofError, ProofReceipt, artifact_bytes, statement_declarations, verify_artifact,
)


class Axiom:
    """An author-declared assumption."""
    def __init__(self, statement: Expr, *, name: str = ""):
        self.name = name
        self.statement = statement
        self.certified = False

    def __repr__(self):
        return f"Axiom({self.name!r})"


def _freeze_spec(spec):
    if isinstance(spec, list):
        return tuple(_freeze_spec(item) for item in spec)
    return spec


def _matches_spec(spec, snapshot):
    if isinstance(spec, list):
        return (
            isinstance(snapshot, tuple)
            and len(spec) == len(snapshot)
            and all(_matches_spec(item, saved) for item, saved in zip(spec, snapshot))
        )
    return spec is snapshot


class _Proof:
    def __init__(self, statement: Expr, *, name: str, declarations=None):
        self.statement = statement
        self.name = name
        self.declarations = (
            statement_declarations(statement) if declarations is None else tuple(declarations)
        )
        self._proof_spec = None
        self._receipt = None
        self._evidence = None
        self._checked_spec = None

    @property
    def receipt(self) -> ProofReceipt | None:
        receipt = self._receipt
        if receipt is None:
            return None
        try:
            current = artifact_bytes(self.name, self.statement, self.declarations, self._evidence)
            same_spec = _matches_spec(self._proof_spec, self._checked_spec)
        except (LogosProofError, TypeError, RecursionError):
            current, same_spec = None, False
        if not same_spec or current != receipt.artifact:
            self._receipt = None
        return self._receipt

    @property
    def certified(self) -> bool:
        return self.receipt is not None


class Theorem(_Proof):
    """A statement with tactics that can be verified by logos.check()."""

    def __init__(self, statement: Expr, *, name: str = "", declarations=None):
        super().__init__(statement, name=name, declarations=declarations)

    def proof(self, *args):
        """Attach proof spec.
        - .proof(tactic1, tactic2, ...)  varargs
        - .proof([t1, t2, ...])  list
        - @thm.proof def _(): return [...]  decorator (0-param fn returning list)
        Returns self for chaining with logos.check().
        """
        self._receipt = None
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


class _GroundProof(_Proof):
    """Intermediate result of logos.prove() for an anonymous statement."""

    def __init__(self, statement: Expr, proof: list):
        super().__init__(statement, name="<anonymous>")
        self._proof_spec = proof


def check(thm):
    """Run the tactics and certify their actual evidence with the Rust checker."""
    if not isinstance(thm, _Proof):
        raise TypeError(
            f"logos.check: expected Theorem or _GroundProof, got {type(thm).__name__!r}"
        )
    thm._receipt = None
    if thm._proof_spec is None:
        raise LogosProofError(f"Theorem '{thm.name}' has no proof attached")

    saved_spec = _freeze_spec(thm._proof_spec)
    statement = thm.statement
    declarations = tuple(thm.declarations)
    name = thm.name
    try:
        evidence = run(Goal({}, statement), thm._proof_spec)
    except TacticFailed as error:
        raise LogosProofError(f"Theorem '{name}': {error}") from error

    artifact = artifact_bytes(name, statement, declarations, evidence)
    receipt = verify_artifact(artifact)
    thm._checked_spec = saved_spec
    thm._evidence = evidence
    thm._receipt = receipt
    if thm.receipt is None:
        raise LogosProofError("proof changed during Rust verification")
    return thm


def prove(thm_or_stmt, tactics=None, *, hints=None, depth: int = 5, timeout: float | None = None):
    """Two modes:

    logos.prove(stmt, [tactics])
        One-shot anonymous proof — returns a _GroundProof, validate with logos.check().

    logos.prove(thm)  /  logos.prove(thm, hints=[...], depth=N, timeout=T)
        Auto-prove a Theorem using t.auto(). Equivalent to:
            logos.check(thm.proof(t.auto(*hints, depth=N, timeout=T)))
        Returns the certified Theorem or raises LogosProofError.
    """
    if isinstance(thm_or_stmt, Theorem):
        from logos.tactics.auto import auto as _auto
        return check(thm_or_stmt.proof(_auto(*(hints or []), depth=depth, timeout=timeout)))
    # Expr + explicit tactics → _GroundProof
    return _GroundProof(thm_or_stmt, tactics or [])
