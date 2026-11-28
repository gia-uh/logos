from __future__ import annotations
import inspect
from typing import get_type_hints
from logos.expr import Expr, Var, ForallNode
from logos.helpers import normalize_order
from logos.goal import Goal
from logos.runner import run, TacticFailed
from logos.portable import (
    LogosProofError, ProofReceipt, artifact_bytes, inspect_artifact,
    statement_declarations, verify_artifact,
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
        self._evidence_key = None
        self._checked_spec = None
        self._claim = None
        self._strategy = None

    def _annotations(self) -> dict:
        return {"claim": self._claim, "strategy": self._strategy}

    def _run_proof(self, statement):
        if self._proof_spec is None:
            raise LogosProofError(f"Theorem '{self.name}' has no proof attached")
        try:
            return run(Goal({}, statement), self._proof_spec)
        except TacticFailed as error:
            raise LogosProofError(f"Theorem '{self.name}': {error}") from error

    def _revalidate(self):
        """Hook for proofs bound to external state; most proofs need nothing."""

    def _compile_evidence(self, *, force_run=False):
        """Return current evidence, reusing compiled records only when eligible.

        The persistent record holds a proof term, never a verdict.  A caller
        that verifies an artifact still sends every lemma to the Rust checker.
        ``force_run`` is used by an explicit ``check`` for a theorem that has
        no usable record: its proof body must execute as it did before the
        cache existed.
        """
        from logos import evidence_cache

        # Subclasses that bind evidence to live source keep revalidating and
        # re-running on every check, as before.
        revalidates = (
            type(self)._run_proof is not _Proof._run_proof
            or type(self)._revalidate is not _Proof._revalidate
            or type(self)._dependency_evidence is not _Proof._dependency_evidence
        )
        cache_plan = evidence_cache._plan(self)
        same_spec = _matches_spec(self._proof_spec, self._checked_spec)
        reuse_memory = not (force_run and cache_plan is None)
        if self._evidence is not None and same_spec and not revalidates and reuse_memory:
            if cache_plan is None:
                if self._evidence_key is None:
                    return self._evidence
            elif self._evidence_key == cache_plan.key:
                return self._evidence
        if cache_plan is not None:
            cached = evidence_cache._load(cache_plan)
            if cached is not None:
                self._evidence = cached
                self._evidence_key = cache_plan.key
                return cached
        evidence = self._run_proof(self.statement)
        self._evidence = evidence
        self._evidence_key = cache_plan.key if cache_plan is not None else None
        if cache_plan is not None:
            evidence_cache._stage(cache_plan, evidence)
        else:
            # An ineligible proof may have changed a global that an eligible
            # dependency reads.  Its next plan must observe the new value.
            evidence_cache._forget_plans()
        return evidence

    def _dependency_evidence(self, refresh):
        if self._proof_spec is None:
            raise LogosProofError(f"Lemma '{self.name}' has no proof attached")
        same_spec = _matches_spec(self._proof_spec, self._checked_spec)
        revalidates = (
            type(self)._run_proof is not _Proof._run_proof
            or type(self)._revalidate is not _Proof._revalidate
        )
        if self._evidence is not None and same_spec and not revalidates:
            if not refresh:
                # The receipt freshness pass re-encodes the current evidence.
                # It does not recompile a dependency, as before the cache.
                return self._evidence
            # A persistent key change means a mutable input or dependency may
            # have moved since the in-memory evidence was built.  Recompile
            # rather than trusting the old object graph.
            from logos import evidence_cache
            cache_plan = evidence_cache._plan(self)
            if cache_plan is None:
                if self._evidence_key is None:
                    return self._evidence
            elif self._evidence_key == cache_plan.key:
                return self._evidence
        if not refresh:
            raise LogosProofError(f"Lemma '{self.name}' evidence has changed")
        self._receipt = None
        self._checked_spec = _freeze_spec(self._proof_spec)
        self._evidence = None
        self._evidence_key = None
        return self._compile_evidence()

    @property
    def receipt(self) -> ProofReceipt | None:
        receipt = self._receipt
        if receipt is None:
            return None
        try:
            self._revalidate()
            current = artifact_bytes(
                self.name, self.statement, self.declarations, self._evidence,
                annotations=self._annotations(),
            )
            same_spec = _matches_spec(self._proof_spec, self._checked_spec)
        except (LogosProofError, TypeError, RecursionError):
            current, same_spec = None, False
        if not same_spec or current != receipt.artifact:
            self._receipt = None
        return self._receipt

    @property
    def certified(self) -> bool:
        return self.receipt is not None

    def inspect(self) -> str:
        """Return the Rust checker's Markdown reading of the current receipt.

        The reading is produced from the exact artifact bytes that the Rust
        checker verified; it is never reconstructed in Python. Authored claim,
        strategy and ``p.note`` commentary travel in those bytes and are
        labelled as commentary by the checker.
        """
        had_receipt = self._receipt is not None
        receipt = self.receipt
        if receipt is None:
            if had_receipt:
                raise LogosProofError(
                    f"Theorem '{self.name}' evidence has changed; call logos.check again"
                )
            raise LogosProofError(
                f"Theorem '{self.name}' has no current Rust verification; call logos.check first"
            )
        markdown = inspect_artifact(receipt.artifact)
        current = self.receipt
        if current is None or current.artifact != receipt.artifact:
            raise LogosProofError(
                f"Theorem '{self.name}' proof changed during inspection; call logos.check again"
            )
        return markdown


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
        self._checked_spec = None
        self._evidence = None
        self._evidence_key = None
        self._strategy = None
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
                self._strategy = inspect.getdoc(fn)
                return fn
            # The book style takes `p` first, then one parameter for each
            # forall binder.  Anything else keeps the original tactic path.
            from logos.authoring import authoring_signature_matches, authoring_tactic
            if authoring_signature_matches(self, fn):
                self._proof_spec = [authoring_tactic(self, fn)]
                self._strategy = inspect.getdoc(fn)
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

    def check(self):
        """Check this theorem now and certify its actual evidence."""
        return check(self)


def _build_from_fn(fn, cls):
    try:
        hints = get_type_hints(fn)
    except Exception:
        hints = {}
    params = [p for p in inspect.signature(fn).parameters if p != 'return']
    vars_ = [Var(p, hints.get(p, object)) for p in params]
    stmt = normalize_order(fn(*vars_))
    if not isinstance(stmt, Expr):
        raise TypeError(
            f"@logos.{cls.__name__.lower()} body must return an Expr, "
            f"got {type(stmt).__name__!r}"
        )
    for v in reversed(vars_):
        stmt = ForallNode(v, stmt)
    built = cls(stmt, name=fn.__name__)
    if hasattr(built, "_claim"):
        built._claim = inspect.getdoc(fn)
    return built


def axiom(fn_or_stmt):
    """@logos.axiom decorator or logos.axiom(expr) — creates a trusted Axiom."""
    if callable(fn_or_stmt):
        return _build_from_fn(fn_or_stmt, Axiom)
    return Axiom(fn_or_stmt)


def theorem(fn=None, *, about=None):
    """@logos.theorem decorator — creates a Theorem object (no proof yet).

    With ``about=<function>`` the decorator builds a contract theorem bound to
    that function's source; the decorated body must return ``logos.contract``.
    """
    if about is not None:
        if fn is not None:
            raise TypeError("logos.theorem: pass a function or about=<function>, not both")
        from logos.contracts import theorem_about
        return lambda body: theorem_about(body, about)
    if fn is None:
        raise TypeError("logos.theorem: expected a function or about=<function>")
    return _build_from_fn(fn, Theorem)


class _GroundProof(_Proof):
    """Intermediate result of logos.prove() for an anonymous statement."""

    def __init__(self, statement: Expr, proof: list):
        super().__init__(statement, name="<anonymous>")
        self._proof_spec = proof


def check(thm):
    """Run the tactics and certify their actual evidence with the Rust checker."""
    declaration = getattr(thm, "__logos_function__", None)
    if declaration is not None:
        return declaration.check()
    if not isinstance(thm, _Proof):
        raise TypeError(
            f"logos.check: expected Theorem or _GroundProof, got {type(thm).__name__!r}"
        )
    from logos import evidence_cache

    thm._receipt = None
    saved_spec = _freeze_spec(thm._proof_spec)
    statement = thm.statement
    declarations = tuple(thm.declarations)
    name = thm.name
    evidence_cache._begin()
    try:
        evidence = thm._compile_evidence(force_run=True)
        artifact = artifact_bytes(
            name, statement, declarations, evidence, refresh_lemmas=True,
            annotations=thm._annotations(),
        )
        receipt = verify_artifact(artifact)
        thm._checked_spec = saved_spec
        thm._evidence = evidence
        thm._receipt = receipt
        # The receipt freshness check runs while the compiled-evidence plans
        # for this check are still reusable.  A mutation during verification
        # still clears the receipt and aborts the staged records.
        if thm.receipt is None:
            raise LogosProofError("proof changed during Rust verification")
    except BaseException:
        evidence_cache._abort()
        raise
    evidence_cache._commit()
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
