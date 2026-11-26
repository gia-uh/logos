"""Export portable proofs and call the installed Rust verifier."""
from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess

from logos.expr import And, Expr, Implies, Var
from logos.kernel import (
    AndElimL, AndElimR, AndIntro, AxiomRef, HypRef, ImpliesIntro, ProofTerm, TheoremRef,
)

FORMAT = "logos-proof-v1"
THEORY = "logos-core-v1"
PROTOCOL_VERSION = 1


class LogosProofError(Exception):
    pass


@dataclass(frozen=True, slots=True)
class ProofReceipt:
    """A verification result for the exact immutable artifact bytes."""

    artifact: bytes
    artifact_sha256: str


def statement_declarations(statement: Expr) -> tuple[Var, ...]:
    """Collect free symbol objects in occurrence order in the supported fragment."""
    declarations = {}

    def visit(expr):
        match expr:
            case Var():
                declarations.setdefault(id(expr), expr)
            case And(left, right) | Implies(left, right):
                visit(left)
                visit(right)

    visit(statement)
    return tuple(declarations.values())


def artifact_bytes(
    name: str, statement: Expr, declarations: tuple[Var, ...], evidence: ProofTerm,
    *, refresh_lemmas: bool = False,
) -> bytes:
    from logos.theorem import Axiom, Theorem

    symbol_ids = {}
    declared = []
    used_ids = set()
    refs = {}
    pending = []
    axioms = []
    lemmas = []

    def declare(symbols):
        scope = set()
        for symbol in symbols:
            if type(symbol) is not Var or not isinstance(symbol.name, str):
                raise LogosProofError("portable declarations must be named Var objects")
            key = id(symbol)
            if key in scope:
                raise LogosProofError(f"duplicate portable declaration {symbol.name!r}")
            scope.add(key)
            if key in symbol_ids:
                continue
            if symbol.type is bool:
                sort = "prop"
            elif symbol.type is int:
                sort = "int"
            else:
                raise LogosProofError(f"unsupported declaration sort for {symbol.name!r}")
            symbol_id = f"p{len(declared) + 1}"
            register(symbol_id)
            symbol_ids[key] = symbol_id
            declared.append({"id": symbol_id, "name": symbol.name, "sort": sort})
        return scope

    def register(id_):
        if id_ in used_ids:
            raise LogosProofError(f"duplicate portable ID {id_!r}")
        used_ids.add(id_)

    def reference(ref, kind):
        key = id(ref)
        if key not in refs:
            if not isinstance(ref.name, str):
                raise LogosProofError("portable dependency IDs must be strings")
            id_ = ref.name or f"{kind}:{len(refs) + 1}"
            register(id_)
            refs[key] = id_
            pending.append((ref, id_))
        return {"tag": f"{kind}_ref", "id": refs[key]}

    def proposition(expr, scope):
        match expr:
            case Var(name, _):
                key = id(expr)
                if key not in scope:
                    raise LogosProofError(f"undeclared proposition {name!r}")
                return {"tag": "symbol", "id": symbol_ids[key]}
            case And(left, right):
                tag = "and"
            case Implies(left, right):
                tag = "implies"
            case _:
                raise LogosProofError(f"unsupported portable proposition {type(expr).__name__}")
        return {"tag": tag, "left": proposition(left, scope), "right": proposition(right, scope)}

    def proof(term, scope):
        match term:
            case ImpliesIntro(hyp, binder, body):
                return {
                    "tag": "implies_intro", "binder": binder,
                    "premise": proposition(hyp, scope), "body": proof(body, scope),
                }
            case HypRef(binder):
                return {"tag": "hyp_ref", "binder": binder}
            case AndIntro(left, right):
                return {"tag": "and_intro", "left": proof(left, scope), "right": proof(right, scope)}
            case AndElimL(child):
                return {"tag": "and_elim_l", "proof": proof(child, scope)}
            case AndElimR(child):
                return {"tag": "and_elim_r", "proof": proof(child, scope)}
            case AxiomRef(axiom) if isinstance(axiom, Axiom):
                return reference(axiom, "axiom")
            case TheoremRef(theorem) if isinstance(theorem, Theorem):
                return reference(theorem, "theorem")
            case _:
                raise LogosProofError(f"unsupported portable proof term {type(term).__name__}")

    try:
        scope = declare(declarations)
        target = proposition(statement, scope)
        target_proof = proof(evidence, scope)
        # References retain their live objects. Serializing each once lets Rust
        # detect cycles and check shared dependencies without trusting receipts.
        for ref, id_ in pending:
            if isinstance(ref, Axiom):
                scope = declare(statement_declarations(ref.statement))
                axioms.append({"id": id_, "statement": proposition(ref.statement, scope)})
            else:
                scope = declare(ref.declarations)
                lemmas.append({
                    "id": id_, "statement": proposition(ref.statement, scope),
                    "proof": proof(ref._dependency_evidence(refresh_lemmas), scope),
                })
        return (
            json.dumps({
                "format": FORMAT, "theory": THEORY, "name": name,
                "declarations": declared, "custom_axioms": axioms, "lemmas": lemmas,
                "target": target, "proof": target_proof,
            }, separators=(",", ":")) + "\n"
        ).encode("utf-8")
    except (TypeError, ValueError, RecursionError) as error:
        raise LogosProofError(f"could not encode portable proof: {error}") from error


def verify_artifact(artifact: bytes) -> ProofReceipt:
    executable = shutil.which("logos")
    if executable is None:
        raise LogosProofError("installed Rust logos checker not found on PATH")

    def invoke(args, data=None):
        try:
            return subprocess.run(
                [executable, *args], input=data, capture_output=True, timeout=10, check=False
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            raise LogosProofError(f"could not run Rust logos checker: {error}") from error

    def response(result, operation):
        if result.returncode != 0:
            diagnostic = result.stderr.decode("utf-8", errors="replace").strip()
            try:
                details = json.loads(diagnostic)
            except ValueError:
                details = None
            if isinstance(details, dict) and isinstance(details.get("error"), str):
                diagnostic = details["error"]
            raise LogosProofError(f"Rust logos {operation} failed ({result.returncode}): {diagnostic}")
        try:
            data = json.loads(result.stdout)
        except (ValueError, UnicodeError) as error:
            raise LogosProofError(f"invalid Rust logos {operation} response") from error
        if not isinstance(data, dict) or type(data.get("protocol_version")) is not int:
            raise LogosProofError(f"invalid Rust logos {operation} response")
        if data["protocol_version"] != PROTOCOL_VERSION:
            raise LogosProofError(f"unsupported Rust logos {operation} protocol")
        return data

    contract = response(invoke(["commands", "--json"]), "commands")
    if contract.get("proof_formats") != [FORMAT] or contract.get("theories") != [THEORY]:
        raise LogosProofError("Rust logos checker does not advertise the required proof format and theory")
    result = response(invoke(["check", "--json", "-"], artifact), "check")
    digest = sha256(artifact).hexdigest()
    if (
        result.get("status") != "verified"
        or result.get("artifact_sha256") != digest
        or result.get("format") != FORMAT
        or result.get("theory") != THEORY
        or not isinstance(result.get("custom_axioms"), list)
        or result.get("statement") != json.loads(artifact)["target"]
    ):
        raise LogosProofError("Rust logos checker returned no matching verification")
    return ProofReceipt(artifact, digest)


def export_proof(theorem, path: str | Path) -> ProofReceipt:
    """Write the current checked artifact for a named or anonymous proof."""
    from logos.theorem import _Proof

    if not isinstance(theorem, _Proof):
        raise TypeError("logos.export_proof expects a theorem or anonymous proof")
    receipt = theorem.receipt
    if receipt is None:
        raise LogosProofError("proof has no current Rust verification; call logos.check first")
    Path(path).write_bytes(receipt.artifact)
    return receipt
