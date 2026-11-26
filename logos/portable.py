"""Export the first portable proof fragment and call the installed Rust verifier."""
from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess

from logos.expr import And, Expr, Implies, Var
from logos.kernel import AndElimL, AndElimR, HypRef, ImpliesIntro, ProofTerm

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
    name: str, statement: Expr, declarations: tuple[Var, ...], evidence: ProofTerm
) -> bytes:
    symbol_ids = {}
    declared = []
    for index, symbol in enumerate(declarations, 1):
        if type(symbol) is not Var or not isinstance(symbol.name, str):
            raise LogosProofError("portable declarations must be named Var objects")
        if id(symbol) in symbol_ids:
            raise LogosProofError(f"duplicate portable declaration {symbol.name!r}")
        if symbol.type is bool:
            sort = "prop"
        elif symbol.type is int:
            sort = "int"
        else:
            raise LogosProofError(f"unsupported declaration sort for {symbol.name!r}")
        symbol_id = f"p{index}"
        symbol_ids[id(symbol)] = symbol_id
        declared.append({"id": symbol_id, "name": symbol.name, "sort": sort})

    def proposition(expr):
        match expr:
            case Var(name, _):
                symbol_id = symbol_ids.get(id(expr))
                if symbol_id is None:
                    raise LogosProofError(f"undeclared proposition {name!r}")
                return {"tag": "symbol", "id": symbol_id}
            case And(left, right):
                return {"tag": "and", "left": proposition(left), "right": proposition(right)}
            case Implies(left, right):
                return {"tag": "implies", "left": proposition(left), "right": proposition(right)}
            case _:
                raise LogosProofError(f"unsupported portable proposition {type(expr).__name__}")

    def proof(term):
        match term:
            case ImpliesIntro(hyp, binder, body):
                return {
                    "tag": "implies_intro", "binder": binder,
                    "premise": proposition(hyp), "body": proof(body),
                }
            case HypRef(binder):
                return {"tag": "hyp_ref", "binder": binder}
            case AndElimL(child):
                return {"tag": "and_elim_l", "proof": proof(child)}
            case AndElimR(child):
                return {"tag": "and_elim_r", "proof": proof(child)}
            case _:
                raise LogosProofError(f"unsupported portable proof term {type(term).__name__}")

    try:
        return (
            json.dumps({
                "format": FORMAT, "theory": THEORY, "name": name,
                "declarations": declared, "custom_axioms": [], "lemmas": [],
                "target": proposition(statement), "proof": proof(evidence),
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
    result = response(invoke(["check", "--json", "--deny-custom-axioms", "-"], artifact), "check")
    digest = sha256(artifact).hexdigest()
    if (
        result.get("status") != "verified"
        or result.get("artifact_sha256") != digest
        or result.get("format") != FORMAT
        or result.get("theory") != THEORY
        or result.get("custom_axioms") != []
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
