"""Export portable proofs and call the installed Rust verifier."""
from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess

from logos.expr import Add, And, App, Eq, Expr, ForallNode, Implies, Lit, Mul, Neg, Pow, Sub, Var
from logos.kernel import (
    AndElimL, AndElimR, AndIntro, AxiomRef, Block, Congr, CoreLaw, ForallElim,
    ForallIntro, HypRef, ImpliesIntro, ProofTerm, Refl, StepRef, Symm, TheoremRef, Trans,
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

    def visit(expr, bound):
        match expr:
            case Var() if id(expr) not in bound:
                declarations.setdefault(id(expr), expr)
            case ForallNode(var, body):
                visit(body, bound | {id(var)})
            case App(_, args):
                for arg in args:
                    visit(arg, bound)
            case Add(left, right) | Sub(left, right) | Mul(left, right) | Eq(left, right) | And(left, right) | Implies(left, right) | Pow(left, right):
                visit(left, bound)
                visit(right, bound)
            case Neg(operand):
                visit(operand, bound)

    visit(statement, set())
    return tuple(declarations.values())


def _integer_decimal(value: int) -> str:
    try:
        return str(value)
    except ValueError:
        # Python limits decimal conversion of a single int. Serialize in
        # chunks without changing that process-wide setting.
        sign = "-" if value < 0 else ""
        value = abs(value)
        base = 10**500
        parts = []
        while value >= base:
            value, remainder = divmod(value, base)
            parts.append(f"{remainder:0500d}")
        return sign + str(value) + "".join(reversed(parts))


def _sort(type_):
    if type_ is int:
        return "int"
    if type_ is bool:
        return "prop"
    raise LogosProofError(f"unsupported portable sort {type_!r}")


def _result_type(expr):
    match expr:
        case Var(_, type_):
            return type_
        case Lit(value):
            return type(value)
        case Add() | Sub() | Mul() | Pow() | Neg():
            return int
        case Eq() | And() | Implies() | ForallNode():
            return bool
        case App(_, _, symbol) if symbol is not None:
            return symbol.result_type or _result_type(symbol.body)
        case _:
            raise LogosProofError(f"unsupported portable function result {type(expr).__name__}")


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
    functions = []
    function_ids = {}

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
            sort = _sort(symbol.type)
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

    def function_id(symbol):
        if symbol is None:
            raise LogosProofError("application has no function declaration")
        key = id(symbol)
        if key not in function_ids:
            id_ = f"f{len(function_ids) + 1}"
            register(id_)
            function_ids[key] = id_
            declaration = {
                "id": id_, "name": symbol.name,
                "params": [_sort(param.type) for param in symbol.params],
                "result": _sort(symbol.result_type or _result_type(symbol.body)),
            }
            if symbol.body is not None:
                declaration["body"] = proposition(symbol.body, set(), tuple(symbol.params))
            functions.append(declaration)
        return function_ids[key]

    def proposition(expr, scope, bound=()):
        def encode(child):
            return proposition(child, scope, bound)

        match expr:
            case Var(name, _):
                for index, var in enumerate(reversed(bound)):
                    if var is expr:
                        return {"tag": "bound", "index": index}
                key = id(expr)
                if key not in scope:
                    raise LogosProofError(f"undeclared proposition or term {name!r}")
                return {"tag": "symbol", "id": symbol_ids[key]}
            case Lit(value) if type(value) is int:
                return {"tag": "int", "value": _integer_decimal(value)}
            case Neg(operand):
                return {"tag": "neg", "operand": encode(operand)}
            case Pow(base, Lit(exponent)) if type(exponent) is int and 0 <= exponent <= 2**32 - 1:
                return {"tag": "pow", "base": encode(base), "exponent": exponent}
            case ForallNode(var, body):
                return {"tag": "forall", "name": var.name, "sort": _sort(var.type),
                        "body": proposition(body, scope, (*bound, var))}
            case App(_, args, symbol):
                return {"tag": "app", "id": function_id(symbol), "args": [encode(arg) for arg in args]}
            case Add(left, right) | Sub(left, right) | Mul(left, right) | Eq(left, right) | And(left, right) | Implies(left, right):
                return {"tag": type(expr).__name__.lower(), "left": encode(left), "right": encode(right)}
            case _:
                raise LogosProofError(f"unsupported portable proposition or term {type(expr).__name__}")

    def proof(term, scope, bound=()):
        def encode(child):
            return proposition(child, scope, bound)

        def derive(child):
            return proof(child, scope, bound)

        match term:
            case ForallIntro(var, body):
                return {"tag": "forall_intro", "name": var.name, "sort": _sort(var.type),
                        "body": proof(body, scope, (*bound, var))}
            case ForallElim(child, value):
                return {"tag": "forall_elim", "proof": derive(child), "term": encode(value)}
            case Refl(expr):
                return {"tag": "refl", "term": encode(expr)}
            case Symm(child):
                return {"tag": "symm", "proof": derive(child)}
            case Trans(left, right):
                return {"tag": "trans", "left": derive(left), "right": derive(right)}
            case Congr(var, context, child):
                return {"tag": "congr", "context": proposition(context, scope, (*bound, var)),
                        "proof": derive(child)}
            case CoreLaw(id_, args):
                return {"tag": "core_law", "id": id_, "args": [encode(arg) for arg in args]}
            case Block(steps, result):
                return {"tag": "block", "steps": [derive(step) for step in steps], "result": result}
            case StepRef(index):
                return {"tag": "step_ref", "index": index}
            case ImpliesIntro(hyp, binder, body):
                return {
                    "tag": "implies_intro", "binder": binder,
                    "premise": encode(hyp), "body": derive(body),
                }
            case HypRef(binder):
                return {"tag": "hyp_ref", "binder": binder}
            case AndIntro(left, right):
                return {"tag": "and_intro", "left": derive(left), "right": derive(right)}
            case AndElimL(child):
                return {"tag": "and_elim_l", "proof": derive(child)}
            case AndElimR(child):
                return {"tag": "and_elim_r", "proof": derive(child)}
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
                **({"functions": functions} if functions else {}),
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
