"""Export portable proofs and call the installed Rust verifier."""
from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import threading

from logos.expr import (
    Add, And, App, Div, Eq, Expr, ExistsNode, ForallNode, Implies, Le, Len,
    Lit, Lt, Mul, Neg, Not, Nth, Or, Pow, Sorted, Sub, Var,
)
from logos.kernel import (
    AndElimL, AndElimR, AndIntro, AxiomRef, Block, Congr, CoreLaw, EqSubst, ExistsElim,
    ExistsIntro, ForallElim, CaseAnalysis, ExFalso, ForallIntro, HypRef, ImpliesElim,
    ImpliesIntro, Induction, Least, NotElim, NotIntro, OrIntroL, OrIntroR, ProofTerm,
    RecursorBase, RecursorStep, Refl, StepRef, Symm, TheoremRef, Trans,
    Have, Linear, Note, ProgramRef,
)

FORMAT = "logos-proof-v1"
THEORY = "logos-core-v1"
PROTOCOL_VERSION = 1


@dataclass(frozen=True, slots=True)
class _CheckerIdentity:
    """What identifies the executable a process measured its capabilities from."""

    path: str
    real_path: str
    device: int
    inode: int
    size: int
    mtime_ns: int
    ctime_ns: int
    mode: int


_CAPABILITY_LOCK = threading.Lock()
_CAPABILITY_MEASUREMENT: tuple[_CheckerIdentity, dict] | None = None


class LogosProofError(Exception):
    """A rejected proof.

    ``details`` is machine-readable context for failures raised by the
    authoring layer; most errors leave it as ``None``.
    """

    def __init__(self, message="", *, details=None):
        super().__init__(message)
        self.details = details


@dataclass(frozen=True, slots=True)
class ProofReceipt:
    """A verification result for the exact immutable artifact bytes."""

    artifact: bytes
    artifact_sha256: str


def statement_declarations(statement: Expr) -> tuple[Var, ...]:
    """Collect free symbol objects in occurrence order in the supported fragment."""
    import dataclasses

    declarations = {}

    def visit(expr, bound):
        if isinstance(expr, Var):
            if id(expr) not in bound:
                declarations.setdefault(id(expr), expr)
            return
        if isinstance(expr, Lit):
            return
        if isinstance(expr, (ForallNode, ExistsNode)):
            visit(expr.body, bound | {id(expr.var)})
            return
        if not dataclasses.is_dataclass(expr):
            return
        for field in dataclasses.fields(expr):
            value = getattr(expr, field.name)
            if isinstance(value, Expr):
                visit(value, bound)
            elif isinstance(value, (list, tuple)):
                for item in value:
                    if isinstance(item, Expr):
                        visit(item, bound)
                    elif isinstance(item, (list, tuple)):
                        for nested in item:
                            if isinstance(nested, Expr):
                                visit(nested, bound)

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
    from logos.sequence import SeqType
    if isinstance(type_, SeqType):
        return "seq"
    raise LogosProofError(f"unsupported portable sort {type_!r}")


def _result_type(expr):
    match expr:
        case Var(_, type_):
            return type_
        case Lit(value):
            return type(value)
        case Add() | Sub() | Mul() | Div() | Pow() | Neg() | Len() | Nth():
            return int
        case Sorted():
            return bool
        case Eq() | Lt() | And() | Or() | Not() | Implies() | ForallNode() | ExistsNode():
            return bool
        case App(_, _, symbol) if symbol is not None:
            return symbol.result_type or _result_type(symbol.body)
        case _:
            raise LogosProofError(f"unsupported portable function result {type(expr).__name__}")


def artifact_bytes(
    name: str, statement: Expr, declarations: tuple[Var, ...], evidence: ProofTerm,
    *, refresh_lemmas: bool = False, annotations: dict | None = None,
) -> bytes:
    from logos.theorem import Axiom, Theorem

    authored = {}
    for key in ("claim", "strategy"):
        if annotations is not None:
            text = annotations.get(key)
            if text is not None:
                if not isinstance(text, str):
                    raise LogosProofError(f"portable annotation {key!r} must be a string")
                if text:
                    authored[key] = text
    if annotations is not None and annotations.get("contract") is not None:
        contract = annotations["contract"]
        if not isinstance(contract, (list, tuple)):
            raise LogosProofError("portable annotation 'contract' must be a list")
        clauses = []
        for item in contract:
            if not isinstance(item, dict):
                raise LogosProofError("each contract annotation must be an object")
            kind = item.get("kind")
            name = item.get("name")
            line = item.get("line")
            if not isinstance(kind, str) or not isinstance(name, str):
                raise LogosProofError("contract annotations need string kind and name")
            clause = {"kind": kind, "name": name}
            if line is not None:
                if type(line) is not int or line < 1:
                    raise LogosProofError("contract annotation line must be a positive integer")
                clause["line"] = line
            clauses.append(clause)
        if clauses:
            authored["contract"] = clauses

    symbol_ids = {}
    declared = []
    used_ids = set()
    refs = {}
    pending = []
    axioms = []
    lemmas = []
    functions = []
    function_ids = {}
    programs = []
    program_ids = {}
    program_scopes = {}
    encoding_programs = set()

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
            if symbol.recursor is not None:
                base, step, previous = symbol.recursor
                declaration["recursor"] = {
                    "base": proposition(base, set(), ()),
                    "step": proposition(step, set(), (symbol.params[0], previous)),
                }
            functions.append(declaration)
        return function_ids[key]

    def encode_statement(statement, scope, names):
        from logos.programs import Assign, Call, If, Return, While
        if isinstance(statement, Assign):
            if statement.name not in names:
                raise LogosProofError(f"unknown program assignment target {statement.name!r}")
            return {"tag": "assign", "name": names[statement.name],
                    "value": proposition(statement.value, scope)}
        if isinstance(statement, If):
            return {"tag": "if", "condition": proposition(statement.condition, scope),
                    "then_body": [encode_statement(item, scope, names) for item in statement.then_body],
                    "else_body": [encode_statement(item, scope, names) for item in statement.else_body]}
        if isinstance(statement, While):
            return {"tag": "while", "condition": proposition(statement.condition, scope),
                    "body": [encode_statement(item, scope, names) for item in statement.body],
                    "invariant": proposition(statement.invariant, scope),
                    "variant": proposition(statement.variant, scope),
                    **({"invariants": [
                        {"name": clause.name, "proposition": proposition(clause.expr, scope)}
                        for clause in statement.invariants
                    ]} if statement.invariants else {}),
                    **({"decreases_name": statement.decreases_name}
                       if statement.decreases_name else {})}
        if isinstance(statement, Call):
            if statement.target not in names:
                raise LogosProofError(f"unknown call target {statement.target!r}")
            return {"tag": "call", "target": names[statement.target],
                    "call": statement.id,
                    "args": [proposition(arg, scope) for arg in statement.args]}
        if isinstance(statement, Return):
            return {"tag": "return", "value": proposition(statement.value, scope)}
        raise LogosProofError(f"unsupported program statement {type(statement).__name__}")

    def encode_program(program, scope):
        from logos.programs import call_statements
        key = id(program)
        if key in program_scopes:
            return
        if key in encoding_programs:
            raise LogosProofError(
                f"cyclic call dependency through program {program.name!r}"
            )
        encoding_programs.add(key)
        for call in call_statements(program):
            encode_program(call.callee.program, None)
        scope = declare(tuple(item.var for item in program.variables))
        program_scopes[key] = scope
        names = {item.name: symbol_ids[id(item.var)] for item in program.variables}
        function = function_id(program.function)
        body = [encode_statement(statement, scope, names) for statement in program.body]
        obligations = []
        for name, evidence in program.obligations.items():
            obligations.append({"id": name, "proof": proof(evidence, scope)})
        calls = []
        for call in call_statements(program):
            callee = call.callee.program
            callee_scope = program_scopes[id(callee)]
            calls.append({
                "id": call.id,
                "callee": program_ids[id(callee)],
                "line": call.line,
                "requires": proposition(callee.requires, callee_scope),
                "requires_clauses": [
                    {"name": clause.name, "proposition": proposition(clause.expr, callee_scope)}
                    for clause in callee.requires_clauses
                ],
                "ensures": proposition(callee.ensures, callee_scope),
                "ensures_clauses": [
                    {"name": clause.name, "proposition": proposition(clause.expr, callee_scope)}
                    for clause in callee.ensures_clauses
                ],
            })
        id_ = f"g{len(program_ids) + 1}"
        register(id_)
        program_ids[key] = id_
        programs.append({
            "id": id_,
            "function": function,
            "params": [symbol_ids[id(item.var)] for item in program.params],
            "locals": [symbol_ids[id(item.var)] for item in program.locals],
            "ghosts": [symbol_ids[id(item.var)] for item in program.ghosts],
            "result": symbol_ids[id(program.result.var)],
            "requires": proposition(program.requires, scope),
            "ensures": proposition(program.ensures, scope),
            "requires_clauses": [
                {"name": clause.name, "proposition": proposition(clause.expr, scope)}
                for clause in program.requires_clauses
            ],
            "ensures_clauses": [
                {"name": clause.name, "proposition": proposition(clause.expr, scope)}
                for clause in program.ensures_clauses
            ],
            "body": body,
            "calls": calls,
            "obligations": obligations,
        })
        encoding_programs.discard(key)

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
            case Lit(value) if value is False:
                return {"tag": "false"}
            case Neg(operand) | Not(operand):
                return {"tag": type(expr).__name__.lower(), "operand": encode(operand)}
            case Pow(base, Lit(exponent)) if type(exponent) is int and 0 <= exponent <= 2**32 - 1:
                return {"tag": "pow", "base": encode(base), "exponent": exponent}
            case ForallNode(var, body) | ExistsNode(var, body):
                tag = "forall" if isinstance(expr, ForallNode) else "exists"
                return {"tag": tag, "name": var.name, "sort": _sort(var.type),
                        "body": proposition(body, scope, (*bound, var))}
            case App(_, args, symbol):
                return {"tag": "app", "id": function_id(symbol), "args": [encode(arg) for arg in args]}
            case Add(left, right) | Sub(left, right) | Mul(left, right) | Div(left, right) | Eq(left, right) | Le(left, right) | Lt(left, right) | And(left, right) | Or(left, right) | Implies(left, right):
                return {"tag": type(expr).__name__.lower(), "left": encode(left), "right": encode(right)}
            case Len(seq):
                return {"tag": "len", "seq": encode(seq)}
            case Nth(seq, index):
                return {"tag": "nth", "seq": encode(seq), "index": encode(index)}
            case Sorted(seq):
                return {"tag": "sorted", "seq": encode(seq)}
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
            case ExistsIntro(witness, body, ExistsNode() as goal):
                return {"tag": "exists_intro", "goal": encode(goal),
                        "witness": encode(witness), "proof": derive(body)}
            case ExistsElim(child, var, binder, body):
                return {"tag": "exists_elim", "proof": derive(child),
                        "name": var.name, "binder": binder,
                        "body": proof(body, scope, (*bound, var))}
            case EqSubst(child, var, template, body):
                return {"tag": "eq_subst", "equality": derive(child),
                        "context": proposition(template, scope, (*bound, var)),
                        "proof": derive(body)}
            case Induction(lower, var, predicate, base, step):
                return {"tag": "induction", "bound": encode(lower), "name": var.name,
                        "predicate": proposition(predicate, scope, (*bound, var)),
                        "base": derive(base), "step": derive(step)}
            case Least(lower, var, predicate, nonempty):
                return {"tag": "least", "bound": encode(lower), "name": var.name,
                        "predicate": proposition(predicate, scope, (*bound, var)),
                        "nonempty": derive(nonempty)}
            case RecursorBase(function):
                return {"tag": "recursor_base", "id": function_id(function)}
            case RecursorStep(function, argument, nonnegative):
                return {"tag": "recursor_step", "id": function_id(function),
                        "argument": encode(argument), "proof": derive(nonnegative)}
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
            case Linear(conclusion, terms):
                return {"tag": "linear", "conclusion": encode(conclusion),
                        "terms": [{"binder": binder, "coefficient": coefficient}
                                  for binder, coefficient in terms]}
            case Have(binder, statement, fact, body):
                return {"tag": "have", "binder": binder, "statement": encode(statement),
                        "proof": derive(fact), "body": derive(body)}
            case Note(text, child):
                if not isinstance(text, str) or not text.strip():
                    raise LogosProofError("proof notes must be nonempty strings")
                return {"tag": "note", "text": text, "body": derive(child)}
            case ProgramRef(program, _conclusion):
                encode_program(program, scope)
                return {"tag": "program_ref", "id": program_ids[id(program)]}
            case Block(steps, result):
                return {"tag": "block", "steps": [derive(step) for step in steps], "result": result}
            case StepRef(index):
                return {"tag": "step_ref", "index": index}
            case ImpliesIntro(hyp, binder, body):
                return {
                    "tag": "implies_intro", "binder": binder,
                    "premise": encode(hyp), "body": derive(body),
                }
            case ImpliesElim(implication, premise):
                return {"tag": "implies_elim", "implication": derive(implication),
                        "premise": derive(premise)}
            case OrIntroL(child, other):
                return {"tag": "or_intro_l", "proof": derive(child), "other": encode(other)}
            case OrIntroR(other, child):
                return {"tag": "or_intro_r", "proof": derive(child), "other": encode(other)}
            case CaseAnalysis(child, binder, left, right):
                return {"tag": "or_elim", "proof": derive(child), "binder": binder,
                        "left": derive(left), "right": derive(right)}
            case NotIntro(child):
                return {"tag": "not_intro", "proof": derive(child)}
            case NotElim(negation, premise):
                return {"tag": "not_elim", "negation": derive(negation), "premise": derive(premise)}
            case ExFalso(child, conclusion):
                return {"tag": "ex_falso", "proof": derive(child), "conclusion": encode(conclusion)}
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
                **({"programs": programs} if programs else {}),
                **({"annotations": authored} if authored else {}),
                "target": target, "proof": target_proof,
            }, separators=(",", ":")) + "\n"
        ).encode("utf-8")
    except (TypeError, ValueError, RecursionError) as error:
        raise LogosProofError(f"could not encode portable proof: {error}") from error


def _checker_executable() -> str:
    executable = shutil.which("logos")
    if executable is None:
        raise LogosProofError("installed Rust logos checker not found on PATH")
    return executable


def _checker_invoke(executable: str, args, data=None):
    try:
        return subprocess.run(
            [executable, *args], input=data, capture_output=True, timeout=10, check=False
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise LogosProofError(f"could not run Rust logos checker: {error}") from error


def _checker_error(result, operation: str) -> str:
    diagnostic = result.stderr.decode("utf-8", errors="replace").strip()
    try:
        details = json.loads(diagnostic)
    except ValueError:
        details = None
    if isinstance(details, dict) and isinstance(details.get("error"), str):
        diagnostic = details["error"]
    return f"Rust logos {operation} failed ({result.returncode}): {diagnostic}"


def _checker_response(result, operation: str):
    if result.returncode != 0:
        raise LogosProofError(_checker_error(result, operation))
    try:
        data = json.loads(result.stdout)
    except (ValueError, UnicodeError) as error:
        raise LogosProofError(f"invalid Rust logos {operation} response") from error
    if not isinstance(data, dict) or type(data.get("protocol_version")) is not int:
        raise LogosProofError(f"invalid Rust logos {operation} response")
    if data["protocol_version"] != PROTOCOL_VERSION:
        raise LogosProofError(f"unsupported Rust logos {operation} protocol")
    return data


def _checker_identity(executable: str) -> _CheckerIdentity | None:
    """Identify the exact file behind a PATH resolution, or None if uncertain."""
    try:
        info = os.stat(executable)
    except OSError:
        return None
    return _CheckerIdentity(
        path=os.path.abspath(executable),
        real_path=os.path.realpath(executable),
        device=info.st_dev,
        inode=info.st_ino,
        size=info.st_size,
        mtime_ns=info.st_mtime_ns,
        ctime_ns=info.st_ctime_ns,
        mode=info.st_mode,
    )


def _require_checker_capabilities(contract: dict) -> None:
    if contract.get("proof_formats") != [FORMAT] or contract.get("theories") != [THEORY]:
        raise LogosProofError("Rust logos checker does not advertise the required proof format and theory")


def _checker_capabilities(executable: str) -> dict:
    """Measure a compatible checker once per unchanged executable in this process."""
    global _CAPABILITY_MEASUREMENT

    identity = _checker_identity(executable)
    if identity is not None:
        with _CAPABILITY_LOCK:
            measured = _CAPABILITY_MEASUREMENT
        if measured is not None and measured[0] == identity:
            _require_checker_capabilities(measured[1])
            return measured[1]

    contract = _checker_response(
        _checker_invoke(executable, ["commands", "--json"]), "commands"
    )
    _require_checker_capabilities(contract)
    if identity is not None:
        if _checker_identity(executable) != identity:
            raise LogosProofError("Rust logos checker changed while its capabilities were measured")
        with _CAPABILITY_LOCK:
            _CAPABILITY_MEASUREMENT = (identity, contract)
    return contract


def verify_artifact(artifact: bytes) -> ProofReceipt:
    executable = _checker_executable()

    # The capability contract may be reused; the check below still runs for
    # every artifact, so a warm cache never becomes a cached verdict.
    _checker_capabilities(executable)
    result = _checker_response(
        _checker_invoke(executable, ["check", "--json", "-"], artifact), "check"
    )
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


def inspect_artifact(artifact: bytes) -> str:
    """Return the Rust checker's Markdown reading of these exact proof bytes."""
    # Re-check the same bytes first: the Markdown must describe a current
    # verification, not a certificate that has since changed.
    verify_artifact(artifact)
    executable = _checker_executable()
    result = _checker_invoke(executable, ["inspect", "--markdown", "-"], artifact)
    if result.returncode != 0:
        raise LogosProofError(_checker_error(result, "inspect"))
    try:
        markdown = result.stdout.decode("utf-8")
    except UnicodeError as error:
        raise LogosProofError("invalid Rust logos inspect response") from error
    if not markdown.startswith("# Checked proof\n") or "## Theorem" not in markdown:
        raise LogosProofError("Rust logos inspect returned no checked derivation")
    return markdown



def export_proof(theorem, path: str | Path) -> ProofReceipt:
    """Write the current checked artifact for a named or anonymous proof."""
    from logos.theorem import _Proof

    declaration = getattr(theorem, "__logos_function__", None)
    if declaration is not None:
        return declaration.export(path)
    if not isinstance(theorem, _Proof):
        raise TypeError("logos.export_proof expects a theorem, anonymous proof or @logos.function")
    theorem._revalidate()
    receipt = theorem.receipt
    if receipt is None:
        raise LogosProofError("proof has no current Rust verification; call logos.check first")
    Path(path).write_bytes(receipt.artifact)
    return receipt
