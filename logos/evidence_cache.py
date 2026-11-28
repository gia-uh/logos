"""Persistent per-lemma reuse of compiled Python proof evidence.

A checked theorem has two parts: the Python proof body that builds a proof
term, and the certificate that the Rust checker replays.  This module caches
only the first part.  A cache record holds the compiled ``ProofTerm`` graph of
one lemma, keyed by the declared statement, the proof implementation, the
relevant dependency declarations and the compiler identity.  A hit is
untrusted evidence: ``logos.check`` still builds the complete artifact and
sends it to the installed Rust checker, which decides the verdict.

Eligibility is deliberately narrow.  Only a book-style authored proof function
whose source and code are stable, whose closure is empty, whose globals are
immutable values or live declarations, and whose evidence can be encoded with
the portable proof vocabulary may be cached.  Anything else executes as
before.
"""
from __future__ import annotations

import builtins
from dataclasses import fields, is_dataclass
import dis
from hashlib import sha256
import inspect
import json
import os
from pathlib import Path
import sys
import tempfile
import threading
from types import CodeType, FunctionType, ModuleType
import weakref

from logos.expr import (
    Add, And, App, CaseExpr, Div, Eq, ExistsNode, Expr, ForallNode, Ge, Gt,
    Implies, Le, Len, Lit, Lt, Mod, Mul, Neg, Neq, Not, Nth, Or, Pow, Sorted,
    Sub, Var,
)
from logos.kernel import (
    AndElimL, AndElimR, AndIntro, Axiom, AxiomRef, Block, CaseAnalysis, Congr,
    CoreLaw, EqSubst, ExFalso, ExistsElim, ExistsIntro, ForallElim, ForallIntro,
    Have, HypRef, ImpliesElim, ImpliesIntro, Induction, Least, Linear, Note,
    NotElim, NotIntro, OrIntroL, OrIntroR, ProgramRef, ProofTerm, RecursorBase,
    RecursorStep, Refl, StepRef, Subst, Symm, TheoremRef, Trans,
)
from logos.portable import FORMAT, PROTOCOL_VERSION, THEORY

RECORD_FORMAT = "logos-evidence-v1"
RECORD_SUFFIX = ".json"
MAX_RECORD_BYTES = 64 * 1024 * 1024
MAX_NODES = 2_000_000
MAX_DEPTH = 200

# Builtins that may observe or change state outside the proof's own evidence.
_UNSAFE_BUILTINS = frozenset({
    "__import__", "breakpoint", "compile", "delattr", "eval", "exec", "exit",
    "getattr", "globals", "hash", "help", "id", "input", "locals", "memoryview",
    "object", "open", "quit", "setattr", "super", "type", "vars",
})

# Bytecode that writes outside the local frame, imports at proof time, or
# suspends the frame.  A proof that does any of these is not a pure function of
# its source and declared inputs.
_UNSAFE_OPNAMES = frozenset({
    "DELETE_DEREF", "DELETE_GLOBAL", "IMPORT_NAME", "IMPORT_FROM",
    "STORE_ATTR", "STORE_DEREF", "STORE_GLOBAL", "STORE_SUBSCR",
    "YIELD_VALUE", "YIELD_FROM", "GET_AWAITABLE", "GET_AITER", "GET_ANEXT",
})

_EXPR_TYPES = {
    cls.__name__: cls for cls in (
        Add, And, App, CaseExpr, Div, Eq, ExistsNode, ForallNode, Ge, Gt,
        Implies, Le, Len, Lit, Lt, Mod, Mul, Neg, Neq, Not, Nth, Or, Pow,
        Sorted, Sub, Var,
    )
}

_PROOF_TYPES = {
    cls.__name__: cls for cls in (
        AndElimL, AndElimR, AndIntro, Axiom, AxiomRef, Block, CaseAnalysis,
        Congr, CoreLaw, EqSubst, ExFalso, ExistsElim, ExistsIntro, ForallElim,
        ForallIntro, Have, HypRef, ImpliesElim, ImpliesIntro, Induction, Least,
        Linear, Note, NotElim, NotIntro, OrIntroL, OrIntroR, ProgramRef,
        RecursorBase, RecursorStep, Refl, StepRef, Subst, Symm, TheoremRef,
        Trans,
    )
}

# Terms whose fields cannot be represented without an executable or identity
# payload.  They keep executing on every check.
_UNSUPPORTED_PROOF_TYPES = frozenset({
    "ProgramRef", "RecursorBase", "RecursorStep", "Subst",
})


class _Ineligible(Exception):
    """This theorem cannot use the persistent evidence cache."""


class _Unsupported(_Ineligible):
    """The compiled evidence is outside the cache's vocabulary."""


_COMPILER_LOCK = threading.Lock()
_COMPILER_IDENTITY: str | None = None
_COMPILER_IDENTITY_READY = False

_STATE = threading.local()


# ── Configuration ────────────────────────────────────────────────────────────


def _enabled() -> bool:
    """Whether the process should read and write cached compiled evidence."""
    value = os.environ.get("LOGOS_CACHE")
    if value is None:
        legacy = os.environ.get("LOGOS_NO_CACHE")
        if legacy is not None:
            return legacy.strip().lower() in {"", "0", "false", "no", "off"}
        return True
    return value.strip().lower() not in {"0", "false", "no", "off", "disable", "disabled", "none"}


def _directory() -> Path:
    """The directory that holds evidence records.

    ``LOGOS_CACHE_DIR`` overrides it exactly.  Otherwise the platform's user
    cache directory is used (``$XDG_CACHE_HOME`` or ``~/.cache`` on Linux).
    """
    override = os.environ.get("LOGOS_CACHE_DIR")
    if override:
        return Path(os.path.expanduser(override))
    if sys.platform == "win32":
        base = os.environ.get("LOCALAPPDATA")
        root = Path(base) if base else Path.home() / "AppData" / "Local"
        return root / "logos" / "evidence-v1"
    if sys.platform == "darwin":
        return Path.home() / "Library" / "Caches" / "logos" / "evidence-v1"
    base = os.environ.get("XDG_CACHE_HOME")
    root = Path(base) if base else Path.home() / ".cache"
    return root / "logos" / "evidence-v1"


def _compiler_identity() -> str | None:
    """A content digest of the Logos Python sources and proof vocabulary.

    A changed checker is handled by the Rust capability cache; this identity
    covers the Python compiler that produced the cached evidence.
    """
    global _COMPILER_IDENTITY, _COMPILER_IDENTITY_READY
    with _COMPILER_LOCK:
        if _COMPILER_IDENTITY_READY:
            return _COMPILER_IDENTITY
        try:
            root = Path(__file__).resolve().parent
            digest = sha256()
            digest.update(
                f"{RECORD_FORMAT}\0{FORMAT}\0{THEORY}\0{PROTOCOL_VERSION}\0"
                f"{sys.implementation.name}\0{sys.version_info.major}.{sys.version_info.minor}\0".encode()
            )
            for path in sorted(root.rglob("*.py")):
                if "__pycache__" in path.parts:
                    continue
                relative = path.relative_to(root).as_posix()
                digest.update(relative.encode())
                digest.update(b"\0")
                digest.update(path.read_bytes())
                digest.update(b"\0")
            _COMPILER_IDENTITY = digest.hexdigest()
        except OSError:
            _COMPILER_IDENTITY = None
        _COMPILER_IDENTITY_READY = True
        return _COMPILER_IDENTITY


# ── Variable tables ──────────────────────────────────────────────────────────


def _sort(value) -> str:
    if value is int:
        return "int"
    if value is bool:
        return "prop"
    if value is object:
        return "object"
    from logos.sequence import SeqType
    if isinstance(value, SeqType):
        return "seq"
    raise _Unsupported(f"unsupported variable sort {value!r}")


def _sort_value(code: str):
    if code == "int":
        return int
    if code == "prop":
        return bool
    if code == "object":
        return object
    if code == "seq":
        from logos.sequence import Seq
        return Seq
    raise _Unsupported(f"unsupported cached variable sort {code!r}")


class _Vars:
    """Deterministic identity map between cached variable names and objects."""

    def __init__(self):
        self.ids: dict[int, str] = {}
        self.objects: dict[str, Var] = {}
        self.next_local = 0

    def _bind(self, name: str, var: Var) -> None:
        self.ids[id(var)] = name
        self.objects[name] = var

    def _claim(self, var: Var, *, prefix: str) -> str:
        key = self.ids.get(id(var))
        if key is not None:
            return key
        if prefix == "s":
            index = sum(1 for name in self.objects if name.startswith("s"))
            name = f"s{index}"
        elif prefix == "b":
            index = sum(1 for name in self.objects if name.startswith("b"))
            name = f"b{index}"
        else:
            name = f"l{self.next_local}"
            self.next_local += 1
        self._bind(name, var)
        return name

    def _fresh(self, name: str, sort: str) -> Var:
        key = f"l{self.next_local}"
        self.next_local += 1
        var = Var(name, _sort_value(sort))
        self._bind(key, var)
        return var

    def _lookup(self, var: Var) -> str:
        key = self.ids.get(id(var))
        if key is None:
            raise _Unsupported(f"unbound variable {var.name!r} in cached proof")
        return key


def _statement_vars(statement: Expr) -> _Vars:
    """Assign ids to every variable in a statement in deterministic order."""
    table = _Vars()

    def visit(expr, bound):
        if isinstance(expr, Var):
            if id(expr) not in table.ids:
                table._claim(expr, prefix="b" if id(expr) in bound else "s")
            return
        if isinstance(expr, Lit):
            return
        if isinstance(expr, (ForallNode, ExistsNode)):
            if id(expr.var) not in table.ids:
                table._claim(expr.var, prefix="b")
            visit(expr.body, bound | {id(expr.var)})
            return
        if not is_dataclass(expr):
            raise _Unsupported(f"unsupported statement node {type(expr).__name__}")
        for field in fields(expr):
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
    return table


# ── Value codec ──────────────────────────────────────────────────────────────


def _int_text(value: int) -> str:
    return ("-" if value < 0 else "") + format(abs(value), "x")


def _int_value(text) -> int:
    if not isinstance(text, str) or not text:
        raise _Unsupported("invalid cached integer")
    sign = -1 if text.startswith("-") else 1
    digits = text[1:] if text[:1] in "+-" else text
    if not digits or any(ch not in "0123456789abcdef" for ch in digits):
        raise _Unsupported("invalid cached integer")
    return sign * int(digits, 16)


def _encode(value, table: _Vars, state, depth=0, *, ref_paths=None):
    if depth > MAX_DEPTH:
        raise _Unsupported("cached value is too deep")
    state[0] += 1
    if state[0] > MAX_NODES:
        raise _Unsupported("cached value is too large")

    if isinstance(value, Var):
        key = table.ids.get(id(value))
        if key is None:
            # A proof-local binder introduced by a term such as ForallIntro,
            # ExistsElim or Congr.  Its name and sort travel with the record;
            # repeated uses share one decoded Var.
            key = f"l{table.next_local}"
            table.next_local += 1
            table._bind(key, value)
        return {"k": "var", "i": key, "n": value.name, "s": _sort(value.type)}
    if isinstance(value, ProofTerm):
        name = type(value).__name__
        if name in _UNSUPPORTED_PROOF_TYPES or name not in _PROOF_TYPES:
            raise _Unsupported(f"unsupported proof term {name}")
        if name in {"TheoremRef", "AxiomRef"}:
            if ref_paths is None:
                raise _Unsupported("reference outside a cache plan")
            obj = value.theorem if name == "TheoremRef" else value.axiom
            path = ref_paths.get(id(obj))
            if path is None:
                raise _Unsupported("unbound reference in cached evidence")
            return {"k": "refp", "c": name, "p": path}
        return {
            "k": "proof",
            "c": name,
            "f": {
                field.name: _encode(getattr(value, field.name), table, state, depth + 1,
                                     ref_paths=ref_paths)
                for field in fields(value)
            },
        }
    if isinstance(value, Expr):
        name = type(value).__name__
        if name not in _EXPR_TYPES or name in {"App", "CaseExpr"}:
            raise _Unsupported(f"unsupported expression {name}")
        if name == "Lit":
            item = value.value
            if item is None:
                return {"k": "lit", "v": None}
            if type(item) is bool:
                return {"k": "lit", "b": item}
            if type(item) is int:
                return {"k": "lit", "i": _int_text(item)}
            if type(item) is str:
                return {"k": "lit", "s": item}
            raise _Unsupported(f"unsupported literal {type(item).__name__}")
        return {
            "k": "expr",
            "c": name,
            "f": {
                field.name: _encode(getattr(value, field.name), table, state, depth + 1,
                                     ref_paths=ref_paths)
                for field in fields(value)
            },
        }
    if value is None:
        return {"k": "none"}
    if type(value) is bool:
        return {"k": "bool", "v": value}
    if type(value) is int:
        return {"k": "int", "v": _int_text(value)}
    if type(value) is str:
        return {"k": "str", "v": value}
    if isinstance(value, tuple):
        return {"k": "tuple",
                "v": [_encode(item, table, state, depth + 1, ref_paths=ref_paths)
                      for item in value]}
    raise _Unsupported(f"unsupported cached value {type(value).__name__}")


def _decode(node, table: _Vars, refs: dict[str, object], state, depth=0):
    if depth > MAX_DEPTH:
        raise _Unsupported("cached value is too deep")
    state[0] += 1
    if state[0] > MAX_NODES:
        raise _Unsupported("cached value is too large")
    if not isinstance(node, dict):
        raise _Unsupported("cached value is not an object")
    kind = node.get("k")
    if kind == "var":
        key = node.get("i")
        if not isinstance(key, str):
            raise _Unsupported("invalid cached variable")
        existing = table.objects.get(key)
        if existing is not None:
            return existing
        name = node.get("n")
        sort = node.get("s")
        if not isinstance(name, str) or not isinstance(sort, str):
            raise _Unsupported("invalid cached variable")
        var = table._fresh(name, sort)
        table.objects[key] = var
        return var
    if kind == "refp":
        path = node.get("p")
        if not isinstance(path, list):
            raise _Unsupported("invalid cached reference")
        lookup = _canonical(path)
        if lookup not in refs:
            raise _Unsupported("unresolved cached reference")
        ref_kind = node.get("c")
        if ref_kind == "TheoremRef":
            return TheoremRef(refs[lookup])
        if ref_kind == "AxiomRef":
            return AxiomRef(refs[lookup])
        raise _Unsupported("invalid cached reference kind")
    if kind == "proof":
        name = node.get("c")
        if name not in _PROOF_TYPES or name in _UNSUPPORTED_PROOF_TYPES:
            raise _Unsupported(f"unsupported cached proof term {name!r}")
        values = node.get("f")
        if not isinstance(values, dict):
            raise _Unsupported("invalid cached proof term")
        cls = _PROOF_TYPES[name]
        args = {
            field.name: _decode(values[field.name], table, refs, state, depth + 1)
            for field in fields(cls)
        }
        return cls(**args)
    if kind == "expr":
        name = node.get("c")
        if name not in _EXPR_TYPES or name in {"App", "CaseExpr"}:
            raise _Unsupported(f"unsupported cached expression {name!r}")
        values = node.get("f")
        if not isinstance(values, dict):
            raise _Unsupported("invalid cached expression")
        cls = _EXPR_TYPES[name]
        args = {
            field.name: _decode(values[field.name], table, refs, state, depth + 1)
            for field in fields(cls)
        }
        return cls(**args)
    if kind == "lit":
        if "i" in node:
            return Lit(_int_value(node["i"]))
        if "b" in node and type(node["b"]) is bool:
            return Lit(node["b"])
        if "s" in node and type(node["s"]) is str:
            return Lit(node["s"])
        if "v" in node and node["v"] is None:
            return Lit(None)
        raise _Unsupported("invalid cached literal")
    if kind == "none":
        return None
    if kind == "bool" and type(node.get("v")) is bool:
        return node["v"]
    if kind == "int":
        return _int_value(node.get("v"))
    if kind == "str" and type(node.get("v")) is str:
        return node["v"]
    if kind == "tuple":
        items = node.get("v")
        if not isinstance(items, list):
            raise _Unsupported("invalid cached tuple")
        return tuple(_decode(item, table, refs, state, depth + 1) for item in items)
    raise _Unsupported(f"unsupported cached value kind {kind!r}")


# ── Fingerprints ─────────────────────────────────────────────────────────────


def _canonical(value) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _digest(value) -> str:
    return sha256(_canonical(value).encode()).hexdigest()


def _statement_fingerprint(statement: Expr) -> tuple[str, _Vars]:
    table = _statement_vars(statement)
    encoded = _encode(statement, table, [0])
    return _digest(encoded), table


def _declarations_fingerprint(declarations) -> list[list[str]]:
    result = []
    for var in declarations:
        if not isinstance(var, Var) or not isinstance(var.name, str):
            raise _Ineligible("declarations must be named Var objects")
        try:
            result.append([var.name, _sort(var.type)])
        except _Unsupported as error:
            raise _Ineligible(str(error)) from error
    return result


def _code_fingerprint(code: CodeType) -> dict:
    constants = []
    for item in code.co_consts:
        if isinstance(item, CodeType):
            raise _Ineligible("proof implementation contains a nested code object")
        if isinstance(item, (str, bytes, int, float, complex, bool, type(None))):
            constants.append([type(item).__name__, repr(item)])
        elif isinstance(item, tuple):
            constants.append(["tuple", repr(item)])
        elif isinstance(item, frozenset):
            constants.append(["frozenset", repr(item)])
        else:
            constants.append([type(item).__name__, repr(item)])
    return {
        "code": code.co_code.hex(),
        "consts": constants,
        "names": list(code.co_names),
        "varnames": list(code.co_varnames),
        "freevars": list(code.co_freevars),
        "cellvars": list(code.co_cellvars),
        "argcount": code.co_argcount,
        "kwonly": code.co_kwonlyargcount,
        "nlocals": code.co_nlocals,
        "stacksize": code.co_stacksize,
        "flags": code.co_flags,
    }


def _check_bytecode(code: CodeType, *, depth: int = 0) -> None:
    if depth > 4:
        raise _Ineligible("proof implementation nests too many code objects")
    for instruction in dis.get_instructions(code):
        if instruction.opname in _UNSAFE_OPNAMES:
            raise _Ineligible(f"proof implementation uses {instruction.opname}")
    for item in code.co_consts:
        if isinstance(item, CodeType):
            _check_bytecode(item, depth=depth + 1)


def _value_fingerprint(value, seen: set[int], depth: int = 0):
    if depth > 6:
        raise _Ineligible("global reference is too deep")
    if value is None or type(value) in (bool, int, str, bytes):
        if type(value) is int and abs(value).bit_length() > 1_000_000:
            raise _Ineligible("global integer is too large to fingerprint")
        return {"kind": "value", "type": type(value).__name__, "value": repr(value)}
    if isinstance(value, FunctionType):
        module = getattr(value, "__module__", "") or ""
        if module == "logos" or module.startswith("logos."):
            owner = sys.modules.get(module)
            name = value.__qualname__.rsplit(".", 1)[-1]
            if owner is None or getattr(owner, name, None) is not value:
                raise _Ineligible("proof implementation reads a replaced Logos function")
            return {
                "kind": "logos-function",
                "module": module,
                "qualname": value.__qualname__,
            }
        return _function_fingerprint(value, seen, depth + 1)
    if isinstance(value, tuple):
        if id(value) in seen:
            raise _Ineligible("cyclic global tuple")
        seen.add(id(value))
        try:
            items = [_value_fingerprint(item, seen, depth + 1) for item in value]
        finally:
            seen.discard(id(value))
        return {"kind": "tuple", "items": items}
    if isinstance(value, ModuleType):
        raise _Ineligible("proof implementation reads a module global")
    if isinstance(value, type):
        # The built-in sorts are immutable values, not constructors that can
        # observe external state.
        if value is int or value is bool:
            return {"kind": "sort", "name": value.__name__}
        # Logos expression classes are pure dataclass constructors.
        if value in _EXPR_TYPES.values():
            return {
                "kind": "logos-class",
                "module": value.__module__,
                "qualname": value.__qualname__,
            }
        raise _Ineligible("proof implementation reads a class global")
    from logos.sequence import SeqType
    if isinstance(value, SeqType):
        return {"kind": "sort", "name": "seq"}
    module = type(value).__module__
    if module == "logos.theorem" and type(value).__name__ == "Theorem":
        statement, _ = _statement_fingerprint(value.statement)
        return {
            "kind": "theorem",
            "name": value.name,
            "statement": statement,
            "declarations": _declarations_fingerprint(value.declarations),
        }
    if module == "logos.theorem" and type(value).__name__ == "Axiom":
        statement, _ = _statement_fingerprint(value.statement)
        return {"kind": "axiom", "name": value.name, "statement": statement}
    raise _Ineligible(f"proof implementation reads an unsupported global {type(value).__name__}")


def _function_fingerprint(fn: FunctionType, seen: set[int], depth: int = 0) -> dict:
    if depth > 6:
        raise _Ineligible("proof helper nesting is too deep")
    if fn.__closure__:
        raise _Ineligible("proof implementation has a closure")
    if fn.__defaults__ or fn.__kwdefaults__:
        raise _Ineligible("proof implementation has default arguments")
    code = fn.__code__
    if code.co_flags & (inspect.CO_GENERATOR | inspect.CO_COROUTINE | inspect.CO_ASYNC_GENERATOR):
        raise _Ineligible("proof implementation is a generator or coroutine")
    _check_bytecode(code)
    if id(fn) in seen:
        return {
            "kind": "function-ref",
            "module": fn.__module__,
            "qualname": fn.__qualname__,
            "code": _digest(_code_fingerprint(code)),
        }
    seen.add(id(fn))
    try:
        source_file = inspect.getsourcefile(fn)
        if not source_file or not os.path.isfile(source_file):
            raise _Ineligible("proof implementation has no readable source")
        try:
            source = inspect.getsource(fn)
        except (OSError, TypeError) as error:
            raise _Ineligible(f"proof implementation source is unreadable: {error}") from error
        globals_fingerprint = {}
        for name in code.co_names:
            if name in fn.__globals__:
                globals_fingerprint[name] = _value_fingerprint(
                    fn.__globals__[name], seen, depth + 1
                )
            elif hasattr(builtins, name):
                if name in _UNSAFE_BUILTINS:
                    raise _Ineligible(f"proof implementation uses builtin {name}")
                globals_fingerprint[name] = {"kind": "builtin", "name": name}
            # Attribute names in co_names are not globals; the object they are
            # read from is fingerprinted separately or is the proof context.
        return {
            "kind": "function",
            "module": fn.__module__,
            "qualname": fn.__qualname__,
            "source": sha256(source.encode()).hexdigest(),
            "code": _code_fingerprint(code),
            "globals": globals_fingerprint,
        }
    finally:
        seen.discard(id(fn))


def _authored_source(theorem) -> FunctionType:
    from logos.theorem import _Proof

    # Contract and program theorems bind their evidence to live source and
    # revalidate on every run.  They keep that path instead of the cache.
    if type(theorem)._revalidate is not _Proof._revalidate:
        raise _Ineligible("theorem revalidates source-bound evidence")
    if type(theorem)._run_proof is not _Proof._run_proof:
        raise _Ineligible("theorem overrides proof execution")
    if type(theorem)._dependency_evidence is not _Proof._dependency_evidence:
        raise _Ineligible("theorem overrides dependency compilation")
    spec = getattr(theorem, "_proof_spec", None)
    if not isinstance(spec, list) or len(spec) != 1:
        raise _Ineligible("proof spec is not a single authored proof function")
    tactic = spec[0]
    fn = getattr(tactic, "__logos_authoring_source__", None)
    if fn is None:
        raise _Ineligible("proof spec is not a book-style authored proof")
    if getattr(tactic, "__logos_authoring_theorem__", None) is not theorem:
        raise _Ineligible("authored proof wrapper belongs to another theorem")
    if not isinstance(fn, FunctionType):
        raise _Ineligible("authored proof source is not a plain function")
    if "<locals>" in fn.__qualname__ or "." in fn.__qualname__:
        raise _Ineligible("authored proof is not a module-level function")
    if fn.__closure__:
        raise _Ineligible("authored proof has a closure")
    return fn


# ── Dependency bindings ──────────────────────────────────────────────────────


def _find_path(globals_map: dict, target) -> list | None:
    def walk(value, path, depth, seen):
        if value is target:
            return path
        if depth >= 4 or id(value) in seen:
            return None
        if isinstance(value, tuple):
            seen.add(id(value))
            for index, item in enumerate(value):
                found = walk(item, path + [index], depth + 1, seen)
                if found is not None:
                    return found
        return None

    for name in sorted(globals_map):
        if name == "__builtins__":
            continue
        found = walk(globals_map[name], [name], 0, set())
        if found is not None:
            return found
    return None


def _resolve_path(globals_map: dict, path: list):
    value = globals_map
    for step in path:
        if isinstance(step, str):
            if not isinstance(value, dict) or step not in value:
                raise _Ineligible("cached dependency path no longer resolves")
            value = value[step]
        elif isinstance(step, int):
            if not isinstance(value, (tuple, list)) or step < 0 or step >= len(value):
                raise _Ineligible("cached dependency path no longer resolves")
            value = value[step]
        else:
            raise _Ineligible("cached dependency path is malformed")
    return value


def _dependency_descriptor(value, globals_map: dict) -> dict:
    from logos.theorem import Axiom as AuthorAxiom, Theorem

    if isinstance(value, Theorem):
        statement, _ = _statement_fingerprint(value.statement)
        path = _find_path(globals_map, value)
        if path is None:
            raise _Ineligible("theorem reference is not bound to a module global")
        return {
            "kind": "theorem",
            "name": value.name,
            "path": path,
            "statement": statement,
            "declarations": _declarations_fingerprint(value.declarations),
        }
    if isinstance(value, AuthorAxiom):
        statement, _ = _statement_fingerprint(value.statement)
        path = _find_path(globals_map, value)
        if path is None:
            from logos import builtins as logos_builtins
            if getattr(logos_builtins, value.name, None) is value:
                path = ["logos.builtins", value.name]
            else:
                raise _Ineligible("axiom reference is not bound to a module global")
        return {
            "kind": "axiom",
            "name": value.name,
            "path": path,
            "statement": statement,
        }
    raise _Ineligible(f"unsupported cached reference {type(value).__name__}")


def _validate_descriptor(descriptor: dict, globals_map: dict):
    from logos import builtins as logos_builtins
    from logos.theorem import Axiom as AuthorAxiom, Theorem

    path = descriptor.get("path")
    if not isinstance(path, list) or len(path) > 8:
        raise _Ineligible("cached dependency path is malformed")
    if any(not isinstance(step, (str, int)) or isinstance(step, bool) for step in path):
        raise _Ineligible("cached dependency path is malformed")
    if len(path) == 2 and path[0] == "logos.builtins":
        value = getattr(logos_builtins, path[1], None)
    else:
        value = _resolve_path(globals_map, path)
    kind = descriptor.get("kind")
    if kind == "theorem":
        if not isinstance(value, Theorem):
            raise _Ineligible("cached theorem dependency now resolves to another kind")
        if value.name != descriptor.get("name"):
            raise _Ineligible("cached theorem dependency name changed")
        statement, _ = _statement_fingerprint(value.statement)
        if statement != descriptor.get("statement"):
            raise _Ineligible("cached theorem dependency statement changed")
        if _declarations_fingerprint(value.declarations) != descriptor.get("declarations"):
            raise _Ineligible("cached theorem dependency declarations changed")
        return value
    if kind == "axiom":
        if not isinstance(value, AuthorAxiom):
            raise _Ineligible("cached axiom dependency now resolves to another kind")
        if value.name != descriptor.get("name"):
            raise _Ineligible("cached axiom dependency name changed")
        statement, _ = _statement_fingerprint(value.statement)
        if statement != descriptor.get("statement"):
            raise _Ineligible("cached axiom dependency statement changed")
        return value
    raise _Ineligible("cached dependency has an unknown kind")


def _collect_references(evidence, refs: dict[int, object], state, depth=0) -> None:
    if depth > MAX_DEPTH:
        raise _Unsupported("cached evidence is too deep")
    state[0] += 1
    if state[0] > MAX_NODES:
        raise _Unsupported("cached evidence is too large")
    if isinstance(evidence, (TheoremRef, AxiomRef)):
        obj = evidence.theorem if isinstance(evidence, TheoremRef) else evidence.axiom
        refs[id(obj)] = obj
        return
    if not is_dataclass(evidence):
        return
    for field in fields(evidence):
        value = getattr(evidence, field.name)
        if isinstance(value, ProofTerm):
            _collect_references(value, refs, state, depth + 1)
        elif isinstance(value, (list, tuple)):
            for item in value:
                if isinstance(item, ProofTerm):
                    _collect_references(item, refs, state, depth + 1)


# ── Plans ────────────────────────────────────────────────────────────────────


class _Plan:
    """A cache key and the codec that binds one theorem's evidence."""

    def __init__(self, theorem, key, record, globals_map: dict):
        self.theorem = theorem
        self.key = key
        self.record = record
        self.globals_map = globals_map

    def _table(self) -> _Vars:
        # Statement variables come first so their s/b ids match the statement
        # fingerprint.  Declarations that are not free in the statement keep
        # their identity too, so evidence may mention them.
        table = _statement_vars(self.theorem.statement)
        index = 0
        for var in self.theorem.declarations:
            if id(var) not in table.ids:
                table._bind(f"d{index}", var)
                index += 1
        return table

    def _encode_record(self, evidence) -> dict:
        refs: dict[int, object] = {}
        _collect_references(evidence, refs, [0])
        descriptors = []
        ref_paths: dict[int, list] = {}
        for identity in sorted(refs):
            descriptor = _dependency_descriptor(refs[identity], self.globals_map)
            descriptors.append(descriptor)
            ref_paths[identity] = descriptor["path"]

        table = self._table()
        encoded = _encode(evidence, table, [0], ref_paths=ref_paths)
        record = dict(self.record)
        record["dependencies"] = descriptors
        record["evidence"] = encoded
        return record

    def _revive(self, record) -> ProofTerm:
        dependencies = record.get("dependencies")
        if not isinstance(dependencies, list):
            raise _Ineligible("cached record has no dependency table")
        refs: dict[str, object] = {}
        for descriptor in dependencies:
            if not isinstance(descriptor, dict):
                raise _Ineligible("cached dependency is malformed")
            path = descriptor.get("path")
            if not isinstance(path, list):
                raise _Ineligible("cached dependency path is malformed")
            refs[_canonical(path)] = _validate_descriptor(descriptor, self.globals_map)
        table = self._table()
        evidence = _decode(record.get("evidence"), table, refs, [0])
        if not isinstance(evidence, ProofTerm):
            raise _Ineligible("cached evidence is not a proof term")
        return evidence


def _plan(theorem) -> _Plan | None:
    """Return a cache plan for an eligible theorem, or None to execute."""
    if not _enabled():
        return None
    # Plans are memoized only inside one check() so that a later call outside
    # a check always sees a changed global or dependency.  The receipt
    # freshness pass still runs before _commit, where the memo is valid.
    memo = getattr(_STATE, "plans", None)
    if memo is not None and getattr(_STATE, "pending", None) is not None:
        try:
            return memo[theorem]
        except KeyError:
            pass
    result = None
    try:
        identity = _compiler_identity()
        if identity is not None:
            fn = _authored_source(theorem)
            statement, _ = _statement_fingerprint(theorem.statement)
            declarations = _declarations_fingerprint(theorem.declarations)
            implementation = _function_fingerprint(fn, set())
            key_material = {
                "format": RECORD_FORMAT,
                "compiler": identity,
                "proof_format": FORMAT,
                "theory": THEORY,
                "name": theorem.name,
                "module": fn.__module__,
                "qualname": fn.__qualname__,
                "statement": statement,
                "declarations": declarations,
                "implementation": implementation,
            }
            key = _digest(key_material)
            record = dict(key_material)
            record["key"] = key
            result = _Plan(theorem, key, record, fn.__globals__)
    except Exception:
        # Cache eligibility must never turn a working proof into a failure.
        # Any unexpected shape falls back to the ordinary execution path.
        pass
    if memo is not None and getattr(_STATE, "pending", None) is not None:
        try:
            memo[theorem] = result
        except TypeError:
            pass
    return result


# ── Disk ─────────────────────────────────────────────────────────────────────


def _record_path(key: str) -> Path:
    return _directory() / key[:2] / f"{key}{RECORD_SUFFIX}"


def _load(cache_plan: _Plan) -> ProofTerm | None:
    """Read and revive evidence for this plan, or None to execute."""
    try:
        path = _record_path(cache_plan.key)
        size = path.stat().st_size
        if size <= 0 or size > MAX_RECORD_BYTES:
            return None
        data = path.read_bytes()
    except OSError:
        return None
    try:
        record = json.loads(data)
    except (ValueError, UnicodeError, RecursionError):
        return None
    if not isinstance(record, dict):
        return None
    if (
        record.get("format") != RECORD_FORMAT
        or record.get("key") != cache_plan.key
        or record.get("compiler") != cache_plan.record["compiler"]
        or record.get("proof_format") != FORMAT
        or record.get("theory") != THEORY
        or record.get("statement") != cache_plan.record["statement"]
        or record.get("declarations") != cache_plan.record["declarations"]
        or record.get("implementation") != cache_plan.record["implementation"]
    ):
        return None
    try:
        return cache_plan._revive(record)
    except Exception:
        # A corrupt or incompatible record is a cache miss, never a failed
        # proof.  The proof will execute and a fresh record may replace it.
        return None


def _store(cache_plan: _Plan, evidence: ProofTerm) -> None:
    """Persist one compiled evidence record atomically.  Errors are ignored."""
    try:
        record = cache_plan._encode_record(evidence)
        data = _canonical(record).encode()
        if len(data) > MAX_RECORD_BYTES:
            return
        path = _record_path(cache_plan.key)
        path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        fd, temporary = tempfile.mkstemp(
            prefix=f".{cache_plan.key}.", suffix=".tmp", dir=path.parent
        )
        try:
            with os.fdopen(fd, "wb") as handle:
                handle.write(data)
                handle.flush()
            # The rename is atomic for concurrent readers.  This is a cache:
            # a record lost to a power cut is recompiled, so fsync would only
            # add latency to every cold lemma.
            os.replace(temporary, path)
        except BaseException:
            try:
                os.unlink(temporary)
            except OSError:
                pass
            raise
    except Exception:
        return


# ── Staging ──────────────────────────────────────────────────────────────────


def _begin() -> None:
    """Start collecting records that may be written after Rust accepts."""
    _STATE.pending = [] if _enabled() else None
    _STATE.plans = weakref.WeakKeyDictionary() if _enabled() else None


def _stage(cache_plan: _Plan, evidence: ProofTerm) -> None:
    pending = getattr(_STATE, "pending", None)
    if pending is not None:
        pending.append((cache_plan, evidence))


def _commit() -> None:
    pending = getattr(_STATE, "pending", None)
    _STATE.pending = None
    _STATE.plans = None
    if pending:
        for cache_plan, evidence in pending:
            _store(cache_plan, evidence)


def _abort() -> None:
    _STATE.pending = None
    _STATE.plans = None


def _forget_plans() -> None:
    """Discard memoized keys after a proof whose effects are not tracked."""
    _STATE.plans = None
