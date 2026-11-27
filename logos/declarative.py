"""Declarative checked functions: ``@logos.function`` and named clauses.

A declared function is an ordinary Python function. The decorator reads its
source, refuses syntax Logos cannot represent at the offending line, and
returns the original object unchanged: there is no wrapper and no runtime
contract enforcement. ``@f.requires``, ``@f.ensures``, ``@f.invariant`` and
``@f.decreases`` attach named symbolic clauses by binding their parameters to
the function's inputs, the result, and the loop-head locals.

``f.check()`` proves the program, checks every callee it calls, and asks the
Rust verifier to replay the whole dependency DAG. A caller may use a callee's
postcondition only after that callee program has been independently verified.
"""
from __future__ import annotations

import ast
import inspect
from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
from types import CodeType, FunctionType

from logos.contracts import (
    LogosContractError, _and_all, _compile, _module_code, _module_path, _normalize,
    _parse, _read_source, _same_code, _sort, _trivial, _variables,
    translate_declarative,
)
from logos.define import Function
from logos.expr import App, Expr, ForallNode, Lit, Var
from logos.helpers import structural_eq
from logos.kernel import ProgramRef
from logos.portable import (
    LogosProofError, ProofReceipt, artifact_bytes, inspect_artifact,
    statement_declarations, verify_artifact,
)
from logos.programs import Call, If, NamedClause, Program, While, call_statements
from logos.proofs import ProofSearchError, build_program_obligations


KINDS = ("requires", "ensures", "invariant", "decreases")


@dataclass(frozen=True)
class Clause:
    """One named clause bound to a declarative function."""

    kind: str
    name: str
    function: FunctionType
    path: Path
    source: bytes
    code: CodeType
    line: int
    expression: Expr
    source_digest: str
    binding: tuple[str, ...]


def _clause_source(clause_fn, kind):
    if not isinstance(clause_fn, FunctionType):
        raise LogosContractError(
            f"@logos.function: @{kind} expects an ordinary Python function, got "
            f"{type(clause_fn).__name__}"
        )
    if clause_fn.__qualname__ != clause_fn.__name__ or clause_fn.__name__.startswith("<"):
        raise LogosContractError(
            f"@{kind}: expected a module-level clause function, got "
            f"{clause_fn.__qualname__!r}; clauses cannot be lambdas or nested functions"
        )
    path = _module_path(clause_fn)
    source = _read_source(path, clause_fn)
    compiled = _compile(source, path, clause_fn)
    tree = _parse(source, path, clause_fn)
    definitions = [
        node for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        and node.name == clause_fn.__name__
    ]
    if len(definitions) != 1:
        raise LogosContractError(
            f"@{kind}: {path} must define clause {clause_fn.__name__!r} exactly once at "
            f"module level, found {len(definitions)}"
        )
    definition = definitions[0]
    if isinstance(definition, ast.AsyncFunctionDef):
        raise LogosContractError(
            f"{path}:{definition.lineno}: clause {clause_fn.__name__!r} is async; "
            "clauses must be ordinary Python functions"
        )
    expected = _module_code(compiled, clause_fn.__name__)
    if expected is None or not _same_code(expected, clause_fn.__code__):
        raise LogosContractError(
            f"source of clause {clause_fn.__name__!r} in {path} does not match the "
            "imported code object; reimport the module before declaring the clause"
        )
    segment = ast.get_source_segment(source.decode("utf-8"), definition) or ""
    return path, source, clause_fn.__code__, definition, sha256(segment.encode()).hexdigest()


def _clause_parameters(clause_fn, kind, allowed, path, line):
    signature = inspect.signature(clause_fn)
    order = []
    names = []
    for parameter in signature.parameters.values():
        if parameter.default is not parameter.empty:
            raise LogosContractError(
                f"{path}:{line}: clause {clause_fn.__name__!r} must not declare default "
                "values; every input is supplied symbolically"
            )
        if parameter.kind in (
            inspect.Parameter.VAR_POSITIONAL, inspect.Parameter.VAR_KEYWORD,
        ):
            raise LogosContractError(
                f"{path}:{line}: clause {clause_fn.__name__!r} must not take *args or "
                "**kwargs; name the symbolic inputs it uses"
            )
        if parameter.name not in allowed:
            expected = ", ".join(sorted(allowed)) or "none"
            raise LogosContractError(
                f"{path}:{line}: clause {clause_fn.__name__!r} names {parameter.name!r}, "
                f"which is not available to a {kind} clause of this function; "
                f"available names: {expected}"
            )
        order.append(parameter)
        names.append(parameter.name)
    return order, names


class FunctionDeclaration:
    """The source-bound declaration behind one ``@logos.function``."""

    def __init__(self, fn):
        self.fn = fn
        self.name = fn.__name__
        self.module = inspect.getmodule(fn)
        self.identity = f"fn:{fn.__module__}.{fn.__qualname__}"
        self.function = Function(self.name, [], None, result_type=int, portable_id=self.identity)
        self.translation = translate_declarative(fn, self.function)
        self.params = tuple(self.translation.variables[name] for name in self.translation.names)
        self.function.params = list(self.params)
        self.result_var = self.translation.program.result.var
        self.clauses_by_kind = {kind: [] for kind in KINDS}
        self._receipt = None
        self._checked_artifact = None
        self._fingerprint = None
        self.program = None
        self.statement = None
        self.rebuild()

    # ── clause registration ────────────────────────────────────────────────

    def _allowed(self, kind):
        names = {var.name for var in self.params}
        if kind == "requires":
            return names
        if kind == "ensures":
            return names | {"result"}
        return names | set(self.translation.entry_locals)

    def add_clause(self, kind, clause_fn):
        if kind not in KINDS:
            raise LogosContractError(f"@logos.function: unknown clause kind {kind!r}")
        path, source, code, definition, digest = _clause_source(clause_fn, kind)
        line = definition.lineno
        if kind in ("invariant", "decreases") and not self.translation.program.ghosts:
            raise LogosContractError(
                f"{path}:{line}: clause {clause_fn.__name__!r} is a {kind} clause, but "
                f"{self.name!r} declares no while loop"
            )
        if kind == "decreases" and self.clauses_by_kind["decreases"]:
            previous = self.clauses_by_kind["decreases"][0]
            raise LogosContractError(
                f"{path}:{line}: {self.name!r} already has a decreases clause "
                f"{previous.name!r}; a loop has one variant"
            )
        allowed = self._allowed(kind)
        parameters, names = _clause_parameters(clause_fn, kind, allowed, path, line)
        if any(previous.name == clause_fn.__name__ for previous in self.clauses_by_kind[kind]):
            raise LogosContractError(
                f"{path}:{line}: {self.name!r} already has a {kind} clause named "
                f"{clause_fn.__name__!r}"
            )
        binding = {}
        for parameter in parameters:
            if parameter.name == "result":
                binding[parameter.name] = self.result_var
            else:
                binding[parameter.name] = self.translation.variables[parameter.name]
        args, kwargs = [], {}
        for parameter in parameters:
            value = binding[parameter.name]
            if parameter.kind is inspect.Parameter.KEYWORD_ONLY:
                kwargs[parameter.name] = value
            else:
                args.append(value)
        try:
            expression = clause_fn(*args, **kwargs)
        except Exception as error:
            raise LogosContractError(
                f"{path}:{line}: clause {clause_fn.__name__!r} of {self.name!r} could not "
                f"be evaluated symbolically: {type(error).__name__}: {error}"
            ) from error
        if not isinstance(expression, Expr):
            raise LogosContractError(
                f"{path}:{line}: clause {clause_fn.__name__!r} of {self.name!r} must return "
                f"a Logos expression, got {type(expression).__name__}"
            )
        expression = _normalize(expression)
        sort = _sort(expression)
        expected = int if kind == "decreases" else bool
        if sort is not expected:
            expectation = "an integer term" if kind == "decreases" else "a proposition"
            raise LogosContractError(
                f"{path}:{line}: clause {clause_fn.__name__!r} of {self.name!r} must be "
                f"{expectation}"
            )
        allowed_ids = {id(value) for value in binding.values()}
        for variable in _variables(expression):
            if id(variable) not in allowed_ids:
                raise LogosContractError(
                    f"{path}:{line}: clause {clause_fn.__name__!r} of {self.name!r} mentions "
                    f"{variable.name!r}, which is not a declared symbolic parameter; bind it "
                    "by name in the clause signature instead of constructing it"
                )
        clause = Clause(
            kind=kind,
            name=clause_fn.__name__,
            function=clause_fn,
            path=path,
            source=source,
            code=code,
            line=line,
            expression=expression,
            source_digest=digest,
            binding=tuple(names),
        )
        self.clauses_by_kind[kind].append(clause)
        self.clauses_by_kind[kind].sort(key=lambda item: item.line)
        self.invalidate()
        self.rebuild()
        return clause_fn

    def clause_decorator(self, kind):
        def decorate(clause_fn):
            return self.add_clause(kind, clause_fn)

        decorate.__name__ = kind
        decorate.__doc__ = f"Declare a named {kind} clause for {{self.name}}."
        return decorate

    def clauses(self):
        return tuple(
            clause
            for kind in KINDS
            for clause in self.clauses_by_kind[kind]
        )

    # ── program assembly ───────────────────────────────────────────────────

    def rebuild(self):
        source = self.translation.program
        requires = [clause.expression for clause in self.clauses_by_kind["requires"]]
        ensures = [clause.expression for clause in self.clauses_by_kind["ensures"]]
        invariants = [
            NamedClause(clause.name, clause.expression)
            for clause in self.clauses_by_kind["invariant"]
        ]
        decreases = self.clauses_by_kind["decreases"]
        variant = decreases[0].expression if decreases else Lit(0)
        decreases_name = decreases[0].name if decreases else None

        def attach(statements):
            attached = []
            seen = False
            for statement in statements:
                if isinstance(statement, While):
                    seen = True
                    attached.append(
                        While(
                            statement.condition,
                            attach(statement.body),
                            _and_all([item.expr for item in invariants]),
                            variant,
                            tuple(invariants),
                            decreases_name,
                        )
                    )
                elif isinstance(statement, If):
                    attached.append(
                        If(statement.condition, attach(statement.then_body),
                           attach(statement.else_body))
                    )
                else:
                    attached.append(statement)
            return tuple(attached)

        program = Program(
            name=source.name,
            function=source.function,
            params=source.params,
            result=source.result,
            locals=source.locals,
            requires=_and_all(requires),
            ensures=_and_all(ensures),
            body=attach(source.body),
            ghosts=source.ghosts,
            requires_clauses=tuple(
                NamedClause(clause.name, clause.expression)
                for clause in self.clauses_by_kind["requires"]
            ),
            ensures_clauses=tuple(
                NamedClause(clause.name, clause.expression)
                for clause in self.clauses_by_kind["ensures"]
            ),
        )
        self.program = program
        self.statement = program_statement(program)
        self._fingerprint = None
        if hasattr(self.fn, "__logos_function__"):
            self.fn.program = program
            self.fn.statement = self.statement
        return program

    def annotations(self):
        contract = [
            {"kind": clause.kind, "name": clause.name, "line": clause.line}
            for clause in self.clauses()
        ]
        return {
            "claim": inspect.getdoc(self.fn),
            "strategy": None,
            "contract": contract,
        }

    # ── freshness ──────────────────────────────────────────────────────────

    def fingerprint(self):
        if self._fingerprint is None:
            parts = [self.translation.source_digest]
            for clause in self.clauses():
                parts.append(f"{clause.kind}:{clause.name}:{clause.source_digest}")
                parts.append(repr(clause.expression))
            for call in self.translation.calls:
                parts.append(f"call:{call.callee.name}:{call.callee.fingerprint()}")
            self._fingerprint = sha256("\0".join(parts).encode("utf-8")).hexdigest()
        return self._fingerprint

    def _fresh_digest(self):
        path = _module_path(self.fn)
        source = _read_source(path, self.fn)
        text = source.decode("utf-8")
        compiled = _compile(source, path, self.fn)
        tree = _parse(source, path, self.fn)
        definitions = [
            node for node in tree.body
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
            and node.name == self.name
        ]
        if len(definitions) != 1:
            raise LogosContractError(
                f"{path} no longer defines {self.name!r} exactly once at module level"
            )
        expected = _module_code(compiled, self.name)
        if expected is None or not _same_code(expected, self.translation.code):
            raise LogosContractError(
                f"source of {self.name!r} in {path} no longer matches the imported code "
                "object; reimport the module and redeclare it"
            )
        segment = ast.get_source_segment(text, definitions[0]) or ""
        digest = sha256(segment.encode("utf-8")).hexdigest()
        if digest != self.translation.source_digest:
            raise LogosContractError(
                f"source of {self.name!r} in {path} changed after @logos.function was "
                "applied; reimport the module and redeclare it"
            )

    def _fresh_clause(self, clause):
        path = _module_path(clause.function)
        source = _read_source(path, clause.function)
        compiled = _compile(source, path, clause.function)
        expected = _module_code(compiled, clause.function.__name__)
        if expected is None or not _same_code(expected, clause.code):
            raise LogosContractError(
                f"source of clause {clause.name!r} of {self.name!r} changed after it was "
                "declared; reimport the module and redeclare the clause"
            )
        tree = _parse(source, path, clause.function)
        definitions = [
            node for node in tree.body
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
            and node.name == clause.name
        ]
        if len(definitions) != 1:
            raise LogosContractError(
                f"{path} no longer defines clause {clause.name!r} exactly once"
            )
        segment = ast.get_source_segment(source.decode("utf-8"), definitions[0]) or ""
        if sha256(segment.encode()).hexdigest() != clause.source_digest:
            raise LogosContractError(
                f"source of clause {clause.name!r} of {self.name!r} changed after it was "
                "declared; reimport the module and redeclare the clause"
            )

    def _invalidate(self):
        self._receipt = None
        self._checked_artifact = None
        if hasattr(self.fn, "certified"):
            self.fn.certified = False

    def invalidate(self):
        self._invalidate()

    def revalidate(self, seen=None):
        """Re-read every source binding, then every transitive callee.

        Raises before any proof or export can use a stale binding.
        """
        seen = set() if seen is None else seen
        if id(self) in seen:
            raise LogosContractError(
                f"cyclic call dependency through {self.name!r}; recursive functions are "
                "not supported"
            )
        seen.add(id(self))
        try:
            self._fresh_digest()
            for clause in self.clauses():
                self._fresh_clause(clause)
                binding = {}
                for name in clause.binding:
                    binding[name] = (
                        self.result_var if name == "result"
                        else self.translation.variables[name]
                    )
                signature = inspect.signature(clause.function)
                args, kwargs = [], {}
                for parameter in signature.parameters.values():
                    value = binding[parameter.name]
                    if parameter.kind is inspect.Parameter.KEYWORD_ONLY:
                        kwargs[parameter.name] = value
                    else:
                        args.append(value)
                fresh = _normalize(clause.function(*args, **kwargs))
                if not structural_eq(fresh, clause.expression):
                    raise LogosContractError(
                        f"clause {clause.name!r} of {self.name!r} no longer evaluates to the "
                        "declaration it was registered with; redeclare the clause"
                    )
            for call in self.translation.calls:
                callee = call.callee
                bound = self.module.__dict__.get(callee.name)
                if bound is not callee.fn:
                    raise LogosContractError(
                        f"callee {callee.name!r} called by {self.name!r} was rebound after "
                        "the caller was declared; redeclare the caller"
                    )
                if call.fingerprint != callee.fingerprint():
                    raise LogosContractError(
                        f"callee {callee.name!r} called by {self.name!r} changed after the "
                        "caller was declared; redeclare the caller"
                    )
                callee.revalidate(seen)
        except LogosContractError:
            self._invalidate()
            raise
        except Exception as error:
            self._invalidate()
            raise LogosContractError(
                f"could not revalidate {self.name!r}: {type(error).__name__}: {error}"
            ) from error

    # ── proofs ─────────────────────────────────────────────────────────────

    def ensure_proved(self, seen=None):
        """Build and prove this program and every callee, callees first."""
        seen = set() if seen is None else seen
        if id(self) in seen:
            raise LogosContractError(
                f"cyclic call dependency through {self.name!r}; recursive functions are "
                "not supported"
            )
        seen.add(id(self))
        for call in self.translation.calls:
            call.callee.ensure_proved(seen)
        program = self.rebuild()
        if not program.obligations:
            try:
                program.obligations = build_program_obligations(program)
            except ProofSearchError as error:
                raise LogosContractError(
                    f"contract of {self.name!r} does not hold: {error}"
                ) from error
        return program

    def artifact(self):
        if self._receipt is None:
            raise LogosProofError(
                f"Function '{self.name}' has no current Rust verification; call .check() first"
            )
        return self._receipt.artifact

    @property
    def receipt(self):
        receipt = self._receipt
        if receipt is None:
            return None
        try:
            self.revalidate()
            program = self.program
            evidence = ProgramRef(program, self.statement)
            current = artifact_bytes(
                self.name, self.statement, statement_declarations(self.statement),
                evidence, refresh_lemmas=True, annotations=self.annotations(),
            )
        except (LogosProofError, LogosContractError, TypeError, RecursionError):
            self._invalidate()
            return None
        if current != receipt.artifact:
            self._invalidate()
            return None
        return receipt

    @property
    def certified(self):
        return self.receipt is not None

    def check(self):
        self._invalidate()
        self.revalidate()
        program = self.ensure_proved()
        self.statement = program_statement(program)
        evidence = ProgramRef(program, self.statement)
        artifact = artifact_bytes(
            self.name, self.statement, statement_declarations(self.statement),
            evidence, refresh_lemmas=True, annotations=self.annotations(),
        )
        receipt = verify_artifact(artifact)
        self._receipt = receipt
        self._checked_artifact = artifact
        self.fn.certified = True
        self.fn.program = program
        self.fn.statement = self.statement
        return self.fn

    def inspect(self):
        receipt = self.receipt
        if receipt is None:
            if self._receipt is not None:
                raise LogosProofError(
                    f"Function '{self.name}' changed; call .check() again"
                )
            raise LogosProofError(
                f"Function '{self.name}' has no current Rust verification; call .check() "
                "first"
            )
        markdown = inspect_artifact(receipt.artifact)
        if self.receipt is None:
            raise LogosProofError(
                f"Function '{self.name}' changed during inspection; call .check() again"
            )
        return markdown

    def export(self, path):
        receipt = self.receipt
        if receipt is None:
            raise LogosProofError(
                f"Function '{self.name}' has no current Rust verification; call .check() first"
            )
        Path(path).write_bytes(receipt.artifact)
        return receipt


def _is_trivial(expression):
    from logos.expr import Eq

    return (
        isinstance(expression, Eq)
        and isinstance(expression.left, Lit)
        and isinstance(expression.right, Lit)
        and expression.left.value == 0
        and expression.right.value == 0
    )


def program_statement(program: Program):
    """The portable statement a checked function's program establishes."""
    parameters = [item.var for item in program.params]
    result = program.result.var
    from logos.expr import Eq, Implies

    equality = Eq(result, App(program.function.name, parameters, program.function))
    statement = equality if _is_trivial(program.ensures) else Implies(equality, program.ensures)
    if not _is_trivial(program.requires):
        statement = Implies(program.requires, statement)
    statement = ForallNode(result, statement)
    for parameter in reversed(parameters):
        statement = ForallNode(parameter, statement)
    return statement


def _attach(fn, declaration):
    fn.__logos_function__ = declaration
    fn.check = declaration.check
    fn.inspect = declaration.inspect
    fn.export = declaration.export
    fn.requires = declaration.clause_decorator("requires")
    fn.ensures = declaration.clause_decorator("ensures")
    fn.invariant = declaration.clause_decorator("invariant")
    fn.decreases = declaration.clause_decorator("decreases")
    fn.certified = False
    fn.program = declaration.program
    fn.statement = declaration.statement
    fn.clauses = declaration.clauses


def function(fn):
    """``@logos.function``: bind a Python function to a checkable program.

    The original function object is returned. Defining the function either
    produces a program Logos can represent or raises at the first unsupported
    line, before any clause is declared.
    """
    if not isinstance(fn, FunctionType):
        raise TypeError(
            f"logos.function: expected an ordinary Python function, got {type(fn).__name__}"
        )
    if getattr(fn, "__logos_function__", None) is not None:
        return fn
    declaration = FunctionDeclaration(fn)
    _attach(fn, declaration)
    return fn
