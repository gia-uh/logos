"""Prove a contract about an ordinary Python function from its source.

The defining module's source is the binding. Logos re-reads it, recompiles it
and refuses to continue when the imported code object disagrees with the file.
The supported fragment is deliberately small: either one ``return`` whose value
is a sum of parameters and integer literals, or one ``if``/``else`` over a
single ``<``, ``==`` or ``!=`` comparison, with one such ``return`` per branch.
Every parameter and the result are annotated with the built-in ``int``. A
branching function needs a ``requires=`` that selects one branch, so each path
gets its own theorem. For ``<`` the complement is its negation, so the equal
case belongs to the else path. Anything else fails closed with a source
diagnostic instead of being approximated.
"""
from __future__ import annotations

import ast
import inspect
import sys
from dataclasses import dataclass, field
from hashlib import sha256
from pathlib import Path
from types import CodeType, FunctionType, ModuleType

from logos.define import Function
from logos.programs import (
    Assign, Call, If, NamedClause, Program, ProgramContract, ProgramVariable,
    Return, While, program_contract,
)
from logos.sequence import Seq, SeqType
from logos.expr import (
    Add, And, App, Div, Eq, Expr, ExistsNode, ForallNode, Ge, Gt, Implies,
    Le, Len, Lit, Lt, Mul, Neg, Neq, Not, Nth, Or, Pow, Sorted, Sub, Var,
)
from logos.goal import Goal
from logos.helpers import structural_eq, substitute_symbols
from logos.kernel import (
    Congr, ForallIntro, HypRef, ImpliesIntro, ProgramRef, Symm, Trans,
)
from logos.portable import LogosProofError
from logos.runner import TacticFailed
from logos.tactics._ring import Ring
from logos.theorem import Theorem


class LogosContractError(LogosProofError):
    """A contract, or the source binding behind it, could not be established."""


@dataclass(frozen=True)
class Contract:
    """The two halves of a function contract, written with signature names."""

    ensures: Expr
    requires: Expr | None = None


def contract(*, ensures: Expr, requires: Expr | None = None) -> Contract:
    """Describe a postcondition and an optional explicit precondition."""
    if not isinstance(ensures, Expr):
        raise TypeError(
            f"logos.contract: ensures must be a Logos expression, got {type(ensures).__name__}"
        )
    if requires is not None and not isinstance(requires, Expr):
        raise TypeError(
            f"logos.contract: requires must be a Logos expression or None, "
            f"got {type(requires).__name__}"
        )
    return Contract(ensures, requires)


@dataclass(frozen=True)
class _Fragment:
    """The translated source of one supported function."""

    body: Expr | None = None
    guard: Expr | None = None
    then_body: Expr | None = None
    else_body: Expr | None = None
    program: Program | None = None

    def selected(self, branch: str | None) -> Expr | None:
        if branch == "then":
            return self.then_body
        if branch == "else":
            return self.else_body
        return self.body


def theorem_about(theorem_body, about: FunctionType):
    """Build the contract theorem for an ordinary function."""
    names, variables, fragment = _bind_source(about)
    result_name = _theorem_signature(theorem_body, names, about)
    parameters = [variables[name] for name in names]
    result = Var(result_name, int)
    value = theorem_body(*parameters, **{result_name: result})
    if fragment.program is not None:
        if not isinstance(value, ProgramContract):
            raise LogosContractError(
                f"logos.theorem: the body of {theorem_body.__name__!r} must return "
                "logos.program_contract(...) for a function with a loop"
            )
        return _program_theorem(
            theorem_body, about, variables, names, fragment, result, value
        )
    if isinstance(value, Contract):
        value = Contract(
            _normalize(value.ensures),
            _normalize(value.requires) if value.requires is not None else None,
        )
    _validate(value, variables, result, theorem_body)
    branch = None
    if fragment.guard is not None:
        branch = _select_branch(value.requires, fragment.guard, about.__name__)
    body = fragment.selected(branch)
    # A branch certificate defines only the path its requires selects. The
    # qualified label keeps that transparent definition from being read as the
    # whole source function; the full fragment is still bound by revalidation.
    symbol_name = about.__name__ if branch is None else f"{about.__name__}[{branch}]"
    symbol = Function(symbol_name, list(variables.values()), body, result_type=int)
    equality = Eq(result, App(symbol_name, parameters, symbol))
    statement = Implies(equality, value.ensures)
    if value.requires is not None:
        statement = Implies(value.requires, statement)
    statement = ForallNode(result, statement)
    for variable in reversed(list(variables.values())):
        statement = ForallNode(variable, statement)
    return ContractTheorem(
        statement, name=theorem_body.__name__, about=about, symbol=symbol,
        parameters=parameters, result=result, requires=value.requires,
        ensures=value.ensures, fragment=fragment, branch=branch,
    )


def _program_theorem(theorem_body, about, variables, names, fragment, result, value):
    program = fragment.program
    locals_by_name = {item.name: item.var for item in program.locals}
    known = dict(variables)
    known.update(locals_by_name)
    known[result.name] = result

    def canonical(expr):
        mapping = {}
        for variable in _variables(expr):
            if variable.name not in known:
                raise LogosContractError(
                    f"logos.program_contract: {variable.name!r} is not a parameter or local "
                    f"of {about.__name__!r}"
                )
            mapping[id(variable)] = known[variable.name]
        return substitute_symbols(expr, mapping)

    requires = _normalize(canonical(value.requires))
    ensures = _normalize(canonical(value.ensures))
    invariant = _normalize(canonical(value.invariant))
    variant = _normalize(canonical(value.variant))
    _validate_program_parts(
        about, names, list(locals_by_name), result, requires, ensures, invariant, variant
    )
    program.requires = requires
    program.ensures = ensures
    program.result = ProgramVariable("result", int, result)
    program.body = _attach_loop(program.body, invariant, variant)
    statement = _program_contract_statement(about, program, requires, ensures)
    return ProgramTheorem(
        statement, name=theorem_body.__name__, about=about, program=program,
        fragment=fragment, names=names, variables=variables,
    )


def _attach_loop(statements, invariant, variant):
    attached = []
    seen = False
    for statement in statements:
        if isinstance(statement, While):
            if seen:
                raise LogosContractError("logos.program_contract: only one loop is supported")
            seen = True
            attached.append(While(statement.condition, statement.body, invariant, variant))
        else:
            attached.append(statement)
    if not seen:
        raise LogosContractError("logos.program_contract: the source has no loop to annotate")
    return tuple(attached)


def _program_contract_statement(about, program, requires, ensures):
    parameters = [item.var for item in program.params]
    result = program.result.var
    equality = Eq(result, App(about.__name__, parameters, program.function))
    statement = Implies(equality, ensures)
    statement = Implies(requires, statement)
    statement = ForallNode(result, statement)
    for parameter in reversed(parameters):
        statement = ForallNode(parameter, statement)
    return statement


def _validate_program_parts(about, names, local_names, result, requires, ensures, invariant, variant):
    allowed_inputs = {name for name in names}
    allowed_locals = {name for name in local_names}
    allowed_all = allowed_inputs | allowed_locals

    def vars_of(expr, label):
        found = list(_variables(expr))
        for variable in found:
            if variable.name not in allowed_all and variable is not result:
                raise LogosContractError(
                    f"logos.program_contract: {label} mentions {variable.name!r}, which is "
                    f"not a parameter or local of {about.__name__!r}"
                )
        return found

    for variable in vars_of(requires, "requires"):
        if variable.name not in allowed_inputs:
            raise LogosContractError(
                "logos.program_contract: requires may only mention input parameters"
            )
    for variable in vars_of(ensures, "ensures"):
        if variable.name in allowed_locals:
            raise LogosContractError(
                "logos.program_contract: ensures may only mention parameters and result"
            )
    for variable in vars_of(invariant, "invariant"):
        if variable is result:
            raise LogosContractError(
                "logos.program_contract: invariant must not mention result"
            )
    for variable in vars_of(variant, "variant"):
        if variable is result:
            raise LogosContractError(
                "logos.program_contract: variant must not mention result"
            )
    if _sort(requires) is not bool:
        raise LogosContractError("logos.program_contract: requires must be a proposition")
    if _sort(ensures) is not bool:
        raise LogosContractError("logos.program_contract: ensures must be a proposition")
    if _sort(invariant) is not bool:
        raise LogosContractError("logos.program_contract: invariant must be a proposition")
    if _sort(variant) is not int:
        raise LogosContractError("logos.program_contract: variant must be an integer term")


class ProgramTheorem(Theorem):
    """A contract theorem whose executable body is a checked loop program."""

    def __init__(self, statement, *, name, about, program, fragment, names, variables):
        super().__init__(statement, name=name)
        self.about = about
        self.program = program
        self._fragment = fragment
        self._names = tuple(names)
        self._variables = dict(variables)
        self._proof_spec = [self._program_evidence]

    def _revalidate(self):
        names, variables, fragment = _bind_source(self.about)
        if tuple(names) != self._names:
            self._receipt = None
            raise LogosContractError(
                f"contract for {self.about.__name__!r} no longer matches its source: the "
                "parameter binding changed; redeclare the theorem from the current function"
            )
        fresh = fragment.program
        if fresh is None or not _same_program(fresh, self._fragment.program):
            self._receipt = None
            raise LogosContractError(
                f"contract for {self.about.__name__!r} no longer matches its source: the "
                "translated loop program changed after the theorem was declared; redeclare "
                "the theorem from the current function"
            )

    def _run_proof(self, statement):
        self._revalidate()
        from logos.proofs import build_program_obligations
        self.program.obligations = build_program_obligations(self.program)
        return ProgramRef(self.program, statement)

    def _program_evidence(self, goal):
        return self._run_proof(goal.statement)

    def _dependency_evidence(self, refresh):
        self._revalidate()
        return self._run_proof(self.statement)


def _same_program(left, right):
    if left.name != right.name:
        return False
    if len(left.body) != len(right.body):
        return False
    return all(_same_statement(a, b) for a, b in zip(left.body, right.body))


def _same_statement(left, right):
    if type(left) is not type(right):
        return False
    if isinstance(left, Assign):
        return left.name == right.name and structural_eq(left.value, right.value)
    if isinstance(left, If):
        return (
            structural_eq(left.condition, right.condition)
            and len(left.then_body) == len(right.then_body)
            and len(left.else_body) == len(right.else_body)
            and all(_same_statement(a, b) for a, b in zip(left.then_body, right.then_body))
            and all(_same_statement(a, b) for a, b in zip(left.else_body, right.else_body))
        )
    if isinstance(left, While):
        return (
            structural_eq(left.condition, right.condition)
            and len(left.body) == len(right.body)
            and all(_same_statement(a, b) for a, b in zip(left.body, right.body))
        )
    if isinstance(left, Return):
        return structural_eq(left.value, right.value)
    return False


class ContractTheorem(Theorem):
    """A theorem whose statement comes from a source-bound function contract."""

    def __init__(
        self, statement, *, name, about, symbol, parameters, result, requires, ensures,
        fragment, branch,
    ):
        super().__init__(statement, name=name)
        self.about = about
        self.symbol = symbol
        self.parameters = list(parameters)
        self.result = result
        self.requires = requires
        self.ensures = ensures
        self._fragment = fragment
        self._branch = branch
        self._proof_spec = [self._contract_evidence]

    def _revalidate(self):
        """Re-read the source now, so a stale binding can never certify.

        Decoration is not enough: ``__code__`` can be replaced and the file can
        change while the theorem object lives on. Every proof run, receipt read
        and export calls this, comparing the fresh signature and translation
        with the ones the statement was built from. A branching function binds
        the whole fragment, so changing either branch or the guard invalidates
        both paths, not only the one this theorem proves.
        """
        names, _variables, fragment = _bind_source(self.about)
        bound = [parameter.name for parameter in self.parameters]
        if names != bound:
            self._receipt = None
            raise LogosContractError(
                f"contract for {self.about.__name__!r} no longer matches its source: the "
                f"parameter binding changed from ({', '.join(bound)}) to "
                f"({', '.join(names)}); redeclare the theorem from the current function"
            )
        stored = self._fragment
        if stored.guard is None:
            if not structural_eq(fragment.body, stored.body):
                self._receipt = None
                raise LogosContractError(
                    f"contract for {self.about.__name__!r} no longer matches its source: the "
                    "translated body changed after the theorem was declared; redeclare the "
                    "theorem from the current function"
                )
        else:
            changed = None
            if not structural_eq(fragment.guard, stored.guard):
                changed = "guard"
            elif not structural_eq(fragment.then_body, stored.then_body):
                changed = "then branch"
            elif not structural_eq(fragment.else_body, stored.else_body):
                changed = "else branch"
            if changed is not None:
                self._receipt = None
                raise LogosContractError(
                    f"contract for {self.about.__name__!r} no longer matches its source: the "
                    f"{changed} changed after the theorem was declared; redeclare the "
                    "theorem from the current function"
                )
        if not structural_eq(self.symbol.body, stored.selected(self._branch)):
            self._receipt = None
            raise LogosContractError(
                f"contract for {self.about.__name__!r} no longer matches its source: the "
                "translated body changed after the theorem was declared; redeclare the "
                "theorem from the current function"
            )

    def _run_proof(self, statement):
        self._revalidate()
        return super()._run_proof(statement)

    def _contract_evidence(self, goal: Goal):
        return _derive(self.symbol, self.parameters, self.result, self.requires, self.ensures)

    def _dependency_evidence(self, refresh):
        self._revalidate()
        return super()._dependency_evidence(refresh)


def _bind_source(fn):
    """Return (parameter names, parameter Vars, body Expr) bound to module source."""
    _require_ordinary(fn)
    path = _module_path(fn)
    source = _read_source(path, fn)
    compiled = _compile(source, path, fn)
    tree = _parse(source, path, fn)
    definitions = [
        node for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == fn.__name__
    ]
    if not definitions:
        raise LogosContractError(
            f"logos.theorem(about=...): {path} has no top-level definition of {fn.__name__!r}"
        )
    if len(definitions) > 1:
        raise LogosContractError(
            f"logos.theorem(about=...): {path} defines {fn.__name__!r} "
            f"{len(definitions)} times at module level; keep exactly one definition"
        )
    expected = _module_code(compiled, fn.__name__)
    if expected is None:
        raise LogosContractError(
            f"logos.theorem(about=...): could not recover the compiled code for "
            f"{fn.__name__!r} from {path}"
        )
    if not _same_code(expected, fn.__code__):
        raise LogosContractError(
            f"source of {fn.__name__!r} in {path} does not match the imported code object; "
            "the module is stale or the file changed after import; reimport it before "
            "declaring the theorem"
        )
    return _fragment(definitions[0], fn, path)


def _require_ordinary(fn):
    if not isinstance(fn, FunctionType):
        raise LogosContractError(
            f"logos.theorem(about=...): expected an ordinary Python function, "
            f"got {type(fn).__name__}"
        )
    if hasattr(fn, "__wrapped__"):
        raise LogosContractError(
            f"logos.theorem(about={fn.__name__!r}): wrapped or decorated functions are not "
            "supported; pass the undecorated module-level function"
        )
    if fn.__qualname__ != fn.__name__ or fn.__name__.startswith("<"):
        raise LogosContractError(
            f"logos.theorem(about=...): expected a module-level function, got "
            f"{fn.__qualname__!r}; lambdas, methods and nested functions are not supported"
        )


def _module_path(fn):
    module = inspect.getmodule(fn)
    if module is None or not isinstance(getattr(module, "__file__", None), str):
        raise LogosContractError(
            f"logos.theorem(about={fn.__name__!r}): the source is not available; import the "
            "function from a module file"
        )
    if fn.__module__ is None or sys.modules.get(fn.__module__) is not module:
        raise LogosContractError(
            f"logos.theorem(about={fn.__name__!r}): the defining module is not the imported "
            "module that holds it; import the function normally"
        )
    path = Path(module.__file__).resolve()
    source = inspect.getsourcefile(fn)
    if source is None or Path(source).resolve() != path:
        raise LogosContractError(
            f"logos.theorem(about={fn.__name__!r}): the function is not bound to "
            f"{path}; exec, eval and copied functions are not supported"
        )
    if not path.is_file():
        raise LogosContractError(
            f"logos.theorem(about={fn.__name__!r}): source file {path} is missing"
        )
    return path


def _read_source(path, fn):
    try:
        return path.read_bytes()
    except OSError as error:
        raise LogosContractError(
            f"logos.theorem(about={fn.__name__!r}): could not read {path}: {error}"
        ) from error


def _compile(source, path, fn):
    try:
        return compile(source, str(path), "exec", dont_inherit=True)
    except (SyntaxError, ValueError) as error:
        raise LogosContractError(
            f"logos.theorem(about={fn.__name__!r}): could not recompile {path}: {error}"
        ) from error


def _parse(source, path, fn):
    try:
        return ast.parse(source, filename=str(path))
    except SyntaxError as error:
        raise LogosContractError(
            f"logos.theorem(about={fn.__name__!r}): could not parse {path}: {error}"
        ) from error


def _module_code(compiled, name):
    for value in compiled.co_consts:
        if isinstance(value, CodeType) and value.co_name == name:
            return value
    return None


def _same_code(left, right):
    fields = (
        "co_argcount", "co_posonlyargcount", "co_kwonlyargcount", "co_nlocals",
        "co_flags", "co_code", "co_names", "co_varnames", "co_freevars", "co_cellvars",
    )
    if any(getattr(left, field) != getattr(right, field) for field in fields):
        return False
    if len(left.co_consts) != len(right.co_consts):
        return False
    for ours, theirs in zip(left.co_consts, right.co_consts):
        if isinstance(ours, CodeType) or isinstance(theirs, CodeType):
            if not (isinstance(ours, CodeType) and isinstance(theirs, CodeType)):
                return False
            if not _same_code(ours, theirs):
                return False
        elif type(ours) is not type(theirs) or ours != theirs:
            return False
    return True


def _int_annotation(node):
    return isinstance(node, ast.Name) and node.id == "int"


def _annotation_sort(node):
    if _int_annotation(node):
        return int
    if (
        isinstance(node, ast.Subscript)
        and isinstance(node.value, ast.Name)
        and node.value.id == "list"
        and _int_annotation(node.slice)
    ):
        return Seq
    return None


def _imported_sort(annotation):
    if annotation is int:
        return int
    import types
    if annotation == list[int]:
        return Seq
    if isinstance(annotation, types.GenericAlias) and annotation.__origin__ is list:
        args = annotation.__args__
        if args == (int,):
            return Seq
    return None


def _signature(definition, fn, path):
    """Validate the source signature and return (names, symbolic variables)."""
    arguments = definition.args
    if arguments.vararg or arguments.kwarg or arguments.kwonlyargs:
        raise LogosContractError(
            f"{path}:{definition.lineno}: {fn.__name__!r} must take plain positional "
            "parameters without *args, **kwargs or keyword-only parameters"
        )
    if arguments.defaults or any(value is not None for value in arguments.kw_defaults):
        raise LogosContractError(
            f"{path}:{definition.lineno}: {fn.__name__!r} must not declare default values; "
            "the theorem quantifies over every input"
        )
    parameters = [*arguments.posonlyargs, *arguments.args]
    names = [parameter.arg for parameter in parameters]
    variables = {}
    for parameter in parameters:
        sort = _annotation_sort(parameter.annotation)
        if sort is None:
            raise LogosContractError(
                f"{path}:{parameter.lineno}: parameter {parameter.arg!r} of "
                f"{fn.__name__!r} must be annotated with int or list[int]"
            )
        variables[parameter.arg] = Var(parameter.arg, sort)
    if not _int_annotation(definition.returns):
        raise LogosContractError(
            f"{path}:{definition.lineno}: {fn.__name__!r} must annotate its return with "
            "the built-in int"
        )
    annotations = fn.__annotations__
    for parameter in parameters:
        expected = _imported_sort(annotations.get(parameter.arg))
        if expected is None or expected is not variables[parameter.arg].type:
            raise LogosContractError(
                f"the imported {fn.__name__!r} must carry the built-in int or list[int] "
                f"annotation on {parameter.arg!r}; postponed annotations are not supported"
            )
    if _imported_sort(annotations.get("return")) is not int:
        raise LogosContractError(
            f"the imported {fn.__name__!r} must carry the built-in int return annotation; "
            "postponed annotations are not supported"
        )
    return names, variables


def _fragment(definition, fn, path, *, allow_decorators=False):
    if isinstance(definition, ast.AsyncFunctionDef):
        raise LogosContractError(
            f"{path}:{definition.lineno}: {fn.__name__!r} is async; only a synchronous "
            "function is supported"
        )
    if definition.decorator_list and not allow_decorators:
        raise LogosContractError(
            f"{path}:{definition.lineno}: {fn.__name__!r} is decorated; only an undecorated "
            "function is supported"
        )
    names, variables = _signature(definition, fn, path)
    body = definition.body
    if any(isinstance(node, (ast.While, ast.For, ast.AsyncFor)) for node in body):
        return _program_fragment(definition, fn, path, names, variables)
    if (
        len(body) == 1
        and isinstance(body[0], ast.If)
        and body[0].orelse
    ):
        node = body[0]
        if isinstance(node.orelse[0], ast.If):
            raise LogosContractError(
                f"{path}:{node.orelse[0].lineno}: {fn.__name__!r} uses elif; only one "
                "if/else with a return in each branch is supported"
            )
        guard = _condition(node.test, variables, fn, path)
        return names, variables, _Fragment(
            guard=guard,
            then_body=_return_term(node.body, variables, fn, path, "then branch"),
            else_body=_return_term(node.orelse, variables, fn, path, "else branch"),
        )
    if len(body) == 1 and isinstance(body[0], ast.If):
        raise LogosContractError(
            f"{path}:{body[0].lineno}: the if in {fn.__name__!r} needs an else branch with "
            "a return; add one so both paths are explicit"
        )
    if len(body) != 1 or not isinstance(body[0], ast.Return) or body[0].value is None:
        raise LogosContractError(
            f"{path}:{definition.lineno}: the body of {fn.__name__!r} must be a single "
            "return statement, one if/else with a return in each branch, or a loop program "
            "ending in one return; assignments and other statements are only supported "
            "with a loop"
        )
    return names, variables, _Fragment(
        body=_term(body[0].value, variables, fn, path)
    )


def _assigned_names(statements):
    for node in statements:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if not isinstance(target, ast.Name):
                    yield None, node.lineno
                else:
                    yield target.id, node.lineno
        elif isinstance(node, ast.AnnAssign):
            if not isinstance(node.target, ast.Name):
                yield None, node.lineno
            else:
                yield node.target.id, node.lineno
        elif isinstance(node, ast.If):
            yield from _assigned_names(node.body)
            yield from _assigned_names(node.orelse)
        elif isinstance(node, ast.AugAssign):
            if not isinstance(node.target, ast.Name):
                yield None, node.lineno
            else:
                yield node.target.id, node.lineno
        elif isinstance(node, ast.While):
            yield from _assigned_names(node.body)
            yield from _assigned_names(node.orelse)


def _program_fragment(definition, fn, path, names, variables):
    body = definition.body
    loops = [node for node in ast.walk(definition) if isinstance(node, ast.While)]
    if len(loops) != 1:
        raise LogosContractError(
            f"{path}:{definition.lineno}: {fn.__name__!r} must contain exactly one while "
            "loop in this fragment"
        )
    if any(isinstance(node, (ast.For, ast.AsyncFor)) for node in ast.walk(definition)):
        raise LogosContractError(
            f"{path}:{definition.lineno}: for loops are not supported; use one while loop"
        )
    if not isinstance(body[-1], ast.Return) or body[-1].value is None:
        raise LogosContractError(
            f"{path}:{definition.lineno}: the program in {fn.__name__!r} must end with one "
            "return statement"
        )
    if any(isinstance(node, ast.Return) for node in body[:-1]):
        raise LogosContractError(
            f"{path}:{definition.lineno}: {fn.__name__!r} may only return after the loop; "
            "early returns are not supported"
        )
    assigned = {}
    for name, line in _assigned_names(body):
        if name is None:
            raise LogosContractError(
                f"{path}:{line}: only plain local names can be assigned"
            )
        if name in variables:
            # Rebinding an integer parameter is local: Python passes the value,
            # so the caller's object is untouched. The parameter stays a program
            # variable and the contract's requires still speaks about its entry
            # value. Only new names become locals.
            continue
        assigned.setdefault(name, line)
    for name, line in assigned.items():
        if name.startswith("_"):
            raise LogosContractError(
                f"{path}:{line}: local {name!r} starts with an underscore; use a plain name"
            )
        variables[name] = Var(name, int)
    locals_ = tuple(
        ProgramVariable(name, int, variables[name]) for name in assigned
    )
    initialized = set(names)
    statements = []
    for node in body[:-1]:
        statement = _program_statement(node, variables, fn, path, initialized, top=True)
        statements.append(statement)
    ret = Return(_term(body[-1].value, variables, fn, path))
    statements.append(ret)
    params = tuple(ProgramVariable(name, variables[name].type, variables[name]) for name in names)
    result = ProgramVariable("result", int, Var("result", int))
    symbol = Function(
        fn.__name__,
        [variables[name] for name in names],
        None,
        result_type=int,
        portable_id=f"fn:{fn.__name__}",
    )
    program = Program(
        name=fn.__name__,
        function=symbol,
        params=params,
        result=result,
        locals=locals_,
        requires=Lit(True),
        ensures=Lit(True),
        body=tuple(statements),
        ghosts=(ProgramVariable("__variant", int, Var("__variant", int)),),
    )
    return names, variables, _Fragment(program=program)


def _program_statement(node, variables, fn, path, initialized, *, top=False):
    if isinstance(node, ast.Assign):
        if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
            raise LogosContractError(
                f"{path}:{node.lineno}: assignments in {fn.__name__!r} must name one local"
            )
        name = node.targets[0].id
        value = _term(node.value, variables, fn, path)
        for used in _used_names(node.value):
            if used not in variables:
                continue
            if used not in initialized:
                raise LogosContractError(
                    f"{path}:{node.lineno}: {used!r} is read before assignment in "
                    f"{fn.__name__!r}"
                )
        initialized.add(name)
        return Assign(name, value)
    if isinstance(node, ast.AugAssign):
        if not isinstance(node.target, ast.Name):
            raise LogosContractError(
                f"{path}:{node.lineno}: augmented assignments in {fn.__name__!r} must "
                "name one local"
            )
        name = node.target.id
        if name not in variables:
            raise LogosContractError(
                f"{path}:{node.lineno}: {name!r} is assigned before it is declared in "
                f"{fn.__name__!r}"
            )
        if name not in initialized:
            raise LogosContractError(
                f"{path}:{node.lineno}: {name!r} is read before assignment in "
                f"{fn.__name__!r}"
            )
        for used in _used_names(node.value):
            if used in variables and used not in initialized:
                raise LogosContractError(
                    f"{path}:{node.lineno}: {used!r} is read before assignment in "
                    f"{fn.__name__!r}"
                )
        right = _term(node.value, variables, fn, path)
        left = variables[name]
        if isinstance(node.op, ast.Add):
            value = Add(left, right)
        elif isinstance(node.op, ast.Sub):
            value = Sub(left, right)
        elif isinstance(node.op, ast.Mult):
            value = Mul(left, right)
        elif isinstance(node.op, ast.FloorDiv):
            value = Div(left, right)
        else:
            raise LogosContractError(
                f"{path}:{node.lineno}: unsupported augmented operator in "
                f"{fn.__name__!r}; use +=, -=, *= or //="
            )
        initialized.add(name)
        return Assign(name, value)
    if isinstance(node, ast.If):
        condition = _condition(node.test, variables, fn, path, ordered=True)
        then_initialized = set(initialized)
        else_initialized = set(initialized)
        then_body = tuple(
            _program_statement(item, variables, fn, path, then_initialized)
            for item in node.body
        )
        else_body = tuple(
            _program_statement(item, variables, fn, path, else_initialized)
            for item in node.orelse
        )
        if then_initialized != initialized or else_initialized != initialized:
            raise LogosContractError(
                f"{path}:{node.lineno}: each branch of the if in {fn.__name__!r} must "
                "assign exactly the same locals; this fragment keeps every local "
                "initialized before the branch"
            )
        return If(condition, then_body, else_body)
    if isinstance(node, ast.While):
        if node.orelse:
            raise LogosContractError(
                f"{path}:{node.lineno}: while/else is not supported"
            )
        condition = _condition(node.test, variables, fn, path, ordered=True)
        body_initialized = set(initialized)
        loop_body = tuple(
            _program_statement(item, variables, fn, path, body_initialized, top=True)
            for item in node.body
        )
        # A loop may introduce a temporary such as the midpoint. It is checked
        # for definite assignment inside the body; the return after the loop can
        # only read locals that were initialized before the loop.
        # The invariant and variant are filled from the contract after the body
        # is translated, so they are placeholders here.
        return While(condition, loop_body, Lit(True), Lit(0))
    if isinstance(node, ast.Return):
        raise LogosContractError(
            f"{path}:{node.lineno}: returns inside the loop are not supported; keep one "
            "return after the loop and carry the answer in a local"
        )
    if isinstance(node, ast.Pass):
        return If(Lit(False), (), ())
    raise LogosContractError(
        f"{path}:{getattr(node, 'lineno', '?')}: unsupported statement "
        f"{type(node).__name__} in {fn.__name__!r}; use assignments, one if/else tree, "
        "one while loop and one final return"
    )


def _used_names(node):
    for child in ast.walk(node):
        if isinstance(child, ast.Name) and isinstance(child.ctx, ast.Load):
            yield child.id


def _condition(node, variables, fn, path, *, ordered=False):
    if isinstance(node, ast.BoolOp) and isinstance(node.op, ast.And):
        result = _condition(node.values[0], variables, fn, path)
        for value in node.values[1:]:
            result = result & _condition(value, variables, fn, path)
        return result
    if isinstance(node, ast.BoolOp) and isinstance(node.op, ast.Or):
        result = _condition(node.values[0], variables, fn, path)
        for value in node.values[1:]:
            result = result | _condition(value, variables, fn, path)
        return result
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return ~_condition(node.operand, variables, fn, path)
    if isinstance(node, ast.Name) and node.id in variables and variables[node.id].type is int:
        # Python treats a nonzero integer as true. Production fragments use
        # this for sentinel flags; the checker sees the equivalent x != 0.
        return Not(Eq(variables[node.id], Lit(0)))
    if (
        not isinstance(node, ast.Compare)
        or len(node.ops) != 1
        or len(node.comparators) != 1
    ):
        expectation = (
            "one <, == or != comparison"
            if not ordered
            else "one comparison"
        )
        raise LogosContractError(
            f"{path}:{getattr(node, 'lineno', '?')}: the condition of {fn.__name__!r} must "
            f"be {expectation} between integer expressions"
        )
    left = _term(node.left, variables, fn, path)
    right = _term(node.comparators[0], variables, fn, path)
    operation = node.ops[0]
    if isinstance(operation, ast.Eq):
        return Eq(left, right)
    if isinstance(operation, ast.NotEq):
        return Not(Eq(left, right))
    if isinstance(operation, ast.Lt):
        return Lt(left, right)
    if isinstance(operation, ast.LtE) and ordered:
        return Le(left, right)
    if isinstance(operation, ast.Gt) and ordered:
        return Lt(right, left)
    if isinstance(operation, ast.GtE) and ordered:
        return Le(right, left)
    if not ordered:
        raise LogosContractError(
            f"{path}:{node.lineno}: the condition of {fn.__name__!r} uses an unsupported "
            "comparison; only <, == and != are supported"
        )
    raise LogosContractError(
        f"{path}:{node.lineno}: unsupported comparison in {fn.__name__!r}"
    )


def _return_term(statements, variables, fn, path, branch):
    if (
        len(statements) != 1
        or not isinstance(statements[0], ast.Return)
        or statements[0].value is None
    ):
        line = statements[0].lineno if statements else "?"
        raise LogosContractError(
            f"{path}:{line}: the {branch} of {fn.__name__!r} must be a single return "
            "statement; nested branches and other statements are not supported"
        )
    return _term(statements[0].value, variables, fn, path)


def _negate(expr):
    return expr.operand if isinstance(expr, Not) else Not(expr)


def _conjuncts(expr):
    if isinstance(expr, And):
        yield from _conjuncts(expr.left)
        yield from _conjuncts(expr.right)
    else:
        yield expr


def _select_branch(requires, guard, name):
    if requires is None:
        raise LogosContractError(
            f"contract for {name!r}: the source branches, so requires= must select one "
            "path with the condition or its negation; declare one theorem per branch"
        )
    for clause in _conjuncts(requires):
        if structural_eq(clause, guard):
            return "then"
        if structural_eq(clause, _negate(guard)):
            return "else"
    raise LogosContractError(
        f"contract for {name!r}: requires= does not select a branch; use the condition or "
        "its negation so the proof only covers that path"
    )


def _normalize(expr):
    """Rewrite derived comparisons before the portable encoding."""
    if isinstance(expr, Neq):
        return Not(Eq(_normalize(expr.left), _normalize(expr.right)))
    if isinstance(expr, Gt):
        return Lt(_normalize(expr.right), _normalize(expr.left))
    if isinstance(expr, Ge):
        return Le(_normalize(expr.right), _normalize(expr.left))
    if isinstance(expr, Implies):
        return Implies(_normalize(expr.antecedent), _normalize(expr.consequent))
    if isinstance(expr, (Add, Sub, Mul, Div, Eq, Le, Lt, And, Or)):
        return type(expr)(_normalize(expr.left), _normalize(expr.right))
    if isinstance(expr, Pow):
        return Pow(_normalize(expr.base), _normalize(expr.exp))
    if isinstance(expr, (Neg, Not)):
        return type(expr)(_normalize(expr.operand))
    if isinstance(expr, (ForallNode, ExistsNode)):
        return type(expr)(expr.var, _normalize(expr.body))
    if isinstance(expr, Len) or isinstance(expr, Sorted):
        return type(expr)(_normalize(expr.seq))
    if isinstance(expr, Nth):
        return Nth(_normalize(expr.seq), _normalize(expr.index))
    return expr


def _term(node, variables, fn, path, *, context=None):
    if isinstance(node, ast.Name):
        if node.id not in variables:
            raise LogosContractError(
                f"{path}:{node.lineno}: {node.id!r} in {fn.__name__!r} is not a parameter or "
                "local; globals, closures and other names are not supported"
            )
        return variables[node.id]
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return Lit(node.value)
    if isinstance(node, ast.BinOp):
        left = _term(node.left, variables, fn, path, context=context)
        right = _term(node.right, variables, fn, path, context=context)
        if isinstance(node.op, ast.Add):
            return Add(left, right)
        if isinstance(node.op, ast.Sub):
            return Sub(left, right)
        if isinstance(node.op, ast.Mult):
            return Mul(left, right)
        if isinstance(node.op, ast.FloorDiv):
            return Div(left, right)
        raise LogosContractError(
            f"{path}:{node.lineno}: unsupported operator in {fn.__name__!r}; use +, -, *, //"
        )
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return Neg(_term(node.operand, variables, fn, path, context=context))
    if isinstance(node, ast.Call):
        if (
            isinstance(node.func, ast.Name)
            and node.func.id == "len"
            and len(node.args) == 1
            and not node.keywords
        ):
            return Len(_term(node.args[0], variables, fn, path, context=context))
        if context is not None:
            return context.translate_call(node)
        raise LogosContractError(
            f"{path}:{node.lineno}: only len(xs) calls are supported in {fn.__name__!r}"
        )
    if isinstance(node, ast.Subscript):
        if isinstance(node.slice, ast.Slice):
            raise LogosContractError(
                f"{path}:{node.lineno}: slices are not supported in {fn.__name__!r}"
            )
        return Nth(
            _term(node.value, variables, fn, path, context=context),
            _term(node.slice, variables, fn, path, context=context),
        )
    raise LogosContractError(
        f"{path}:{getattr(node, 'lineno', '?')}: unsupported expression "
        f"{type(node).__name__} in {fn.__name__!r}; use parameters, locals, integer "
        "literals, +, -, *, //, len(xs) and xs[i]"
    )


def _theorem_signature(theorem_body, names, about):
    try:
        signature = inspect.signature(theorem_body)
    except (TypeError, ValueError) as error:
        raise LogosContractError(
            f"logos.theorem: could not read the signature of {theorem_body!r}: {error}"
        ) from error
    positional, keyword = [], []
    for parameter in signature.parameters.values():
        if parameter.default is not parameter.empty:
            raise LogosContractError(
                f"logos.theorem: {theorem_body.__name__!r} must not declare default values"
            )
        if parameter.kind in (
            inspect.Parameter.POSITIONAL_ONLY, inspect.Parameter.POSITIONAL_OR_KEYWORD
        ):
            positional.append(parameter.name)
        elif parameter.kind is inspect.Parameter.KEYWORD_ONLY:
            keyword.append(parameter.name)
        else:
            raise LogosContractError(
                f"logos.theorem: {theorem_body.__name__!r} must take the input names and "
                "exactly one keyword-only result parameter; *args and **kwargs are not supported"
            )
    if len(keyword) != 1:
        raise LogosContractError(
            f"logos.theorem: {theorem_body.__name__!r} needs exactly one keyword-only result "
            f"parameter, got {keyword!r}"
        )
    if tuple(positional) != tuple(names):
        raise LogosContractError(
            f"logos.theorem: {theorem_body.__name__!r} must take the inputs of "
            f"{about.__name__!r} by name and order: expected ({', '.join(names)}, *, "
            f"result), got ({', '.join(positional) or ''}, *, {', '.join(keyword)})"
        )
    return keyword[0]


def _validate(value, variables, result, theorem_body):
    if not isinstance(value, Contract):
        raise LogosContractError(
            f"logos.theorem: the body of {theorem_body.__name__!r} must return "
            f"logos.contract(...), got {type(value).__name__}"
        )
    allowed = {id(variable) for variable in variables.values()} | {id(result)}
    for variable in _variables(value.ensures):
        if id(variable) not in allowed:
            raise LogosContractError(
                f"logos.theorem: the contract mentions {variable.name!r}, which is not a "
                "parameter or the result; only the function signature binds values"
            )
    if not isinstance(value.ensures, Eq):
        raise LogosContractError(
            "logos.contract: ensures must be one equality between integer terms over the "
            "parameters and the result"
        )
    for side in (value.ensures.left, value.ensures.right):
        if _sort(side) is not int:
            raise LogosContractError(
                "logos.contract: both sides of ensures must be integer terms over the "
                "parameters and the result"
            )
    left = _mentions(value.ensures.left, result)
    right = _mentions(value.ensures.right, result)
    if left and right:
        raise LogosContractError(
            "logos.contract: ensure that the result appears on exactly one side of the "
            "equality; the checker rewrites the result through the source body"
        )
    if not (left or right):
        raise LogosContractError(
            "logos.contract: ensures must mention the keyword-only result parameter"
        )
    if value.requires is not None:
        for variable in _variables(value.requires):
            if variable is result:
                raise LogosContractError(
                    "logos.contract: requires must not mention the result; it is a premise "
                    "on the inputs"
                )
            if id(variable) not in {id(item) for item in variables.values()}:
                raise LogosContractError(
                    f"logos.contract: requires mentions {variable.name!r}, which is not an "
                    "input parameter"
                )
        if _sort(value.requires) is not bool:
            raise LogosContractError(
                "logos.contract: requires must be a proposition over the input parameters"
            )


def _variables(expr):
    if isinstance(expr, Var):
        yield expr
    elif isinstance(expr, Lit):
        return
    elif isinstance(expr, (Add, Sub, Mul, Div, Eq, Le, Lt, And, Or)):
        yield from _variables(expr.left)
        yield from _variables(expr.right)
    elif isinstance(expr, (Len, Sorted)):
        yield from _variables(expr.seq)
    elif isinstance(expr, Nth):
        yield from _variables(expr.seq)
        yield from _variables(expr.index)
    elif isinstance(expr, Implies):
        yield from _variables(expr.antecedent)
        yield from _variables(expr.consequent)
    elif isinstance(expr, Pow):
        yield from _variables(expr.base)
        yield from _variables(expr.exp)
    elif isinstance(expr, (Neg, Not)):
        yield from _variables(expr.operand)
    elif isinstance(expr, ForallNode):
        for variable in _variables(expr.body):
            if variable is not expr.var:
                yield variable
    elif isinstance(expr, ExistsNode):
        for variable in _variables(expr.body):
            if variable is not expr.var:
                yield variable
    else:
        raise LogosContractError(
            f"logos.contract: unsupported expression {type(expr).__name__}; use +, -, *, "
            "integer literals, equality, <, &, |, ~ and >>"
        )


def _sort(expr):
    if isinstance(expr, Var):
        from logos.sequence import SeqType
        if expr.type is int:
            return int
        if expr.type is bool:
            return bool
        if isinstance(expr.type, SeqType):
            return expr.type
        raise LogosContractError(
            f"logos.contract: unsupported sort {expr.type!r} on {expr.name!r}"
        )
    if isinstance(expr, Lit):
        if type(expr.value) is int:
            return int
        if type(expr.value) is bool:
            return bool
        raise LogosContractError(
            f"logos.contract: unsupported literal {expr.value!r}; use integers or booleans"
        )
    if isinstance(expr, (Add, Sub, Mul, Div)):
        if _sort(expr.left) is not int or _sort(expr.right) is not int:
            raise LogosContractError(
                f"logos.contract: {type(expr).__name__} expects integer operands"
            )
        return int
    if isinstance(expr, Pow):
        if (
            _sort(expr.base) is not int
            or not isinstance(expr.exp, Lit)
            or type(expr.exp.value) is not int
            or not 0 <= expr.exp.value <= 2**32 - 1
        ):
            raise LogosContractError(
                "logos.contract: ** expects an integer base and a non-negative integer "
                "literal exponent"
            )
        return int
    if isinstance(expr, Neg):
        if _sort(expr.operand) is not int:
            raise LogosContractError("logos.contract: unary - expects an integer operand")
        return int
    if isinstance(expr, Len):
        from logos.sequence import SeqType
        if not isinstance(_sort(expr.seq), SeqType):
            raise LogosContractError("logos.contract: len expects a sequence")
        return int
    if isinstance(expr, Nth):
        from logos.sequence import SeqType
        if not isinstance(_sort(expr.seq), SeqType) or _sort(expr.index) is not int:
            raise LogosContractError("logos.contract: nth expects a sequence and an integer index")
        return int
    if isinstance(expr, Sorted):
        from logos.sequence import SeqType
        if not isinstance(_sort(expr.seq), SeqType):
            raise LogosContractError("logos.contract: sorted expects a sequence")
        return bool
    if isinstance(expr, Le):
        if _sort(expr.left) is not int or _sort(expr.right) is not int:
            raise LogosContractError("logos.contract: <= expects integer operands")
        return bool
    if isinstance(expr, (ForallNode, ExistsNode)):
        if _sort(expr.body) is not bool:
            raise LogosContractError(
                "logos.contract: a quantifier body must be a proposition"
            )
        return bool
    if isinstance(expr, Eq):
        if _sort(expr.left) is not _sort(expr.right):
            raise LogosContractError(
                "logos.contract: equality compares terms of different sorts"
            )
        return bool
    if isinstance(expr, Lt):
        if _sort(expr.left) is not int or _sort(expr.right) is not int:
            raise LogosContractError(
                "logos.contract: < expects integer operands"
            )
        return bool
    if isinstance(expr, (And, Or)):
        if _sort(expr.left) is not bool or _sort(expr.right) is not bool:
            raise LogosContractError(
                f"logos.contract: {type(expr).__name__} expects proposition operands"
            )
        return bool
    if isinstance(expr, Implies):
        if _sort(expr.antecedent) is not bool or _sort(expr.consequent) is not bool:
            raise LogosContractError("logos.contract: >> expects proposition operands")
        return bool
    if isinstance(expr, Not):
        if _sort(expr.operand) is not bool:
            raise LogosContractError("logos.contract: ~ expects a proposition")
        return bool
    if isinstance(expr, App):
        if expr.symbol is None or expr.symbol.result_type is None:
            raise LogosContractError(
                f"logos.contract: call {expr.func_name!r} has no declared result type"
            )
        for argument, parameter in zip(expr.args, expr.symbol.params):
            if _sort(argument) is not parameter.type:
                raise LogosContractError(
                    f"logos.contract: argument of {expr.func_name!r} has the wrong sort"
                )
        return expr.symbol.result_type
    raise LogosContractError(
        f"logos.contract: unsupported expression {type(expr).__name__}; the portable format "
        "supports integer +, -, *, ** with literal exponents, equality, <, &, |, ~ and >>"
    )


def _mentions(expr, variable):
    return any(item is variable for item in _variables(expr))


def _replace(expr, needle, value):
    if isinstance(expr, Var):
        return value if expr is needle else expr
    if isinstance(expr, Lit):
        return expr
    if isinstance(expr, (Add, Sub, Mul, Eq, Lt, And, Or)):
        return type(expr)(_replace(expr.left, needle, value), _replace(expr.right, needle, value))
    if isinstance(expr, Implies):
        return Implies(
            _replace(expr.antecedent, needle, value),
            _replace(expr.consequent, needle, value),
        )
    if isinstance(expr, Pow):
        return Pow(_replace(expr.base, needle, value), _replace(expr.exp, needle, value))
    if isinstance(expr, (Neg, Not)):
        return type(expr)(_replace(expr.operand, needle, value))
    raise LogosContractError(
        f"logos.contract: cannot rewrite through {type(expr).__name__}"
    )


def _derive(symbol, parameters, result, requires, ensures):
    equality = Eq(result, App(symbol.name, list(parameters), symbol))
    hole = Var("hole", int)
    if _mentions(ensures.left, result):
        template = _replace(ensures.left, result, hole)
        other = ensures.right
        certificate = Congr(hole, template, HypRef("value"))
        arithmetic = _arithmetic(
            _replace(template, hole, symbol.body), other, requires, symbol
        )
        proof = Trans(certificate, arithmetic)
    else:
        template = _replace(ensures.right, result, hole)
        other = ensures.left
        certificate = Congr(hole, template, HypRef("value"))
        arithmetic = _arithmetic(
            other, _replace(template, hole, symbol.body), requires, symbol
        )
        proof = Trans(arithmetic, Symm(certificate))
    proof = ImpliesIntro(equality, "value", proof)
    if requires is not None:
        proof = ImpliesIntro(requires, "requires", proof)
    proof = ForallIntro(result, proof)
    for parameter in reversed(list(parameters)):
        proof = ForallIntro(parameter, proof)
    return proof


def _arithmetic(left, right, requires, symbol):
    """Prove ``left = right``, using one parameter equals a literal premise.

    A branch theorem can state its claim at the guard boundary, for example
    ``requires=(x == 0)`` with a postcondition in the other branch's formula.
    In that case the premise is substituted into both sides before the ring
    checker runs, and the substitution is replayed as checked congruences.
    """
    substitution = _literal_substitution(requires)
    if substitution is None:
        return _ring(left, right, symbol)
    variable, value, premise, hole = substitution
    left_premise = Congr(hole, _replace(left, variable, hole), premise)
    right_premise = Congr(hole, _replace(right, variable, hole), premise)
    core = _ring(
        _replace(left, variable, value), _replace(right, variable, value), symbol
    )
    return Trans(Trans(left_premise, core), Symm(right_premise))


def _literal_substitution(requires):
    """Return (parameter, integer literal, proof, hole) for one simple premise."""
    if not isinstance(requires, Eq):
        return None
    hole = Var("hole", int)
    if (
        isinstance(requires.left, Var)
        and isinstance(requires.right, Lit)
        and type(requires.right.value) is int
    ):
        return requires.left, requires.right, HypRef("requires"), hole
    if (
        isinstance(requires.right, Var)
        and isinstance(requires.left, Lit)
        and type(requires.left.value) is int
    ):
        return requires.right, requires.left, Symm(HypRef("requires")), hole
    return None


def _ring(left, right, symbol):
    try:
        return Ring().prove(Eq(left, right))
    except (TacticFailed, RecursionError) as error:
        raise LogosContractError(
            f"contract for {symbol.name!r} does not follow from its source body: {error}"
        ) from error


# ── Declarative functions ───────────────────────────────────────────────────


def _trivial():
    """A proposition the checker proves by reflexivity, used for empty clauses."""
    return Eq(Lit(0), Lit(0))


def _and_all(expressions):
    expressions = list(expressions)
    if not expressions:
        return _trivial()
    result = expressions[-1]
    for expression in reversed(expressions[:-1]):
        result = And(expression, result)
    return result


def _source_digest(text, node):
    segment = ast.get_source_segment(text, node)
    if segment is None:
        segment = ast.dump(node)
    return sha256(segment.encode("utf-8")).hexdigest()


@dataclass
class TranslatedFunction:
    """The source-bound executable program of one declarative function."""

    path: Path
    source: bytes
    code: CodeType
    definition: ast.FunctionDef
    names: list[str]
    variables: dict[str, Var]
    program: Program
    entry_locals: tuple[str, ...]
    source_digest: str
    calls: tuple[Call, ...]


def _logos_function_decorator(node):
    """True when the decorator is spelled ``logos.function`` or ``function``."""
    if isinstance(node, ast.Name):
        return node.id == "function"
    if isinstance(node, ast.Attribute):
        return (
            node.attr == "function"
            and isinstance(node.value, ast.Name)
            and node.value.id == "logos"
        )
    return False


def _check_decorators(definition, fn, path):
    if isinstance(definition, ast.AsyncFunctionDef):
        raise LogosContractError(
            f"{path}:{definition.lineno}: {fn.__name__!r} is async; only a synchronous "
            "function is supported"
        )
    for decorator in definition.decorator_list:
        if not _logos_function_decorator(decorator):
            raise LogosContractError(
                f"{path}:{getattr(decorator, 'lineno', definition.lineno)}: "
                f"{fn.__name__!r} carries a decorator other than @logos.function; "
                "only the declarative decorator is supported on a checked function"
            )
    if not definition.decorator_list:
        raise LogosContractError(
            f"{path}:{definition.lineno}: {fn.__name__!r} is not decorated with "
            "@logos.function"
        )


class _DeclContext:
    """Translate one function body, collecting call sites as it goes."""

    def __init__(self, fn, path, module, variables, names):
        self.fn = fn
        self.path = path
        self.module = module
        self.variables = variables
        self.names = list(names)
        self.local_order: list[str] = []
        self.calls: list[Call] = []
        self.entry_locals: tuple[str, ...] = ()
        self.loop_seen = False
        self.emit = None

    def _fresh(self, base):
        name = base
        suffix = 2
        while name in self.variables:
            name = f"{base}_{suffix}"
            suffix += 1
        self.variables[name] = Var(name, int)
        self.local_order.append(name)
        return name

    def translate_call(self, node):
        line = node.lineno
        if not isinstance(node.func, ast.Name):
            raise LogosContractError(
                f"{self.path}:{line}: {self.fn.__name__!r} may only call a function by "
                "its module-level name"
            )
        name = node.func.id
        if name in self.variables:
            raise LogosContractError(
                f"{self.path}:{line}: {self.fn.__name__!r} tries to call {name!r}, which is "
                "a parameter or local; calls to values are not supported"
            )
        value = self.module.__dict__.get(name)
        callee = getattr(value, "__logos_function__", None)
        if callee is None:
            raise LogosContractError(
                f"{self.path}:{line}: {self.fn.__name__!r} calls {name!r}, which is not "
                "declared with @logos.function; only checked functions can be called"
            )
        if node.keywords:
            raise LogosContractError(
                f"{self.path}:{line}: the call to {name!r} uses keyword arguments; "
                "only positional arguments are supported"
            )
        args = tuple(
            _term(arg, self.variables, self.fn, self.path, context=self)
            for arg in node.args
        )
        params = callee.params
        if len(args) != len(params):
            raise LogosContractError(
                f"{self.path}:{line}: {name!r} takes {len(params)} argument(s) but the "
                f"call passes {len(args)}"
            )
        for index, (arg, param) in enumerate(zip(args, params)):
            if _sort(arg) is not param.type:
                raise LogosContractError(
                    f"{self.path}:{line}: argument {index + 1} of {name!r} must have sort "
                    f"{param.type!r}, got {arg!r}"
                )
        target = self._fresh(f"{name}_result")
        call = Call(
            id=f"call{len(self.calls)}",
            target=target,
            callee=callee,
            function=callee.function,
            args=args,
            line=line,
            fingerprint=callee.fingerprint(),
        )
        self.calls.append(call)
        if self.emit is None:
            raise LogosContractError(
                f"{self.path}:{line}: a call to {name!r} is only supported in an "
                "assignment or a return statement"
            )
        self.emit(call)
        return self.variables[target]


def _decl_statement(node, context, initialized, *, top, in_loop):
    if isinstance(node, ast.Assign):
        if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
            raise LogosContractError(
                f"{context.path}:{node.lineno}: assignments in {context.fn.__name__!r} "
                "must name one local"
            )
        name = node.targets[0].id
        if name.startswith("_"):
            raise LogosContractError(
                f"{context.path}:{node.lineno}: local {name!r} starts with an underscore; "
                "use a plain name"
            )
        emitted = []
        context.emit = emitted.append
        value = _term(node.value, context.variables, context.fn, context.path, context=context)
        context.emit = None
        if name not in context.variables:
            context.variables[name] = Var(name, int)
            context.local_order.append(name)
        for used in _used_names(node.value):
            if used in context.variables and used not in initialized:
                raise LogosContractError(
                    f"{context.path}:{node.lineno}: {used!r} is read before assignment in "
                    f"{context.fn.__name__!r}"
                )
        initialized.add(name)
        return [*emitted, Assign(name, value)], False
    if isinstance(node, ast.AugAssign):
        if not isinstance(node.target, ast.Name):
            raise LogosContractError(
                f"{context.path}:{node.lineno}: augmented assignments in "
                f"{context.fn.__name__!r} must name one local"
            )
        name = node.target.id
        if name not in context.variables:
            raise LogosContractError(
                f"{context.path}:{node.lineno}: {name!r} is assigned before it is declared "
                f"in {context.fn.__name__!r}"
            )
        if name not in initialized:
            raise LogosContractError(
                f"{context.path}:{node.lineno}: {name!r} is read before assignment in "
                f"{context.fn.__name__!r}"
            )
        emitted = []
        context.emit = emitted.append
        right = _term(node.value, context.variables, context.fn, context.path, context=context)
        context.emit = None
        left = context.variables[name]
        if isinstance(node.op, ast.Add):
            value = Add(left, right)
        elif isinstance(node.op, ast.Sub):
            value = Sub(left, right)
        elif isinstance(node.op, ast.Mult):
            value = Mul(left, right)
        elif isinstance(node.op, ast.FloorDiv):
            value = Div(left, right)
        else:
            raise LogosContractError(
                f"{context.path}:{node.lineno}: unsupported augmented operator in "
                f"{context.fn.__name__!r}; use +=, -=, *= or //="
            )
        return [*emitted, Assign(name, value)], False
    if isinstance(node, ast.If):
        if not node.orelse:
            raise LogosContractError(
                f"{context.path}:{node.lineno}: the if in {context.fn.__name__!r} needs an "
                "else branch; every path must be explicit"
            )
        condition = _condition(node.test, context.variables, context.fn, context.path, ordered=True)
        then_initialized = set(initialized)
        else_initialized = set(initialized)
        then_statements, then_returns = _decl_statement_list(
            node.body, context, then_initialized, top=False, in_loop=in_loop
        )
        else_statements, else_returns = _decl_statement_list(
            node.orelse, context, else_initialized, top=False, in_loop=in_loop
        )
        if then_returns != else_returns:
            raise LogosContractError(
                f"{context.path}:{node.lineno}: in {context.fn.__name__!r} both branches of "
                "an if must return or neither may return"
            )
        if not then_returns:
            if then_initialized != initialized or else_initialized != initialized:
                raise LogosContractError(
                    f"{context.path}:{node.lineno}: each branch of the if in "
                    f"{context.fn.__name__!r} must assign exactly the same locals; this "
                    "fragment keeps every local initialized before the branch"
                )
        return [If(condition, tuple(then_statements), tuple(else_statements))], then_returns
    if isinstance(node, ast.While):
        if in_loop:
            raise LogosContractError(
                f"{context.path}:{node.lineno}: nested loops are not supported in "
                f"{context.fn.__name__!r}"
            )
        if not top:
            raise LogosContractError(
                f"{context.path}:{node.lineno}: the while loop in {context.fn.__name__!r} "
                "must be a direct statement of the function body, not inside an if"
            )
        if context.loop_seen:
            raise LogosContractError(
                f"{context.path}:{node.lineno}: {context.fn.__name__!r} must contain "
                "exactly one while loop"
            )
        if node.orelse:
            raise LogosContractError(
                f"{context.path}:{node.lineno}: while/else is not supported"
            )
        condition = _condition(node.test, context.variables, context.fn, context.path, ordered=True)
        context.loop_seen = True
        context.entry_locals = tuple(
            name for name in context.local_order if name in initialized
        )
        body_initialized = set(initialized)
        body, body_returns = _decl_statement_list(
            node.body, context, body_initialized, top=False, in_loop=True
        )
        if body_returns:
            raise LogosContractError(
                f"{context.path}:{node.lineno}: returns inside the loop are not supported; "
                "keep one return after the loop and carry the answer in a local"
            )
        return [While(condition, tuple(body), _trivial(), Lit(0))], False
    if isinstance(node, ast.Return):
        if in_loop:
            raise LogosContractError(
                f"{context.path}:{node.lineno}: returns inside the loop are not supported; "
                "keep one return after the loop and carry the answer in a local"
            )
        if node.value is None:
            raise LogosContractError(
                f"{context.path}:{node.lineno}: {context.fn.__name__!r} must return a value"
            )
        emitted = []
        context.emit = emitted.append
        value = _term(node.value, context.variables, context.fn, context.path, context=context)
        context.emit = None
        return [*emitted, Return(value)], True
    if isinstance(node, ast.Pass):
        return [], False
    raise LogosContractError(
        f"{context.path}:{getattr(node, 'lineno', '?')}: unsupported statement "
        f"{type(node).__name__} in {context.fn.__name__!r} at @logos.function; use "
        "assignments, one if/else tree, one while loop and returns of integer expressions"
    )


def _decl_statement_list(statements, context, initialized, *, top, in_loop):
    result = []
    returned = False
    for node in statements:
        if returned:
            raise LogosContractError(
                f"{context.path}:{getattr(node, 'lineno', '?')}: unreachable statement after "
                f"a return in {context.fn.__name__!r}"
            )
        emitted, returned = _decl_statement(
            node, context, initialized, top=top, in_loop=in_loop
        )
        result.extend(emitted)
    return result, returned


def translate_declarative(fn, function):
    """Translate a ``@logos.function`` body, rejecting unsupported syntax now."""
    _require_ordinary(fn)
    path = _module_path(fn)
    source = _read_source(path, fn)
    compiled = _compile(source, path, fn)
    tree = _parse(source, path, fn)
    definitions = [
        node for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == fn.__name__
    ]
    if not definitions:
        raise LogosContractError(
            f"logos.function: {path} has no top-level definition of {fn.__name__!r}"
        )
    if len(definitions) > 1:
        raise LogosContractError(
            f"logos.function: {path} defines {fn.__name__!r} {len(definitions)} times at "
            "module level; keep exactly one definition"
        )
    definition = definitions[0]
    _check_decorators(definition, fn, path)
    expected = _module_code(compiled, fn.__name__)
    if expected is None or not _same_code(expected, fn.__code__):
        raise LogosContractError(
            f"source of {fn.__name__!r} in {path} does not match the imported code object; "
            "the module is stale or the file changed after import; reimport it before "
            "declaring the function"
        )
    names, variables = _signature(definition, fn, path)
    if "result" in variables:
        raise LogosContractError(
            f"{path}:{definition.lineno}: {fn.__name__!r} must not name a parameter "
            "'result'; that name is reserved for the postcondition"
        )
    module = inspect.getmodule(fn)
    context = _DeclContext(fn, path, module, variables, names)
    initialized = set(names)
    statements, returned = _decl_statement_list(
        definition.body, context, initialized, top=True, in_loop=False
    )
    if not returned:
        raise LogosContractError(
            f"{path}:{definition.lineno}: {fn.__name__!r} must return a value on every path"
        )
    parameters = tuple(
        ProgramVariable(name, variables[name].type, variables[name]) for name in names
    )
    locals_ = tuple(
        ProgramVariable(name, int, variables[name]) for name in context.local_order
    )
    result = ProgramVariable("result", int, Var("result", int))
    ghosts = (
        (ProgramVariable("__variant", int, Var("__variant", int)),)
        if context.loop_seen else ()
    )
    program = Program(
        name=fn.__name__,
        function=function,
        params=parameters,
        result=result,
        locals=locals_,
        requires=_trivial(),
        ensures=_trivial(),
        body=tuple(statements),
        ghosts=ghosts,
    )
    text = source.decode("utf-8")
    return TranslatedFunction(
        path=path,
        source=source,
        code=fn.__code__,
        definition=definition,
        names=names,
        variables=variables,
        program=program,
        entry_locals=context.entry_locals,
        source_digest=_source_digest(text, definition),
        calls=tuple(context.calls),
    )
