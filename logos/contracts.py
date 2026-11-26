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
from dataclasses import dataclass
from pathlib import Path
from types import CodeType, FunctionType

from logos.define import Function
from logos.expr import (
    Add, And, App, Eq, Expr, ExistsNode, ForallNode, Implies, Lit, Lt, Mul,
    Neg, Neq, Not, Or, Pow, Sub, Var,
)
from logos.goal import Goal
from logos.helpers import structural_eq
from logos.kernel import Congr, ForallIntro, HypRef, ImpliesIntro, Symm, Trans
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


def _fragment(definition, fn, path):
    if isinstance(definition, ast.AsyncFunctionDef):
        raise LogosContractError(
            f"{path}:{definition.lineno}: {fn.__name__!r} is async; only a synchronous "
            "function is supported"
        )
    if definition.decorator_list:
        raise LogosContractError(
            f"{path}:{definition.lineno}: {fn.__name__!r} is decorated; only an undecorated "
            "function is supported"
        )
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
    for parameter in parameters:
        if not _int_annotation(parameter.annotation):
            raise LogosContractError(
                f"{path}:{parameter.lineno}: parameter {parameter.arg!r} of "
                f"{fn.__name__!r} must be annotated with the built-in int"
            )
    if not _int_annotation(definition.returns):
        raise LogosContractError(
            f"{path}:{definition.lineno}: {fn.__name__!r} must annotate its return with "
            "the built-in int"
        )
    annotations = fn.__annotations__
    for name in names:
        if annotations.get(name) is not int:
            raise LogosContractError(
                f"the imported {fn.__name__!r} must carry the built-in int annotation on "
                f"{name!r}; postponed annotations are not supported"
            )
    if annotations.get("return") is not int:
        raise LogosContractError(
            f"the imported {fn.__name__!r} must carry the built-in int return annotation; "
            "postponed annotations are not supported"
        )
    body = definition.body
    variables = {name: Var(name, int) for name in names}
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
            "return statement or one if/else with a return in each branch; loops, "
            "assignments and other statements are not supported"
        )
    return names, variables, _Fragment(
        body=_term(body[0].value, variables, fn, path)
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


def _condition(node, variables, fn, path):
    if (
        not isinstance(node, ast.Compare)
        or len(node.ops) != 1
        or len(node.comparators) != 1
    ):
        raise LogosContractError(
            f"{path}:{getattr(node, 'lineno', '?')}: the condition of {fn.__name__!r} must "
            "be one <, == or != comparison between integer expressions"
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
    raise LogosContractError(
        f"{path}:{node.lineno}: the condition of {fn.__name__!r} uses an unsupported "
        "comparison; only <, == and != are supported"
    )


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
    """Rewrite ``!=`` to ``~(... == ...)`` before the portable encoding."""
    if isinstance(expr, Neq):
        return Not(Eq(_normalize(expr.left), _normalize(expr.right)))
    if isinstance(expr, (Add, Sub, Mul, Eq, Lt, And, Or, Implies)):
        return type(expr)(_normalize(expr.left), _normalize(expr.right))
    if isinstance(expr, Pow):
        return Pow(_normalize(expr.base), _normalize(expr.exp))
    if isinstance(expr, (Neg, Not)):
        return type(expr)(_normalize(expr.operand))
    return expr


def _term(node, variables, fn, path):
    if isinstance(node, ast.Name):
        if node.id not in variables:
            raise LogosContractError(
                f"{path}:{node.lineno}: {node.id!r} in {fn.__name__!r} is not a parameter; "
                "globals, closures and other names are not supported"
            )
        return variables[node.id]
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return Lit(node.value)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return Add(
            _term(node.left, variables, fn, path),
            _term(node.right, variables, fn, path),
        )
    raise LogosContractError(
        f"{path}:{getattr(node, 'lineno', '?')}: unsupported expression "
        f"{type(node).__name__} in {fn.__name__!r}; only parameters, integer literals "
        "and + are supported"
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
    elif isinstance(expr, (Add, Sub, Mul, Eq, Lt, And, Or)):
        yield from _variables(expr.left)
        yield from _variables(expr.right)
    elif isinstance(expr, Implies):
        yield from _variables(expr.antecedent)
        yield from _variables(expr.consequent)
    elif isinstance(expr, Pow):
        yield from _variables(expr.base)
        yield from _variables(expr.exp)
    elif isinstance(expr, (Neg, Not)):
        yield from _variables(expr.operand)
    elif isinstance(expr, (ForallNode, ExistsNode)):
        raise LogosContractError(
            "logos.contract: quantifiers are not supported inside a contract; the function "
            "signature is the universe and requires= supplies explicit premises"
        )
    else:
        raise LogosContractError(
            f"logos.contract: unsupported expression {type(expr).__name__}; use +, -, *, "
            "integer literals, equality, <, &, |, ~ and >>"
        )


def _sort(expr):
    if isinstance(expr, Var):
        if expr.type is int:
            return int
        if expr.type is bool:
            return bool
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
    if isinstance(expr, (Add, Sub, Mul)):
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
