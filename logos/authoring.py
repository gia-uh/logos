"""The author-facing proof style used by the Logos book.

A theorem keeps its existing statement form::

    @logos.theorem
    def first_fact(P: Prop, Q: Prop):
        return (P & Q) >> P

A proof function receives a context ``p`` first, then one Python object for
each universally quantified variable.  The context records what may be used
and what remains to be proved::

    @first_fact.proof
    def prove_first(p, P, Q):
        both = p.assume(P & Q)
        return both.left()

The operations are deliberately small.  ``assume`` introduces an
implication, ``obtain`` opens a checked existential, ``ring`` proves an
integer identity from equations already in scope, and ``witness`` closes an
existential goal.  Every returned term is built from the trusted kernel terms;
this module only chooses the terms.
"""
from __future__ import annotations

import ast
import inspect
import linecache
import os
from collections import deque
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

from logos.expr import (
    Add, And, App, Eq, ExistsNode, Expr, ForallNode, Implies, Lit, Mul, Neg,
    Not, Or, Sub, Var,
)
from logos.helpers import free_symbol_ids, structural_eq, substitute_symbols
from logos.kernel import (
    AndElimL, AndElimR, Congr, ExistsElim, ExistsIntro, ForallIntro, HypRef,
    ImpliesIntro, ProofTerm, Refl, Symm, Trans,
)
from logos.portable import LogosProofError
from logos.runner import TacticFailed
from logos.tactics._ring import Ring


# ── Errors ────────────────────────────────────────────────────────────────────


def _sort_name(type_) -> str:
    if type_ is int:
        return "Int"
    if type_ in (bool, object):
        return "Prop"
    name = getattr(type_, "__name__", None)
    return name or repr(type_)


_PREC = {
    "implies": 1,
    "or": 2,
    "and": 3,
    "eq": 4,
    "add": 5,
    "mul": 6,
    "unary": 7,
    "atom": 8,
}


def _render(expr: Expr, parent: int = 0) -> str:
    match expr:
        case Var(name, _):
            return name
        case Lit(value):
            return repr(value) if isinstance(value, str) else str(value)
        case Add(left, right):
            text = f"{_render(left, _PREC['add'])} + {_render(right, _PREC['add'] + 1)}"
            return f"({text})" if _PREC["add"] < parent else text
        case Sub(left, right):
            text = f"{_render(left, _PREC['add'])} - {_render(right, _PREC['add'] + 1)}"
            return f"({text})" if _PREC["add"] < parent else text
        case Mul(left, right):
            text = f"{_render(left, _PREC['mul'])} * {_render(right, _PREC['mul'] + 1)}"
            return f"({text})" if _PREC["mul"] < parent else text
        case Neg(operand):
            text = f"-{_render(operand, _PREC['unary'])}"
            return f"({text})" if _PREC["unary"] < parent else text
        case Eq(left, right):
            text = f"{_render(left, _PREC['eq'] + 1)} = {_render(right, _PREC['eq'] + 1)}"
            return f"({text})" if _PREC["eq"] < parent else text
        case And(left, right):
            text = f"{_render(left, _PREC['and'] + 1)} & {_render(right, _PREC['and'] + 1)}"
            return f"({text})" if _PREC["and"] < parent else text
        case Or(left, right):
            text = f"{_render(left, _PREC['or'] + 1)} | {_render(right, _PREC['or'] + 1)}"
            return f"({text})" if _PREC["or"] < parent else text
        case Not(operand):
            text = f"~{_render(operand, _PREC['unary'])}"
            return f"({text})" if _PREC["unary"] < parent else text
        case Implies(antecedent, consequent):
            text = f"{_render(antecedent, _PREC['implies'] + 1)} >> {_render(consequent, _PREC['implies'])}"
            return f"({text})" if _PREC["implies"] < parent else text
        case ForallNode(var, body):
            return f"forall {var.name}:{_sort_name(var.type)}. {_render(body)}"
        case ExistsNode(var, body):
            return f"exists {var.name}:{_sort_name(var.type)}. {_render(body)}"
        case App(name, args, _):
            rendered = ", ".join(_render(arg) for arg in args)
            return f"{name}({rendered})"
        case _:
            return repr(expr)


def format_expr(expr: Expr) -> str:
    """Render an expression the way a reader writes it in the book."""
    return _render(expr, 0)


def _detail_expr(expr: Expr) -> dict:
    return {"text": format_expr(expr), "repr": repr(expr)}


def _detail_fact(fact: "Fact") -> dict:
    return {
        "label": fact.label,
        "statement": _detail_expr(fact.statement),
        "file": fact.file,
        "line": fact.line,
        "source_line": fact.source_line,
    }


class AuthoringFailure(LogosProofError):
    """A failed authoring step with a human message and machine data."""

    def __init__(
        self,
        kind: str,
        message: str,
        *,
        theorem: str | None = None,
        file: str | None = None,
        line: int | None = None,
        source_line: str | None = None,
        goal: Expr | None = None,
        expected: Expr | str | None = None,
        got: Expr | str | None = None,
        hypotheses: tuple = (),
        opened: tuple = (),
        related: tuple = (),
        extra: dict | None = None,
    ):
        self.kind = kind
        self.theorem = theorem
        self.file = file
        self.line = line
        self.source_line = source_line
        self.goal = goal
        self.expected = expected
        self.got = got
        self.hypotheses = tuple(hypotheses)
        self.opened = tuple(opened)
        self.related = tuple(related)
        self.extra = extra or {}
        super().__init__(self._build_message(message))
        self.details = self.as_dict()

    def _build_message(self, summary: str) -> str:
        where = ""
        if self.file and self.line:
            where = f" at {os.path.basename(self.file)}:{self.line}"
        prefix = f"Theorem '{self.theorem}': " if self.theorem else ""
        lines = [f"{prefix}{summary}{where}"]
        if self.goal is not None:
            lines.append(f"  expected goal: {format_expr(self.goal)}")
        if self.expected is not None:
            text = (
                format_expr(self.expected)
                if isinstance(self.expected, Expr)
                else str(self.expected)
            )
            lines.append(f"  expected: {text}")
        if self.got is not None:
            text = format_expr(self.got) if isinstance(self.got, Expr) else str(self.got)
            lines.append(f"  got: {text}")
        if self.opened:
            lines.append("  opened hypotheses:")
            for fact in self.opened:
                location = (
                    f" ({os.path.basename(fact.file)}:{fact.line})"
                    if fact.file and fact.line
                    else ""
                )
                lines.append(
                    f"    {fact.label}: {format_expr(fact.statement)}{location}"
                )
        if self.hypotheses and not self.opened:
            lines.append("  hypotheses in scope:")
            for name, statement in self.hypotheses:
                lines.append(f"    {name}: {format_expr(statement)}")
        if self.related:
            lines.append("  related authored lines:")
            for item in self.related:
                lines.append(
                    f"    {os.path.basename(item['file'])}:{item['line']}: "
                    f"{item['source_line']}"
                )
        if self.source_line:
            lines.append(f"  failing source: {self.source_line}")
        return "\n".join(lines)

    def as_dict(self) -> dict:
        return {
            "kind": self.kind,
            "theorem": self.theorem,
            "message": str(self),
            "file": self.file,
            "line": self.line,
            "source_line": self.source_line,
            "goal": _detail_expr(self.goal) if self.goal is not None else None,
            "expected": (
                _detail_expr(self.expected)
                if isinstance(self.expected, Expr)
                else self.expected
            ),
            "got": (
                _detail_expr(self.got)
                if isinstance(self.got, Expr)
                else self.got
            ),
            "hypotheses": [
                {"name": name, "statement": _detail_expr(statement)}
                for name, statement in self.hypotheses
            ],
            "opened": [_detail_fact(fact) for fact in self.opened],
            "related": list(self.related),
            **self.extra,
        }


# ── Source locations ─────────────────────────────────────────────────────────


@lru_cache(maxsize=64)
def _parse(path: str, stamp: int):
    try:
        text = Path(path).read_text(encoding="utf-8")
    except (OSError, UnicodeError):
        return None
    try:
        return ast.parse(text)
    except SyntaxError:
        return None


def _tree(path: str):
    try:
        stamp = os.stat(path).st_mtime_ns
    except OSError:
        return None
    return _parse(path, stamp)


def _line_text(path: str, line: int) -> str:
    return linecache.getline(path, line).strip()


def _absolute(path: str) -> str:
    if path.startswith("<") and path.endswith(">"):
        return path
    try:
        return str(Path(path).resolve())
    except OSError:
        return path


def _enclosing_function(tree, line: int):
    best = None
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            end = getattr(node, "end_lineno", node.lineno)
            if node.lineno <= line <= end:
                if best is None or node.lineno >= best.lineno:
                    best = node
    return best


def _assignment_at(tree, line: int):
    candidates = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.Assign, ast.AnnAssign)):
            end = getattr(node, "end_lineno", node.lineno)
            if node.lineno <= line <= end:
                candidates.append(node)
    if not candidates:
        return None
    return min(candidates, key=lambda node: getattr(node, "end_lineno", node.lineno) - node.lineno)


def _target_names(node) -> list[str]:
    if node is None:
        return []
    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
    names = []
    for target in targets:
        if isinstance(target, ast.Name):
            names.append(target.id)
        elif isinstance(target, (ast.Tuple, ast.List)):
            names.extend(item.id for item in target.elts if isinstance(item, ast.Name))
    return names


def _assignment_names(path: str, line: int) -> list[str]:
    tree = _tree(path)
    if tree is None:
        return []
    return _target_names(_assignment_at(tree, line))


def _names_in(node) -> set[str]:
    if node is None:
        return set()
    names = set()
    for child in ast.walk(node):
        if isinstance(child, ast.Name):
            names.add(child.id)
    return names


def _literal_on_the_left(node) -> bool:
    if isinstance(node, ast.Constant):
        return True
    return (
        isinstance(node, ast.UnaryOp)
        and isinstance(node.op, ast.USub)
        and isinstance(node.operand, ast.Constant)
    )


def _as_written_equation(path: str, line: int, equation: Expr) -> Expr:
    """Undo Python's reflection of ``1 == expr`` into ``expr == 1``.

    The chapter writes arithmetic goals with the constant first.  Python sends
    ``1 == expr`` to ``Expr.__eq__`` as ``expr == 1``.  Equality is symmetric,
    but keeping the source order makes the goal, the certificate and any
    failure report read like the page.
    """
    tree = _tree(path)
    if tree is None or not isinstance(equation, Eq):
        return equation
    calls = [
        node
        for node in ast.walk(tree)
        if isinstance(node, ast.Call)
        and node.lineno <= line <= getattr(node, "end_lineno", node.lineno)
    ]
    for call in sorted(calls, key=lambda node: getattr(node, "end_lineno", node.lineno) - node.lineno):
        if not isinstance(call.func, ast.Attribute) or call.func.attr != "ring":
            continue
        if not call.args:
            continue
        first = call.args[0]
        if (
            isinstance(first, ast.Compare)
            and len(first.ops) == 1
            and isinstance(first.ops[0], ast.Eq)
            and _literal_on_the_left(first.left)
        ):
            return Eq(equation.right, equation.left)
        break
    return equation


def _related_assignments(path: str, line: int) -> tuple[dict, ...]:
    """Assignments named on the failing source line, before that line."""
    tree = _tree(path)
    if tree is None:
        return ()
    node = _assignment_at(tree, line)
    if node is None:
        return ()
    function = _enclosing_function(tree, line)
    if function is None:
        return ()
    wanted = _names_in(getattr(node, "value", node))
    found = []
    for candidate in ast.walk(function):
        if not isinstance(candidate, (ast.Assign, ast.AnnAssign)):
            continue
        if candidate.lineno >= line:
            continue
        for name in _target_names(candidate):
            if name in wanted:
                found.append(
                    {
                        "name": name,
                        "file": _absolute(path),
                        "line": candidate.lineno,
                        "source_line": _line_text(path, candidate.lineno),
                    }
                )
    return tuple(sorted(found, key=lambda item: (item["line"], item["name"])))


_AUTHORING_FILE = os.path.abspath(__file__)


def _caller_outside():
    """The author's frame, skipping this module's own helpers."""
    frame = inspect.currentframe().f_back
    while frame is not None:
        if os.path.abspath(frame.f_code.co_filename) != _AUTHORING_FILE:
            return frame
        frame = frame.f_back
    return None


def _return_location(fn) -> tuple[str, int, str]:
    path = _absolute(fn.__code__.co_filename)
    tree = _tree(path)
    if tree is not None:
        first = fn.__code__.co_firstlineno
        functions = [
            node
            for node in ast.walk(tree)
            if isinstance(node, ast.FunctionDef)
            and node.name == fn.__name__
            and node.lineno - 1 <= first <= getattr(node, "end_lineno", node.lineno)
        ]
        if functions:
            returns = [
                node
                for node in ast.walk(max(functions, key=lambda node: node.lineno))
                if isinstance(node, ast.Return)
            ]
            if returns:
                node = max(returns, key=lambda node: node.lineno)
                return path, node.lineno, _line_text(path, node.lineno)
    return path, first, _line_text(path, first)


def _location(frame) -> tuple[str, int, str]:
    if frame is None:
        return "<unknown>", 0, ""
    path = _absolute(frame.f_code.co_filename)
    line = frame.f_lineno
    return path, line, _line_text(path, line)


# ── Terms ────────────────────────────────────────────────────────────────────


def unfold(expr: Expr) -> Expr:
    """Unfold transparent definitions at the head of a proposition."""
    while isinstance(expr, App) and expr.symbol is not None:
        symbol = expr.symbol
        body = getattr(symbol, "body", None)
        params = getattr(symbol, "params", None)
        if body is None or params is None:
            break
        expr = substitute_symbols(
            body, {id(param): argument for param, argument in zip(params, expr.args)}
        )
    return expr


def _same(left: Expr, right: Expr) -> bool:
    return structural_eq(unfold(left), unfold(right))


def _flipped_equality(statement: Expr, expected: Expr) -> bool:
    left, right = unfold(statement), unfold(expected)
    return (
        isinstance(left, Eq)
        and isinstance(right, Eq)
        and structural_eq(left.left, right.right)
        and structural_eq(left.right, right.left)
    )


def _close_ring(ring: Ring, equation) -> ProofTerm:
    if equation.step is None:
        return Refl(equation.left)
    from logos.kernel import Block

    return Block(tuple(ring.steps), equation.step.index)


def _occurrence(expr: Expr, pattern: Expr):
    """Return the field path to the first structural occurrence, or None."""
    if structural_eq(expr, pattern):
        return ()
    if not hasattr(expr, "__dataclass_fields__"):
        return None
    for name in expr.__dataclass_fields__:
        value = getattr(expr, name)
        if isinstance(value, Expr):
            path = _occurrence(value, pattern)
            if path is not None:
                return (name, *path)
    return None


def _replace_at(expr: Expr, path: tuple[str, ...], value: Expr) -> Expr:
    if not path:
        return value
    head, *rest = path
    child = getattr(expr, head)
    fields = {
        name: (getattr(expr, name) if name != head else _replace_at(child, tuple(rest), value))
        for name in expr.__dataclass_fields__
    }
    return type(expr)(**fields)


def _ring_attempt(equation: Eq) -> ProofTerm | None:
    try:
        return Ring().prove(equation)
    except (TacticFailed, RecursionError):
        return None


def _ring_rules(facts: tuple["Fact", ...]):
    rules = []
    for fact in facts:
        statement = unfold(fact.statement)
        if not isinstance(statement, Eq):
            continue
        rules.append((fact, statement.left, statement.right, fact.proof))
    return rules


def _rewrite_proof(term: Expr, target: Expr, rules) -> ProofTerm | None:
    """Connect ``term`` to ``target`` with ring steps and opened equations."""
    if not rules:
        return _ring_attempt(Eq(term, target))
    hole = Var("__logos_ring_hole", int)
    started = {_key(term): term}
    queue = deque([(term, [])])
    limit = 400
    while queue and len(started) < limit:
        current, steps = queue.popleft()
        closing = _ring_attempt(Eq(current, target))
        if closing is not None:
            proof = closing
            for fact, context, oriented in reversed(steps):
                proof = Trans(Congr(hole, context, oriented), proof)
            return proof
        if len(steps) >= 6:
            continue
        for fact, left, right, evidence in rules:
            for pattern, replacement, oriented in (
                (left, right, evidence),
                (right, left, Symm(evidence)),
            ):
                path = _occurrence(current, pattern)
                if path is None:
                    continue
                rewritten = _replace_at(current, path, replacement)
                context = _replace_at(current, path, hole)
                key = _key(rewritten)
                if key in started:
                    continue
                started[key] = rewritten
                queue.append((rewritten, [*steps, (fact, context, oriented)]))
    return None


def _key(expr: Expr):
    # A structural key that keeps identical terms together without using
    # Python's id, so two independently built but equal terms merge.
    match expr:
        case Var(name, type_):
            return ("var", name, _sort_name(type_))
        case Lit(value):
            return ("lit", value)
        case Add(left, right) | Sub(left, right) | Mul(left, right) | Eq(left, right):
            return (type(expr).__name__, _key(left), _key(right))
        case Neg(operand) | Not(operand):
            return (type(expr).__name__, _key(operand))
        case And(left, right) | Or(left, right) | Implies(left, right):
            return (type(expr).__name__, _key(left), _key(right))
        case App(name, args, _):
            return ("app", name, tuple(_key(arg) for arg in args))
        case _:
            return ("other", repr(expr))


def _ring_using(goal: Expr, facts: tuple["Fact", ...], context: "ProofContext") -> ProofTerm:
    equation = unfold(goal)
    if not isinstance(equation, Eq):
        raise context.failure(
            "ring_goal",
            "ring expects an equality",
            goal=goal,
        )
    direct = _ring_attempt(equation)
    if direct is not None:
        return direct

    rules = _ring_rules(facts)
    for source, target in (
        (equation.left, equation.right),
        (equation.right, equation.left),
    ):
        # First try the raw terms, then their polynomial normal forms.  The
        # second form is what connects a product such as d * (j - k) to the
        # two equations a = d*k and a+1 = d*j.
        candidates = [(source, None)]
        try:
            ring = Ring()
            normal = ring.normalize(source)
            candidates.append((normal.right, _close_ring(ring, normal)))
        except (TacticFailed, RecursionError):
            pass
        for candidate, normal_proof in candidates:
            forward = _rewrite_proof(candidate, target, rules)
            if forward is None:
                continue
            proof = forward if normal_proof is None else Trans(normal_proof, forward)
            return proof if source is equation.left else Symm(proof)

    raise context.failure(
        "ring_goal_unreachable",
        "ring could not connect the goal to the equations opened with 'using'",
        goal=goal,
        extra={"using": [_detail_fact(fact) for fact in facts]},
    )


# ── Proof context ────────────────────────────────────────────────────────────


@dataclass
class _Frame:
    kind: str
    name: str
    statement: Expr | None = None
    proof: ProofTerm | None = None
    variable: Var | None = None
    fact: "Fact | None" = None


@dataclass
class Fact:
    """A proposition and checked evidence for it, plus where it was written."""

    context: "ProofContext"
    statement: Expr
    proof: ProofTerm
    label: str = ""
    file: str | None = None
    line: int | None = None
    source_line: str = ""

    def left(self) -> "Fact":
        statement = unfold(self.statement)
        if not isinstance(statement, And):
            raise self.context.failure(
                "projection",
                "left() needs a conjunction",
                got=self.statement,
            )
        return Fact(
            self.context,
            statement.left,
            AndElimL(self.proof),
            label=f"{self.label}.left" if self.label else "left",
            file=self.file,
            line=self.line,
            source_line=self.source_line,
        )

    def right(self) -> "Fact":
        statement = unfold(self.statement)
        if not isinstance(statement, And):
            raise self.context.failure(
                "projection",
                "right() needs a conjunction",
                got=self.statement,
            )
        return Fact(
            self.context,
            statement.right,
            AndElimR(self.proof),
            label=f"{self.label}.right" if self.label else "right",
            file=self.file,
            line=self.line,
            source_line=self.source_line,
        )

    def __repr__(self):
        return f"Fact({format_expr(self.statement)!r})"


class ProofContext:
    """The ``p`` argument of a book-style proof function."""

    def __init__(self, statement: Expr, binders: tuple[Var, ...], theorem: str, fn=None):
        self.theorem = theorem
        self.fn = fn
        body = statement
        for _ in binders:
            if not isinstance(body, ForallNode):
                raise TypeError(
                    f"Theorem '{theorem}': statement has fewer forall binders than its parameters"
                )
            body = body.body
        self.initial_goal = body
        self.goal: Expr | None = body
        self.binders = tuple(binders)
        self.frames: list[_Frame] = []
        self.hypotheses: dict[str, Expr] = {}
        self.opened: list[Fact] = []
        self.used_names = {binder.name for binder in binders}
        self.allowed = free_symbol_ids(body) | {id(binder) for binder in binders}

    # -- diagnostics ---------------------------------------------------------

    def failure(self, kind: str, message: str, **kwargs) -> AuthoringFailure:
        frame = _caller_outside()
        file, line, source_line = _location(frame)
        kwargs.setdefault("file", file)
        kwargs.setdefault("line", line)
        kwargs.setdefault("source_line", source_line)
        kwargs.setdefault("theorem", self.theorem)
        if kwargs.get("goal") is None and self.goal is not None:
            kwargs["goal"] = self.goal
        kwargs.setdefault(
            "hypotheses", tuple(self.hypotheses.items())
        )
        kwargs.setdefault("opened", tuple(self.opened))
        file = kwargs.get("file") or file
        line = kwargs.get("line") or line
        if file and line:
            kwargs.setdefault("related", _related_assignments(file, line))
        return AuthoringFailure(kind, message, **kwargs)

    def _fresh(self, base: str) -> str:
        base = "".join(ch if ch.isalnum() or ch == "_" else "_" for ch in base) or "h"
        if base[0].isdigit():
            base = f"h_{base}"
        candidate = base
        index = 1
        while candidate in self.used_names:
            candidate = f"{base}{index}"
            index += 1
        self.used_names.add(candidate)
        return candidate

    # -- operations ----------------------------------------------------------

    def assume(self, proposition: Expr) -> Fact:
        if self.goal is None:
            raise self.failure("assume_after_close", "there is no goal left to assume")
        goal = unfold(self.goal)
        if not isinstance(goal, Implies) or not _same(goal.antecedent, proposition):
            raise self.failure(
                "assume_mismatch",
                "assume does not match the antecedent of the current goal",
                expected=goal.antecedent if isinstance(goal, Implies) else goal,
                got=proposition,
            )
        file, line, source_line = _location(_caller_outside())
        target = _assignment_names(file, line)
        label = target[0] if target else "assumed"
        name = self._fresh(label)
        self.hypotheses[name] = proposition
        self.frames.append(_Frame("assume", name, statement=proposition))
        self.goal = goal.consequent
        fact = Fact(
            self,
            proposition,
            HypRef(name),
            label=label,
            file=file,
            line=line,
            source_line=source_line,
        )
        return fact

    def obtain(self, existential: Fact) -> tuple[Var, Fact]:
        statement = unfold(existential.statement)
        if not isinstance(statement, ExistsNode):
            raise self.failure(
                "obtain_mismatch",
                "obtain needs an existential fact",
                expected="exists x. P(x)",
                got=existential.statement,
            )
        file, line, source_line = _location(_caller_outside())
        names = _assignment_names(file, line)
        witness_name = names[0] if len(names) >= 1 else statement.var.name
        fact_name = names[1] if len(names) >= 2 else "obtained"
        variable = Var(self._fresh(witness_name), statement.var.type)
        name = self._fresh(fact_name)
        hypothesis = substitute_symbols(statement.body, {id(statement.var): variable})
        self.hypotheses[name] = hypothesis
        self.frames.append(
            _Frame(
                "exists",
                name,
                proof=existential.proof,
                variable=variable,
                fact=existential,
            )
        )
        self.allowed.add(id(variable))
        fact = Fact(
            self,
            hypothesis,
            HypRef(name),
            label=fact_name,
            file=file,
            line=line,
            source_line=source_line,
        )
        self.opened.append(fact)
        return variable, fact

    def ring(self, equation: Expr, *, using=()) -> Fact:
        facts = tuple(using)
        for fact in facts:
            if not isinstance(fact, Fact):
                raise TypeError("ring(using=...) expects facts returned by obtain/assume")
        file, line, source_line = _location(_caller_outside())
        equation = _as_written_equation(file, line, equation)
        proof = _ring_using(equation, facts, self)
        target = _assignment_names(file, line)
        return Fact(
            self,
            equation,
            proof,
            label=target[0] if target else "equation",
            file=file,
            line=line,
            source_line=source_line,
        )

    def witness(self, value: Expr, evidence: Fact | ProofTerm) -> ProofTerm:
        if self.goal is None:
            raise self.failure("witness_after_close", "there is no goal left to witness")
        goal = unfold(self.goal)
        if not isinstance(goal, ExistsNode):
            raise self.failure(
                "witness_goal",
                "witness needs an existential goal",
                goal=self.goal,
            )
        unbound = free_symbol_ids(value) - self.allowed
        if unbound:
            names = sorted(
                {
                    getattr(expr, "name", "?")
                    for expr in _walk_expr(value)
                    if id(expr) in unbound and isinstance(expr, Var)
                }
            )
            raise self.failure(
                "witness_escape",
                "the witness mentions symbols that are not in scope",
                expected=goal,
                got=value,
                extra={"unbound": names},
            )
        expected = substitute_symbols(goal.body, {id(goal.var): value})
        if isinstance(evidence, Fact):
            statement = evidence.statement
            proof = evidence.proof
            if not _same(statement, expected):
                # Python reflects `1 == expr` into `Expr.__eq__(expr, 1)`, so
                # a perfectly good equality can arrive with its sides swapped.
                # Equality is symmetric, and the proof term must follow it.
                if _flipped_equality(statement, expected):
                    proof = Symm(proof)
                else:
                    raise self.failure(
                        "witness_mismatch",
                        "the evidence does not prove the instantiated existential predicate",
                        expected=expected,
                        got=statement,
                    )
        elif isinstance(evidence, ProofTerm):
            proof = evidence
        else:
            raise TypeError("witness(value, evidence) expects a Fact or proof term")
        self.goal = goal
        return ExistsIntro(value, proof, goal)

    # -- finishing -----------------------------------------------------------

    def finish(self, result) -> ProofTerm:
        if isinstance(result, Fact):
            if self.goal is not None and not _same(self.goal, result.statement):
                if _flipped_equality(result.statement, self.goal):
                    result = Fact(
                        result.context,
                        self.goal,
                        Symm(result.proof),
                        label=result.label,
                        file=result.file,
                        line=result.line,
                        source_line=result.source_line,
                    )
                else:
                    file, line, source_line = (
                        _return_location(self.fn) if self.fn is not None else (None, None, "")
                    )
                    raise self.failure(
                        "proof_mismatch",
                        "the returned evidence does not prove the current goal",
                        expected=self.goal,
                        got=result.statement,
                        file=file,
                        line=line,
                        source_line=source_line,
                    )
            proof = result.proof
        elif isinstance(result, ProofTerm):
            proof = result
        else:
            raise self.failure(
                "proof_result",
                "an authoring proof must return a Fact or a proof term",
                got=type(result).__name__,
            )
        for frame in reversed(self.frames):
            if frame.kind == "assume":
                proof = ImpliesIntro(frame.statement, frame.name, proof)
            else:
                proof = ExistsElim(frame.proof, frame.variable, frame.name, proof)
        for binder in reversed(self.binders):
            proof = ForallIntro(binder, proof)
        return proof


def _walk_expr(expr: Expr):
    yield expr
    if not hasattr(expr, "__dataclass_fields__"):
        return
    for name in expr.__dataclass_fields__:
        value = getattr(expr, name)
        if isinstance(value, Expr):
            yield from _walk_expr(value)


def binders_and_body(statement: Expr) -> tuple[tuple[Var, ...], Expr]:
    binders = []
    body = statement
    while isinstance(body, ForallNode):
        binders.append(body.var)
        body = body.body
    return tuple(binders), body


def authoring_signature_matches(theorem, fn) -> bool:
    try:
        params = list(inspect.signature(fn).parameters)
    except (TypeError, ValueError):
        return False
    binders, _ = binders_and_body(theorem.statement)
    return params == ["p", *(binder.name for binder in binders)]


def authoring_tactic(theorem, fn):
    """Wrap a book-style proof function as a tactic for the existing runner."""

    def tactic(goal):
        binders, _ = binders_and_body(goal.statement)
        context = ProofContext(goal.statement, binders, theorem.name, fn=fn)
        try:
            result = fn(context, *binders)
            return context.finish(result)
        except AuthoringFailure as failure:
            if failure.theorem is None:
                failure.theorem = theorem.name
            raise
        except Exception:
            # Keep accidental Python errors inside the authoring contract so a
            # reader still sees the source line and the local state.
            raise

    return tactic
