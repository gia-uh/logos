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
    Add, And, App, Div, Eq, ExistsNode, Expr, ForallNode, Implies, Le, Len, Lit,
    Lt, Mod, Mul, Neg, Not, Nth, Or, Pow, Sorted, Sub, Var,
)
from logos.helpers import free_symbol_ids, normalize_order, structural_eq, substitute_symbols
from logos.kernel import (
    AndElimL, AndElimR, AndIntro, AxiomRef, CaseAnalysis, Congr, CoreLaw,
    EqSubst, ExFalso, ExistsElim, ExistsIntro, ForallElim, ForallIntro, Have,
    HypRef, ImpliesElim, ImpliesIntro, Induction, Least, Linear, NotElim,
    NotIntro, ProofTerm, RecursorBase, RecursorStep, Refl, Symm, TheoremRef,
    Trans, Note,
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
        case Div(left, right):
            text = f"{_render(left, _PREC['mul'])} // {_render(right, _PREC['mul'] + 1)}"
            return f"({text})" if _PREC["mul"] < parent else text
        case Mod(left, right):
            text = f"{_render(left, _PREC['mul'])} % {_render(right, _PREC['mul'] + 1)}"
            return f"({text})" if _PREC["mul"] < parent else text
        case Pow(base, exponent):
            text = f"{_render(base, _PREC['unary'])} ** {_render(exponent, _PREC['unary'])}"
            return f"({text})" if _PREC["unary"] < parent else text
        case Len(seq):
            return f"len({_render(seq)})"
        case Nth(seq, index):
            return f"{_render(seq, _PREC['atom'])}[{_render(index)}]"
        case Sorted(seq):
            return f"sorted({_render(seq)})"
        case Neg(operand):
            text = f"-{_render(operand, _PREC['unary'])}"
            return f"({text})" if _PREC["unary"] < parent else text
        case Eq(left, right):
            text = f"{_render(left, _PREC['eq'] + 1)} = {_render(right, _PREC['eq'] + 1)}"
            return f"({text})" if _PREC["eq"] < parent else text
        case Lt(left, right):
            text = f"{_render(left, _PREC['eq'] + 1)} < {_render(right, _PREC['eq'] + 1)}"
            return f"({text})" if _PREC["eq"] < parent else text
        case Le(left, right):
            text = f"{_render(left, _PREC['eq'] + 1)} <= {_render(right, _PREC['eq'] + 1)}"
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


def _return_location(fn) -> tuple[str | None, int | None, str]:
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
    # Generated proof functions may have no source file. The function's
    # first line is not a return site.
    return None, None, ""


def _location(frame) -> tuple[str, int, str]:
    if frame is None:
        return "<unknown>", 0, ""
    path = _absolute(frame.f_code.co_filename)
    line = frame.f_lineno
    return path, line, _line_text(path, line)


# ── Terms ────────────────────────────────────────────────────────────────────


def unfold(expr: Expr) -> Expr:
    """Unfold transparent definitions throughout a proposition."""
    while isinstance(expr, App) and expr.symbol is not None:
        symbol = expr.symbol
        body = getattr(symbol, "body", None)
        params = getattr(symbol, "params", None)
        if body is None or params is None:
            break
        expr = substitute_symbols(
            body, {id(param): argument for param, argument in zip(params, expr.args)}
        )
    if not hasattr(expr, "__dataclass_fields__") or isinstance(expr, (Var, Lit)):
        return expr
    values = {}
    for name in expr.__dataclass_fields__:
        value = getattr(expr, name)
        if isinstance(value, Expr):
            value = unfold(value)
        elif isinstance(value, list):
            value = [
                tuple(unfold(part) if isinstance(part, Expr) else part for part in item)
                if isinstance(item, tuple)
                else unfold(item) if isinstance(item, Expr)
                else item
                for item in value
            ]
        values[name] = value
    return type(expr)(**values)


def _sort_of(expr: Expr) -> type:
    if isinstance(expr, Var):
        return expr.type
    if isinstance(expr, Lit):
        return type(expr.value)
    if isinstance(expr, App):
        symbol = expr.symbol
        return getattr(symbol, "result_type", None) or int
    if isinstance(expr, (And, Or, Not, Implies, Eq, Lt, Le, ExistsNode, ForallNode)):
        return bool
    return int


def _same(left: Expr, right: Expr) -> bool:
    return structural_eq(
        normalize_order(unfold(left)),
        normalize_order(unfold(right)),
    )


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
        elif isinstance(value, (list, tuple)):
            for index, item in enumerate(value):
                if isinstance(item, Expr):
                    path = _occurrence(item, pattern)
                    if path is not None:
                        return (name, index, *path)
    return None


def _replace_at(expr: Expr, path: tuple, value: Expr) -> Expr:
    if not path:
        return value
    head, *rest = path
    if isinstance(head, int):
        items = list(expr)
        items[head] = _replace_at(items[head], tuple(rest), value)
        return type(expr)(items) if isinstance(expr, list) else tuple(items)
    child = getattr(expr, head)
    fields = {}
    for name in expr.__dataclass_fields__:
        current = getattr(expr, name)
        if name == head:
            fields[name] = _replace_at(child, tuple(rest), value)
        else:
            fields[name] = current
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
        fact = Fact(
            self.context,
            statement.left,
            AndElimL(self.proof),
            label=f"{self.label}.left" if self.label else "left",
            file=self.file,
            line=self.line,
            source_line=self.source_line,
        )
        self.context.last_fact = fact
        return fact

    def right(self) -> "Fact":
        statement = unfold(self.statement)
        if not isinstance(statement, And):
            raise self.context.failure(
                "projection",
                "right() needs a conjunction",
                got=self.statement,
            )
        fact = Fact(
            self.context,
            statement.right,
            AndElimR(self.proof),
            label=f"{self.label}.right" if self.label else "right",
            file=self.file,
            line=self.line,
            source_line=self.source_line,
        )
        self.context.last_fact = fact
        return fact

    def __repr__(self):
        return f"Fact({format_expr(self.statement)!r})"


def _wrap_frames(proof: ProofTerm, frames) -> ProofTerm:
    """Close the local frames that a branch actually introduced."""
    for frame in reversed(tuple(frames)):
        if frame.kind == "assume":
            proof = ImpliesIntro(frame.statement, frame.name, proof)
        elif frame.kind == "forall":
            proof = ForallIntro(frame.variable, proof)
        else:
            proof = ExistsElim(frame.proof, frame.variable, frame.name, proof)
    return proof


def _fraction_text(value) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


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
        self.last_fact: Fact | None = None

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
        file = kwargs["file"]
        line = kwargs["line"]
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

    def note(self, text: str) -> None:
        """Attach authored commentary after the most recently derived fact.

        The note travels inside the checked evidence as an annotation. It does
        not create a step, change the goal or count as evidence.
        """
        if not isinstance(text, str) or not text.strip():
            raise self.failure("note_text", "p.note needs a nonempty string")
        if self.last_fact is None:
            raise self.failure(
                "note_position",
                "p.note needs an earlier proof step in this scope",
            )
        self.last_fact.proof = Note(text, self.last_fact.proof)

    # -- operations ----------------------------------------------------------

    def assume(self, proposition: Expr) -> Fact:
        if self.goal is None:
            raise self.failure("assume_after_close", "there is no goal left to assume")
        proposition = normalize_order(proposition)
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
        self.last_fact = fact
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
        hypothesis = normalize_order(
            substitute_symbols(statement.body, {id(statement.var): variable})
        )
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
        self.last_fact = fact
        return variable, fact

    def _fact(self, statement: Expr, proof: ProofTerm, label: str | None = None) -> Fact:
        file, line, source_line = _location(_caller_outside())
        if label is None:
            names = _assignment_names(file, line)
            label = names[0] if names else "fact"
        fact = Fact(
            self,
            statement,
            proof,
            label=label,
            file=file,
            line=line,
            source_line=source_line,
        )
        self.last_fact = fact
        return fact

    def _match_fact(self, expected: Expr, fact: Fact) -> ProofTerm:
        """Use a fact as evidence for ``expected``, flipping equalities once."""
        if _same(fact.statement, expected):
            return fact.proof
        if _flipped_equality(fact.statement, expected):
            return Symm(fact.proof)
        file, line, source_line = _location(_caller_outside())
        raise self.failure(
            "evidence_mismatch",
            "the evidence does not prove the expected statement",
            expected=expected,
            got=fact.statement,
            file=file,
            line=line,
            source_line=source_line,
        )

    # -- general evidence-producing operations ---------------------------------

    def apply(self, lemma, *arguments) -> Fact:
        """Instantiate a checked theorem (or local implication fact) step by step.

        An expression argument instantiates a ``forall``; a ``Fact``
        discharges an implication.  Nothing is closed behind the reader's
        back: the returned fact carries the remaining statement.
        """
        from logos.theorem import Axiom as AuthorAxiom, Theorem

        if isinstance(lemma, Theorem):
            proof: ProofTerm = TheoremRef(lemma)
            statement = lemma.statement
            name = lemma.name
        elif isinstance(lemma, AuthorAxiom):
            proof = AxiomRef(lemma)
            statement = lemma.statement
            name = lemma.name
        elif isinstance(lemma, Fact):
            proof = lemma.proof
            statement = lemma.statement
            name = lemma.label
        else:
            raise self.failure(
                "apply_kind",
                "apply expects a theorem, axiom or local fact",
                got=type(lemma).__name__,
            )
        file, line, source_line = _location(_caller_outside())
        for index, argument in enumerate(arguments):
            shape = unfold(statement)
            if isinstance(argument, Fact):
                if not isinstance(shape, Implies):
                    raise self.failure(
                        "apply_not_implication",
                        "apply received a fact but no implication remains",
                        expected=shape,
                        got=argument.statement,
                        extra={"lemma": name, "argument": index},
                        file=file,
                        line=line,
                        source_line=source_line,
                    )
                try:
                    premise = self._match_fact(shape.antecedent, argument)
                except AuthoringFailure as error:
                    raise self.failure(
                        "apply_premise_mismatch",
                        f"the fact does not prove the antecedent needed by {name}",
                        expected=shape.antecedent,
                        got=argument.statement,
                        extra={"lemma": name, "argument": index},
                        file=file,
                        line=line,
                        source_line=source_line,
                    ) from error
                proof = ImpliesElim(proof, premise)
                statement = shape.consequent
                continue
            if isinstance(argument, ProofTerm):
                if not isinstance(shape, Implies):
                    raise self.failure(
                        "apply_not_implication",
                        "apply received a proof term but no implication remains",
                        expected=shape,
                        got="proof term",
                        extra={"lemma": name, "argument": index},
                        file=file,
                        line=line,
                        source_line=source_line,
                    )
                proof = ImpliesElim(proof, argument)
                statement = shape.consequent
                continue
            if not isinstance(shape, ForallNode):
                raise self.failure(
                    "apply_not_forall",
                    "apply received a term but no universal binder remains",
                    expected=shape,
                    got=argument,
                    extra={"lemma": name, "argument": index},
                    file=file,
                    line=line,
                    source_line=source_line,
                )
            term = argument if isinstance(argument, Expr) else Lit(argument)
            unbound = free_symbol_ids(term) - self.allowed
            if unbound:
                raise self.failure(
                    "apply_escape",
                    "the argument mentions symbols that are not in scope",
                    expected=shape,
                    got=term,
                    extra={"lemma": name, "argument": index, "unbound": sorted(
                        getattr(item, "name", "?")
                        for item in _walk_expr(term)
                        if id(item) in unbound and isinstance(item, Var)
                    )},
                    file=file,
                    line=line,
                    source_line=source_line,
                )
            proof = ForallElim(proof, term)
            statement = substitute_symbols(shape.body, {id(shape.var): term})
        return self._fact(statement, proof)

    def and_intro(self, left: Fact, right: Fact) -> Fact:
        if not isinstance(left, Fact) or not isinstance(right, Fact):
            raise TypeError("and_intro expects two facts")
        statement = And(left.statement, right.statement)
        return self._fact(statement, AndIntro(left.proof, right.proof))

    def exists(self, goal: Expr, value: Expr, evidence: Fact) -> Fact:
        """Package a witness as evidence for an existential statement."""
        goal = normalize_order(goal)
        shape = unfold(goal)
        if not isinstance(shape, ExistsNode):
            raise self.failure(
                "exists_goal",
                "exists expects an existential statement",
                expected="exists x. P(x)",
                got=goal,
            )
        if not isinstance(value, Expr):
            value = Lit(value)
        unbound = free_symbol_ids(value) - self.allowed
        if unbound:
            raise self.failure(
                "witness_escape",
                "the witness mentions symbols that are not in scope",
                expected=shape,
                got=value,
                extra={"unbound": sorted(
                    getattr(item, "name", "?")
                    for item in _walk_expr(value)
                    if id(item) in unbound and isinstance(item, Var)
                )},
            )
        expected = substitute_symbols(shape.body, {id(shape.var): value})
        proof = self._match_fact(expected, evidence)
        return self._fact(goal, ExistsIntro(value, proof, shape))

    def subst(self, fact: Fact, equality: Fact) -> Fact:
        """Replace one side of an equality throughout a fact."""
        equality_statement = unfold(equality.statement)
        if not isinstance(equality_statement, Eq):
            raise self.failure(
                "subst_equality",
                "subst needs an equality",
                expected="a = b",
                got=equality.statement,
            )
        path = _occurrence(fact.statement, equality_statement.left)
        if path is None:
            raise self.failure(
                "subst_occurrence",
                "the equality's left side does not occur in the fact",
                expected=equality_statement.left,
                got=fact.statement,
            )
        variable = Var(self._fresh("target"), _sort_of(equality_statement.left))
        template = _replace_at(fact.statement, path, variable)
        proof = EqSubst(equality.proof, variable, template, fact.proof)
        statement = _replace_at(fact.statement, path, equality_statement.right)
        return self._fact(statement, proof)

    def refl(self, expression: Expr) -> Fact:
        if not isinstance(expression, Expr):
            expression = Lit(expression)
        return self._fact(Eq(expression, expression), Refl(expression))

    def symm(self, fact: Fact) -> Fact:
        statement = unfold(fact.statement)
        if not isinstance(statement, Eq):
            raise self.failure(
                "symm_goal",
                "symm expects an equality",
                goal=fact.statement,
            )
        return self._fact(Eq(statement.right, statement.left), Symm(fact.proof))

    def trans(self, left: Fact, right: Fact) -> Fact:
        first = unfold(left.statement)
        second = unfold(right.statement)
        if not isinstance(first, Eq) or not isinstance(second, Eq):
            raise self.failure(
                "trans_goal",
                "trans expects two equalities",
                expected="a = b, b = c",
                got=left.statement,
            )
        if not _same(first.right, second.left):
            raise self.failure(
                "trans_middle",
                "the middle terms of the equalities do not match",
                expected=first.right,
                got=second.left,
            )
        return self._fact(Eq(first.left, second.right), Trans(left.proof, right.proof))

    def not_elim(self, negation: Fact, premise: Fact) -> Fact:
        shape = unfold(negation.statement)
        if not isinstance(shape, Not):
            raise self.failure(
                "not_elim_goal",
                "not_elim needs a negated fact",
                expected="~A",
                got=negation.statement,
            )
        return self._fact(
            Lit(False),
            NotElim(negation.proof, self._match_fact(shape.operand, premise)),
        )

    def ex_falso(self, falsehood: Fact) -> Fact:
        if self.goal is None:
            raise self.failure("ex_falso_after_close", "there is no goal left")
        return self._fact(self.goal, ExFalso(falsehood.proof, self.goal))

    def not_lt_of_lt(self, low: Expr, high: Expr, fact: Fact) -> Fact:
        """From ``low < high`` derive ``~(high < low)`` without a new axiom."""
        low = low if isinstance(low, Expr) else Lit(low)
        high = high if isinstance(high, Expr) else Lit(high)
        shape = unfold(fact.statement)
        if not isinstance(shape, Lt) or not _same(shape.left, low) or not _same(shape.right, high):
            raise self.failure(
                "not_lt_wrong_fact",
                "not_lt_of_lt needs the inequality low < high",
                expected=Lt(low, high),
                got=fact.statement,
            )
        name = self._fresh("back")
        inner = ImpliesElim(
            ImpliesElim(CoreLaw("lt_trans", (low, high, low)), fact.proof),
            HypRef(name),
        )
        body = NotElim(CoreLaw("lt_irrefl", (low,)), inner)
        proof = NotIntro(ImpliesIntro(Lt(high, low), name, body))
        return self._fact(Not(Lt(high, low)), proof)

    def order(self, law: str, *args, using=()) -> Fact:
        """Cite a core order law with explicit integer arguments and premises."""
        from logos.core_laws import law_statement
        from logos.order import order_law, split_implications

        args = tuple(arg if isinstance(arg, Expr) else Lit(arg) for arg in args)
        try:
            full = order_law(law, args)
        except ValueError:
            full = law_statement(law, tuple(args))
        premises, conclusion = split_implications(normalize_order(unfold(full)))
        available = list(using)
        used = []
        for premise in premises:
            match = None
            for fact in available:
                try:
                    self._match_fact(premise, fact)
                except AuthoringFailure:
                    continue
                match = fact
                break
            if match is None:
                for name, statement in self.hypotheses.items():
                    candidate = Fact(self, statement, HypRef(name), label=name)
                    try:
                        self._match_fact(premise, candidate)
                    except AuthoringFailure:
                        continue
                    match = candidate
                    break
            if match is None:
                raise self.failure(
                    "order_premise_missing",
                    f"the {law} law needs a premise that is not in scope",
                    expected=premise,
                    goal=conclusion,
                    extra={"law": law},
                )
            used.append(match)
        proof: ProofTerm = CoreLaw(law, tuple(args))
        for fact in used:
            proof = ImpliesElim(proof, fact.proof)
        return self._fact(conclusion, proof)

    def linear(self, goal: Expr, *, using=()) -> Fact:
        """Prove a linear inequality from named facts with a checked certificate."""
        from logos.proofs import farkas

        if not isinstance(goal, Expr):
            goal = Lit(goal)
        goal = normalize_order(goal)
        facts = list(using)
        base = [
            (name, normalize_order(statement))
            for name, statement in self.hypotheses.items()
        ]
        wrapped = []
        for fact in facts:
            name = self._fresh(fact.label or "fact")
            base.append((name, normalize_order(fact.statement)))
            wrapped.append((name, fact))
        labels = farkas(unfold(goal), base)
        if labels is None:
            raise self.failure(
                "linear_goal_unreachable",
                "linear arithmetic could not derive the goal from these facts",
                goal=goal,
                extra={"using": [_detail_fact(fact) for fact in facts]},
            )
        proof: ProofTerm = Linear(
            unfold(goal),
            tuple((name, _fraction_text(value)) for name, value in labels.items()),
        )
        for name, fact in reversed(wrapped):
            proof = Have(name, fact.statement, fact.proof, proof)
        return self._fact(goal, proof)

    def recursor_base(self, function) -> Fact:
        from logos.expr import App

        base = function.recursor[0]
        statement = Eq(function(Lit(0)), base)
        return self._fact(statement, RecursorBase(function))

    def recursor_step(self, function, argument: Expr, nonnegative: Fact) -> Fact:
        from logos.expr import App

        if not isinstance(argument, Expr):
            argument = Lit(argument)
        base, step_body, previous = function.recursor
        expected = Not(Lt(argument, Lit(0)))
        if not _same(expected, nonnegative.statement):
            raise self.failure(
                "recursor_nonnegative",
                "the recursive step needs a nonnegative argument",
                expected=expected,
                got=nonnegative.statement,
            )
        argument_var = function.params[0]
        value = function(argument)
        statement = Eq(
            function(argument + Lit(1)),
            substitute_symbols(
                step_body,
                {id(argument_var): argument, id(previous): value},
            ),
        )
        return self._fact(statement, RecursorStep(function, argument, nonnegative.proof))

    def rewrite(self, fact: Fact, equality: Fact) -> Fact:
        """Rewrite the second argument of a transparent ``divides`` fact."""
        statement = fact.statement
        equality_statement = unfold(equality.statement)
        if (
            not isinstance(statement, App)
            or statement.symbol is None
            or len(statement.args) != 2
            or not isinstance(equality_statement, Eq)
        ):
            raise self.failure(
                "rewrite_shape",
                "rewrite expects a divides fact and an equality",
                expected="divides(d, a), a = b",
                got=fact.statement,
            )
        variable = Var(self._fresh("target"), statement.args[1].type)
        template = statement.symbol(statement.args[0], variable)
        expected = substitute_symbols(template, {id(variable): equality_statement.left})
        proof = self._match_fact(expected, fact)
        new_statement = substitute_symbols(template, {id(variable): equality_statement.right})
        return self._fact(new_statement, EqSubst(equality.proof, variable, template, proof))

    def least(self, lower: Expr, nonempty: Fact) -> Fact:
        """Apply the least-element rule to a nonempty bounded predicate."""
        if not isinstance(lower, Expr):
            lower = Lit(lower)
        shape = unfold(normalize_order(nonempty.statement))
        if not isinstance(shape, ExistsNode) or not isinstance(unfold(shape.body), And):
            raise self.failure(
                "least_shape",
                "least needs an existential of a lower bound and a predicate",
                expected="exists m. ~(m < lower) & P(m)",
                got=nonempty.statement,
            )
        membership = unfold(shape.body)
        if not isinstance(unfold(membership.left), Not):
            raise self.failure(
                "least_lower",
                "least needs a nonnegativity conjunct",
                expected="~(m < lower) & P(m)",
                got=shape.body,
            )
        predicate = membership.right
        var = shape.var
        minimal_var = Var(self._fresh("smaller"), var.type)
        minimal = ForallNode(
            minimal_var,
            Implies(
                And(
                    Not(Lt(minimal_var, lower)),
                    Lt(minimal_var, var),
                ),
                Not(substitute_symbols(predicate, {id(var): minimal_var})),
            ),
        )
        statement = ExistsNode(var, And(membership, minimal))
        return self._fact(statement, Least(lower, var, predicate, nonempty.proof))

    def fix(self, name: str = "x") -> "_Fixed":
        return _Fixed(self, name)

    def negate(self, statement: Expr | None = None) -> "_Negation":
        return _Negation(self, statement)

    def cases(self, disjunction: Fact) -> "_Cases":
        return _Cases(self, disjunction)

    def contradict(self, proposition: Expr) -> "_Contradiction":
        return _Contradiction(self, proposition)

    def induction(self, variable: Var, lower=0, *, nonnegative: Fact | None = None) -> "_Induction":
        return _Induction(self, variable, lower, nonnegative)

    def ring(self, equation: Expr, *, using=()) -> Fact:
        facts = tuple(using)
        for fact in facts:
            if not isinstance(fact, Fact):
                raise TypeError("ring(using=...) expects facts returned by obtain/assume")
        file, line, source_line = _location(_caller_outside())
        equation = normalize_order(_as_written_equation(file, line, equation))
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
        if not isinstance(value, Expr):
            value = Lit(value)
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


class _Scope:
    """Temporary state for one branch of a proof, with its own frames."""

    def __init__(self, context: ProofContext, goal: Expr):
        self.context = context
        self.goal = goal
        self.proof: ProofTerm | None = None
        self._saved = None

    def _open(self, hypotheses=None):
        context = self.context
        self._saved = (
            context.goal, context.frames, context.hypotheses, context.allowed,
            context.opened, context.last_fact,
        )
        context.goal = self.goal
        context.frames = []
        if hypotheses is None:
            hypotheses = context.hypotheses
        context.hypotheses = dict(hypotheses)
        context.allowed = set(context.allowed)
        context.opened = list(context.opened)
        context.last_fact = None

    def _hypothesis(self, proposition: Expr, hint: str, *, frame: bool = True) -> Fact:
        context = self.context
        proposition = normalize_order(proposition)
        name = context._fresh(hint)
        if frame:
            context.frames.append(_Frame("assume", name, statement=proposition))
        context.hypotheses[name] = proposition
        return Fact(context, proposition, HypRef(name), label=hint)

    def finish(self, result) -> None:
        target = self.context.goal if self.context.goal is not None else self.goal
        if isinstance(result, Fact):
            proof = self.context._match_fact(target, result)
        elif isinstance(result, ProofTerm):
            proof = result
        else:
            raise self.context.failure(
                "proof_result",
                "a branch must return a Fact or a proof term",
                got=type(result).__name__,
            )
        self.proof = _wrap_frames(proof, self.context.frames)

    def close(self):
        context = self.context
        if self._saved is None:
            raise self.context.failure("scope_closed", "the branch was not opened")
        (
            context.goal, context.frames, context.hypotheses, context.allowed,
            context.opened, context.last_fact,
        ) = self._saved
        self._saved = None


class _Fixed(_Scope):
    """Introduce a universal variable from a ``forall`` goal."""

    def __init__(self, context: ProofContext, name: str):
        self.name = name
        self.statement = None
        self.variable = None
        super().__init__(context, Lit(False))

    def __enter__(self):
        shape = unfold(self.context.goal)
        if not isinstance(shape, ForallNode):
            raise self.context.failure(
                "fix_goal",
                "fix needs a universal goal",
                expected="forall x. P(x)",
                got=self.context.goal,
            )
        self.statement = self.context.goal
        self.variable = Var(self.context._fresh(self.name), shape.var.type)
        self.goal = substitute_symbols(shape.body, {id(shape.var): self.variable})
        self._open()
        self.context.frames.append(_Frame("forall", self.variable.name, variable=self.variable))
        self.context.allowed.add(id(self.variable))
        return self

    def __exit__(self, exc_type, exc, traceback):
        if exc_type is not None:
            self.close()
            return False
        if self.proof is None:
            self.close()
            raise self.context.failure(
                "fix_unfinished",
                "the forall branch was never finished with .finish(...)",
                goal=self.statement,
            )
        self.result = Fact(self.context, self.statement, self.proof, label=self.name)
        self.close()
        return False


class _Negation(_Scope):
    """Prove ``~A`` by assuming ``A`` and deriving false."""

    def __init__(self, context: ProofContext, statement: Expr | None = None):
        self.statement = statement
        self.assumption = None
        super().__init__(context, Lit(False))

    def __enter__(self):
        if self.statement is None:
            self.statement = self.context.goal
        self.statement = normalize_order(self.statement)
        shape = unfold(self.statement)
        if not isinstance(shape, Not):
            raise self.context.failure(
                "negate_goal",
                "negate needs a negated statement",
                expected="~A",
                got=self.statement,
            )
        self._open()
        self.assumption = self._hypothesis(shape.operand, "suppose")
        return self

    def __exit__(self, exc_type, exc, traceback):
        if exc_type is not None:
            self.close()
            return False
        if self.proof is None:
            self.close()
            raise self.context.failure(
                "negate_unfinished",
                "the negation was never finished with .finish(...)",
                goal=self.statement,
            )
        self.result = Fact(self.context, self.statement, NotIntro(self.proof), label="not")
        self.close()
        return False


class _CaseBranch(_Scope):
    def __init__(self, context: ProofContext, goal: Expr, proposition: Expr, name: str):
        self.proposition = proposition
        self.name = name
        self.assumption = None
        super().__init__(context, goal)

    def __enter__(self):
        self._open()
        self.proposition = normalize_order(self.proposition)
        self.context.hypotheses[self.name] = self.proposition
        self.assumption = Fact(
            self.context, self.proposition, HypRef(self.name), label=self.name
        )
        return self.assumption

    def __exit__(self, exc_type, exc, traceback):
        if exc_type is not None:
            self.close()
            return False
        if self.proof is None:
            self.close()
            raise self.context.failure(
                "case_unfinished",
                "this case was never finished with cases.finish(...)",
                goal=self.goal,
            )
        self.close()
        return False


class _Cases:
    """Case analysis on a disjunction, with one scope per branch."""

    def __init__(self, context: ProofContext, disjunction: Fact):
        shape = unfold(normalize_order(disjunction.statement))
        if not isinstance(shape, Or):
            raise context.failure(
                "cases_goal",
                "cases needs a disjunction",
                expected="A | B",
                got=disjunction.statement,
            )
        self.context = context
        self.disjunction = disjunction
        self.shape = shape
        self.case_name = context._fresh("case")
        self.goal = context.goal
        self.left_proof = None
        self.right_proof = None
        self._active = None
        self.result = None

    def left(self):
        branch = _CaseBranch(self.context, self.goal, self.shape.left, self.case_name)
        branch._owner = self
        return self._track(branch, "left")

    def right(self):
        branch = _CaseBranch(self.context, self.goal, self.shape.right, self.case_name)
        branch._owner = self
        return self._track(branch, "right")

    def _track(self, branch, side):
        class _Tracked:
            def __enter__(inner):
                self._active = branch
                value = branch.__enter__()
                inner.value = value
                return value

            def __exit__(inner, exc_type, exc, traceback):
                try:
                    return branch.__exit__(exc_type, exc, traceback)
                finally:
                    proof = branch.proof
                    if proof is not None:
                        if side == "left":
                            self.left_proof = proof
                        else:
                            self.right_proof = proof
                    self._active = None
        return _Tracked()

    def finish(self, result) -> None:
        if self._active is None:
            raise self.context.failure(
                "cases_outside",
                "cases.finish must be called inside a case branch",
                goal=self.goal,
            )
        self._active.finish(result)

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, traceback):
        if exc_type is not None:
            return False
        if self.left_proof is None or self.right_proof is None:
            raise self.context.failure(
                "cases_unfinished",
                "both branches of a case analysis need evidence",
                goal=self.goal,
            )
        proof = CaseAnalysis(
            self.disjunction.proof,
            self.case_name,
            self.left_proof,
            self.right_proof,
        )
        self.result = Fact(self.context, self.goal, proof, label="cases")
        return False


class _Contradiction(_Scope):
    """Prove a strict-order goal from the negation of that goal."""

    def __init__(self, context: ProofContext, proposition: Expr):
        proposition = normalize_order(proposition)
        shape = unfold(proposition)
        if not isinstance(shape, Lt):
            raise context.failure(
                "contradict_goal",
                "contradict needs a strict-order statement to prove",
                expected="a < b",
                got=proposition,
            )
        self.proposition = proposition
        self.assumption = None
        super().__init__(context, Lit(False))

    def __enter__(self):
        self._open()
        self.assumption = self._hypothesis(Not(self.proposition), "contrary")
        self.hypothesis = self.assumption
        return self

    def __exit__(self, exc_type, exc, traceback):
        if exc_type is not None:
            self.close()
            return False
        if self.proof is None:
            self.close()
            raise self.context.failure(
                "contradict_unfinished",
                "the contradiction was never finished with .finish(...)",
                goal=self.proposition,
            )
        not_not = NotIntro(self.proof)
        name = self.context._fresh("decided")
        proof = CaseAnalysis(
            CoreLaw("lt_decidable", (self.proposition.left, self.proposition.right)),
            name,
            HypRef(name),
            ExFalso(NotElim(not_not, HypRef(name)), self.proposition),
        )
        self.result = Fact(self.context, self.proposition, proof, label="contradiction")
        self.close()
        return False


class _InductionBase(_Scope):
    def __init__(self, context: ProofContext, goal: Expr):
        super().__init__(context, goal)

    def __enter__(self):
        self._open()
        return self

    def __exit__(self, exc_type, exc, traceback):
        if exc_type is not None:
            self.close()
            return False
        if self.proof is None:
            self.close()
            raise self.context.failure(
                "induction_base_unfinished",
                "the induction base was never finished with .finish(...)",
                goal=self.goal,
            )
        self.close()
        return False


class _InductionStep(_Scope):
    def __init__(self, context: ProofContext, goal: Expr, variable: Var, rule: "_Induction"):
        self.variable = variable
        self.rule = rule
        self.nonnegative = None
        self.hypothesis = None
        self.nonnegative_statement = Not(Lt(variable, rule.lower))
        self.hypothesis_statement = substitute_symbols(
            rule.predicate, {id(rule.indvar): variable}
        )
        super().__init__(context, goal)

    def __enter__(self):
        self._open(hypotheses=self.rule.hypotheses)
        self.context.allowed.add(id(self.variable))
        self.nonnegative = self._hypothesis(self.nonnegative_statement, "nonnegative")
        self.hypothesis = self._hypothesis(self.hypothesis_statement, "previous")
        return self

    def __exit__(self, exc_type, exc, traceback):
        if exc_type is not None:
            self.close()
            return False
        if self.proof is None:
            self.close()
            raise self.context.failure(
                "induction_step_unfinished",
                "the induction step was never finished with .finish(...)",
                goal=self.goal,
            )
        self.step_proof = ForallIntro(self.variable, self.proof)
        self.close()
        return False


class _Induction:
    """Ordinary integer induction with an explicit base and step."""

    def __init__(self, context: ProofContext, variable: Var, lower, nonnegative):
        self.context = context
        self.variable = variable
        self.lower = lower if isinstance(lower, Expr) else Lit(lower)
        self.parent_goal = context.goal
        self.indvar = Var(context._fresh(variable.name), variable.type)
        self.predicate = substitute_symbols(self.parent_goal, {id(variable): self.indvar})
        self.base_scope = None
        self.step_scope = None
        self.proof = None
        self.result = None
        self._nonnegative = nonnegative
        self.hypotheses = {
            name: statement
            for name, statement in context.hypotheses.items()
            if id(variable) not in free_symbol_ids(statement)
        }

    def base(self):
        goal = substitute_symbols(self.predicate, {id(self.indvar): self.lower})
        self.base_scope = _InductionBase(self.context, goal)
        return self.base_scope

    def step(self):
        # The kernel uses ``k + 1`` for the successor case.
        variable = Var(self.context._fresh("k"), self.indvar.type)
        goal = substitute_symbols(self.predicate, {id(self.indvar): variable + Lit(1)})
        self.step_scope = _InductionStep(self.context, goal, variable, self)
        return self.step_scope

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, traceback):
        if exc_type is not None:
            return False
        if (
            self.base_scope is None
            or self.base_scope.proof is None
            or self.step_scope is None
            or self.step_scope.proof is None
        ):
            raise self.context.failure(
                "induction_unfinished",
                "induction needs a finished base and step",
                goal=self.parent_goal,
            )
        self.proof = Induction(
            self.lower,
            self.indvar,
            self.predicate,
            self.base_scope.proof,
            self.step_scope.step_proof,
        )
        nonnegative = self._nonnegative
        if nonnegative is None:
            for name, statement in self.context.hypotheses.items():
                candidate = Fact(self.context, statement, HypRef(name), label=name)
                if _same(candidate.statement, Not(Lt(self.variable, self.lower))):
                    nonnegative = candidate
                    break
        if nonnegative is None:
            raise self.context.failure(
                "induction_bound",
                "induction needs the current variable's lower-bound fact",
                expected=Not(Lt(self.variable, self.lower)),
            )
        premise = self.context._match_fact(Not(Lt(self.variable, self.lower)), nonnegative)
        conclusion = ForallElim(self.proof, self.variable)
        proof = ImpliesElim(conclusion, premise)
        instantiated = substitute_symbols(
            self.predicate, {id(self.indvar): self.variable}
        )
        self.result = Fact(self.context, instantiated, proof, label="induction")
        return False


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

    # The persistent evidence cache identifies a source-bound proof through
    # these two attributes.  They are not part of the public authoring API.
    tactic.__logos_authoring_source__ = fn
    tactic.__logos_authoring_theorem__ = theorem
    return tactic
