"""Executable program fragments and their checked loop certificates.

The source fragment is a straight-line function with one ``while`` loop. Its
statements and loop assertions are exported in the portable artifact. The Rust
checker recomputes every verification condition from this program, then checks
the proofs supplied for those conditions. No loop summary is trusted.

A ``Call`` names another checked function. The callee program travels in the
same artifact and the Rust checker verifies it before the caller's conditions
use its contract. The ``Call`` object keeps the declaration, not a snapshot:
the caller always uses the callee's current, revalidated program.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from logos.expr import Expr, Var
from logos.define import Function


@dataclass(frozen=True)
class ProgramVariable:
    name: str
    sort: Any
    var: Var


@dataclass(frozen=True)
class NamedClause:
    """One authored contract clause, kept beside the proposition it denotes."""

    name: str
    expr: Expr


@dataclass(frozen=True)
class Assign:
    name: str
    value: Expr


@dataclass(frozen=True)
class If:
    condition: Expr
    then_body: tuple["Statement", ...]
    else_body: tuple["Statement", ...]


@dataclass(frozen=True)
class While:
    condition: Expr
    body: tuple["Statement", ...]
    invariant: Expr
    variant: Expr
    invariants: tuple[NamedClause, ...] = ()
    decreases_name: str | None = None


@dataclass(frozen=True)
class Return:
    value: Expr


@dataclass(frozen=True)
class Call:
    """A direct call to another checked function.

    ``callee`` is the callee's declaration object. ``function`` is its opaque
    function symbol. ``target`` is the local that receives the result.
    """

    id: str
    target: str
    callee: Any
    function: Function
    args: tuple[Expr, ...]
    line: int
    fingerprint: str = ""


Statement = Assign | If | While | Return | Call


@dataclass
class Program:
    name: str
    function: Function
    params: tuple[ProgramVariable, ...]
    result: ProgramVariable
    locals: tuple[ProgramVariable, ...]
    requires: Expr
    ensures: Expr
    body: tuple[Statement, ...]
    ghosts: tuple[ProgramVariable, ...] = ()
    obligations: dict[str, Any] = field(default_factory=dict)
    requires_clauses: tuple[NamedClause, ...] = ()
    ensures_clauses: tuple[NamedClause, ...] = ()

    @property
    def variables(self) -> tuple[ProgramVariable, ...]:
        return (*self.params, *self.locals, *self.ghosts, self.result)


@dataclass(frozen=True)
class ProgramContract:
    requires: Expr
    ensures: Expr
    invariant: Expr
    variant: Expr


def program_contract(*, requires: Expr, ensures: Expr, invariant: Expr, variant: Expr) -> ProgramContract:
    if not isinstance(requires, Expr) or not isinstance(ensures, Expr):
        raise TypeError("logos.program_contract: requires and ensures must be Logos expressions")
    if not isinstance(invariant, Expr) or not isinstance(variant, Expr):
        raise TypeError("logos.program_contract: invariant and variant must be Logos expressions")
    return ProgramContract(requires, ensures, invariant, variant)


def call_statements(program: Program) -> tuple[Call, ...]:
    """Every call in the program body, in source order."""
    found: list[Call] = []

    def walk(statements):
        for statement in statements:
            if isinstance(statement, Call):
                found.append(statement)
            elif isinstance(statement, If):
                walk(statement.then_body)
                walk(statement.else_body)
            elif isinstance(statement, While):
                walk(statement.body)

    walk(program.body)
    return tuple(found)
