"""Floor-division laws and the fragments a production contract needs."""

import shutil
import subprocess

import pytest

import logos
from logos import tactics as t
from logos.core_laws import law_statement
from logos.expr import Div, Implies, Le, Lit, Lt, Mul, Var
from logos.goal import Goal
from logos.helpers import structural_eq
from logos.portable import artifact_bytes, statement_declarations
from logos.runner import run

CHECKER = shutil.which("logos")
requires_checker = pytest.mark.skipif(CHECKER is None, reason="install the Rust logos CLI")


def halve(n: int, flag: int) -> int:
    if flag:
        n //= 2
    else:
        n //= 3
    while n > 10:
        n = n // 2
    return n


@logos.theorem(about=halve)
def halve_nonnegative(n, flag, *, result):
    from logos.expr import Var
    return logos.program_contract(
        requires=(Lit(0) <= n),
        ensures=(Lit(0) <= result),
        invariant=(Lit(0) <= n),
        variant=n,
    )


def test_division_schemas_are_explicit():
    a, b = Var("a", int), Var("b", int)
    assert structural_eq(
        law_statement("div_nonneg", (a, b)),
        Implies(Le(Lit(0), a), Implies(Lt(Lit(0), b), Le(Lit(0), Div(a, b)))),
    )
    assert structural_eq(
        law_statement("div_lt", (a, b)),
        Implies(Lt(Lit(0), a), Implies(Lt(Lit(1), b), Lt(Div(a, b), a))),
    )
    assert structural_eq(
        law_statement("mul_nonneg", (a, b)),
        Implies(Le(Lit(0), a), Implies(Le(Lit(0), b), Le(Lit(0), Mul(a, b)))),
    )


def test_order_tactic_emits_the_division_law():
    statement = logos.forall(
        int, int, lambda a, b: (Lit(0) < a) >> ((Lit(1) < b) >> (Div(a, b) < a))
    )
    evidence = run(Goal({}, statement), [t.intro("a", "b", "h1", "h2"), t.order("div_lt")])
    artifact = artifact_bytes(
        "div_lt_tactic", statement, statement_declarations(statement), evidence
    )
    assert b'"id":"div_lt"' in artifact or b'"id": "div_lt"' in artifact


def test_augmented_assignment_and_a_bare_integer_flag():
    halve_nonnegative.check()
    assert halve_nonnegative.certified
    assert "loop0.preserve" in halve_nonnegative.program.obligations


@requires_checker
def test_the_halve_certificate_verifies_strictly(tmp_path):
    halve_nonnegative.check()
    artifact = tmp_path / "halve.logos"
    logos.export_proof(halve_nonnegative, artifact)
    result = subprocess.run(
        [CHECKER, "check", "--strict", str(artifact)],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stderr
    assert "Verified with 0 custom axioms" in result.stdout
