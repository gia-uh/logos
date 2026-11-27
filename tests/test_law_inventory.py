"""The published law inventory, the Python schema and the verifier agree."""
from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path

import pytest

import logos
from logos.core_laws import LAWS, law_statement
from logos.expr import Div, Le, Len, Lit, Nth, Sorted, Var
from logos.kernel import CoreLaw
from logos.portable import statement_declarations
from logos.sequence import seq_var

CHECKER = shutil.which("logos")
requires_checker = pytest.mark.skipif(
    CHECKER is None, reason="install the Rust logos CLI to check the inventory"
)
ROOT = Path(__file__).resolve().parents[1]


def arguments(sorts):
    return tuple(
        seq_var(f"xs{index}") if sort == "seq" else Var(f"a{index}", int)
        for index, sort in enumerate(sorts)
    )


@requires_checker
def test_the_installed_inventory_is_unique_and_versioned():
    commands = json.loads(subprocess.run(
        [CHECKER, "commands", "--json"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout)
    assert commands["protocol_version"] == 1
    assert commands["proof_formats"] == ["logos-proof-v1"]
    assert commands["theories"] == ["logos-core-v1"]
    published = commands["proof_format"]["core_laws"]
    assert len(published) == len(set(published)) == len(LAWS)
    assert set(published) == set(LAWS)


@requires_checker
@pytest.mark.parametrize("law", list(LAWS))
def test_every_published_law_has_a_checked_instance(law):
    sorts, _ = LAWS[law]
    args = arguments(sorts)
    theorem = logos.Theorem(law_statement(law, args), name=f"{law}_instance")
    logos.check(theorem.proof(lambda goal: CoreLaw(law, args)))
    assert theorem.certified


@requires_checker
def test_the_previously_omitted_laws_are_published():
    commands = json.loads(subprocess.run(
        [CHECKER, "commands", "--json"], capture_output=True, text=True, check=True
    ).stdout)
    published = commands["proof_format"]["core_laws"]
    for law in ("le_refl", "le_trans", "lt_trichotomy", "sorted_gap"):
        assert law in published


@requires_checker
def test_unknown_law_and_wrong_arity_fail_closed():
    a = Var("a", int)
    unknown = logos.Theorem(a == a, name="unknown_law")
    with pytest.raises(logos.LogosProofError) as failure:
        logos.check(unknown.proof(lambda goal: CoreLaw("invented_law", (a,))))
    assert "unknown core law" in str(failure.value)

    short = logos.Theorem(a == a, name="short_law")
    with pytest.raises(logos.LogosProofError) as failure:
        logos.check(short.proof(lambda goal: CoreLaw("lt_dne", (a,))))
    assert "requires 2 substitutions" in str(failure.value)


@requires_checker
def test_a_sequence_law_rejects_an_integer_substitution():
    a = Var("a", int)
    theorem = logos.Theorem(a <= a, name="wrong_sort_law")
    with pytest.raises(logos.LogosProofError) as failure:
        logos.check(theorem.proof(lambda goal: CoreLaw("length_nonneg", (a,))))
    assert "expected seq" in str(failure.value)


def test_declarations_cover_order_sequence_and_division_nodes():
    a, xs = Var("a", int), seq_var("xs")
    assert [v.name for v in statement_declarations(Le(a, a))] == ["a"]
    assert [v.name for v in statement_declarations(Len(xs) > Lit(0))] == ["xs"]
    assert [v.name for v in statement_declarations(Nth(xs, a) == a)] == ["xs", "a"]
    assert [v.name for v in statement_declarations(Sorted(xs))] == ["xs"]
    assert [v.name for v in statement_declarations(Div(a, Lit(2)) == a)] == ["a"]


def test_the_manual_names_every_law():
    manual = (ROOT / "docs" / "portable-proof-format.md").read_text(encoding="utf-8")
    for law in LAWS:
        assert f"`{law}`" in manual, law
    assert "Existential elimination and other domains remain milestone work" not in manual
