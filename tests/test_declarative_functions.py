"""Declarative ``@logos.function`` contracts and independently checked calls.

These tests run against the installed wheel and the Rust checker, like the book
tests. They keep the small example first, then the guarded caller, then the
binary search, and exercise the refusals: unsupported syntax at decoration,
clause scope and sort errors, a missing guard at a call, and forged, stale,
missing, mismatched or cyclic callee artifacts.
"""
from __future__ import annotations

import importlib.util
import json
import shutil
import subprocess
import sys
import uuid
from pathlib import Path

import pytest

import logos
from logos.contracts import LogosContractError
from logos.portable import LogosProofError

ROOT = Path(__file__).resolve().parents[1]
CALLS = ROOT / "book" / "examples" / "declarative_calls.py"
BINARY = ROOT / "book" / "examples" / "binary_search.py"
CHECKER = shutil.which("logos")
requires_checker = pytest.mark.skipif(CHECKER is None, reason="install the Rust logos CLI")


def load(path: Path, name: str | None = None):
    module_name = name or f"decl_{uuid.uuid4().hex}"
    spec = importlib.util.spec_from_file_location(module_name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def write_module(tmp_path: Path, text: str, name: str | None = None):
    module_name = name or f"decl_{uuid.uuid4().hex}"
    path = tmp_path / f"{module_name}.py"
    path.write_text(text, encoding="utf-8")
    return load(path, module_name), path


def check_strict(path: Path) -> subprocess.CompletedProcess:
    return subprocess.run(
        [CHECKER, "check", "--strict", str(path)],
        capture_output=True,
        text=True,
        check=False,
    )


@requires_checker
def test_the_small_example_checks_and_replays_strictly(tmp_path):
    module = load(CALLS)
    module.first.check()
    module.first_or_zero.check()
    assert module.first.certified
    assert module.first_or_zero.certified
    assert list(module.first.program.obligations) == ["read0", "main"]
    assert list(module.first_or_zero.program.obligations) == [
        "call0.requires.nonempty",
        "main",
    ]
    certificate = tmp_path / "first_or_zero.logos"
    logos.export_proof(module.first_or_zero, certificate)
    result = check_strict(certificate)
    assert result.returncode == 0, result.stderr
    assert "Verified with 0 custom axioms" in result.stdout


def test_the_decorator_returns_the_original_function():
    module = load(CALLS)
    assert module.first is module.__dict__["first"]
    assert not hasattr(module.first, "__wrapped__")
    assert module.first([7]) == 7
    with pytest.raises(IndexError):
        module.first([])
    assert module.first_or_zero([]) == 0
    assert module.first_or_zero([9, 8]) == 9


def test_unsupported_body_syntax_is_rejected_at_decoration(tmp_path):
    text = (
        "import logos\n"
        "\n"
        "@logos.function\n"
        "def append_one(xs: list[int]) -> int:\n"
        "    xs.append(1)\n"
        "    return 0\n"
    )
    with pytest.raises(LogosContractError) as caught:
        write_module(tmp_path, text)
    message = str(caught.value)
    assert "append_one" in message
    assert ":5:" in message
    assert "unsupported statement" in message

    loop = (
        "import logos\n"
        "\n"
        "@logos.function\n"
        "def first(xs: list[int]) -> int:\n"
        "    for value in xs:\n"
        "        return value\n"
        "    return 0\n"
    )
    with pytest.raises(LogosContractError) as caught:
        write_module(tmp_path, loop)
    assert ":5:" in str(caught.value)
    assert "For" in str(caught.value)


def test_clause_scope_and_sort_are_validated(tmp_path):
    base = (
        "import logos\n"
        "\n"
        "@logos.function\n"
        "def first(xs: list[int]) -> int:\n"
        "    return xs[0]\n"
        "\n"
    )
    cases = {
        "unknown name": (
            "@first.requires\n"
            "def bad(xs, low):\n"
            "    return 0 <= low\n"
        ),
        "result outside ensures": (
            "@first.requires\n"
            "def bad(xs, *, result):\n"
            "    return result == 0\n"
        ),
        "wrong sort": (
            "@first.requires\n"
            "def bad(xs):\n"
            "    return 1\n"
        ),
        "manual symbol": (
            "from logos.expr import Var\n"
            "@first.requires\n"
            "def bad(xs):\n"
            "    return 0 < Var('xs', int)\n"
        ),
        "invariant without loop": (
            "@first.invariant\n"
            "def bad(xs):\n"
            "    return logos.sorted(xs)\n"
        ),
    }
    for label, clause in cases.items():
        with pytest.raises(LogosContractError) as caught:
            write_module(tmp_path, base + clause)
        message = str(caught.value)
        assert "bad" in message, label
        assert __import__("re").search(r":\d+:", message), (label, message)
        assert "declares no while loop" in message or "not available" in message or "not a declared" in message or "Logos expression" in message or "must be" in message, (label, message)


@requires_checker
def test_the_missing_guard_names_the_call_line_callee_clause_and_need(tmp_path):
    source = CALLS.read_text(encoding="utf-8")
    broken = source.split("\ndef main()", 1)[0] + (
        "\n\n@logos.function\n"
        "def unguarded(xs: list[int]) -> int:\n"
        "    return first(xs)\n"
        "\n"
        "@unguarded.ensures\n"
        "def zero_or_first_unguarded(xs, *, result):\n"
        "    return (result == 0) | (result == logos.nth(xs, 0))\n"
    )
    module, _ = write_module(tmp_path, broken)
    with pytest.raises(LogosContractError) as caught:
        module.unguarded.check()
    message = str(caught.value)
    assert "calls 'first'" in message
    assert "'nonempty'" in message
    assert "0 < len(xs)" in message
    assert "line " in message
    assert not module.unguarded.certified


@requires_checker
def test_forged_missing_mismatched_and_cyclic_callees_are_rejected(tmp_path):
    module = load(CALLS)
    module.first_or_zero.check()
    certificate = tmp_path / "caller.logos"
    logos.export_proof(module.first_or_zero, certificate)
    data = json.loads(certificate.read_text(encoding="utf-8"))
    callee = next(program for program in data["programs"] if program["function"] == "f2")
    caller = next(program for program in data["programs"] if program["function"] == "f1")
    assert callee["id"] != caller["id"]

    forged = json.loads(certificate.read_text(encoding="utf-8"))
    forged_callee = next(
        program for program in forged["programs"] if program["function"] == "f2"
    )
    forged_callee["requires"] = {"tag": "int", "value": "0"}
    path = tmp_path / "forged.logos"
    path.write_text(json.dumps(forged), encoding="utf-8")
    result = check_strict(path)
    assert result.returncode != 0
    assert "sort" in result.stderr or "produces" in result.stderr

    missing = json.loads(certificate.read_text(encoding="utf-8"))
    missing["programs"] = [
        program for program in missing["programs"] if program["id"] != callee["id"]
    ]
    path = tmp_path / "missing.logos"
    path.write_text(json.dumps(missing), encoding="utf-8")
    result = check_strict(path)
    assert result.returncode != 0
    assert "unknown callee" in result.stderr

    mismatched = json.loads(certificate.read_text(encoding="utf-8"))
    mismatched_caller = next(
        program for program in mismatched["programs"] if program["function"] == "f1"
    )
    mismatched_caller["calls"][0]["requires"] = {"tag": "int", "value": "0"}
    path = tmp_path / "mismatched.logos"
    path.write_text(json.dumps(mismatched), encoding="utf-8")
    result = check_strict(path)
    assert result.returncode != 0
    assert "differs from callee" in result.stderr

    cyclic = json.loads(certificate.read_text(encoding="utf-8"))
    cyclic_callee = next(
        program for program in cyclic["programs"] if program["function"] == "f2"
    )
    cyclic_callee["calls"].append(
        {
            "id": "cycle",
            "callee": caller["id"],
            "line": 1,
            "requires": {"tag": "int", "value": "0"},
            "ensures": {"tag": "int", "value": "0"},
        }
    )
    path = tmp_path / "cyclic.logos"
    path.write_text(json.dumps(cyclic), encoding="utf-8")
    result = check_strict(path)
    assert result.returncode != 0
    assert "cyclic call dependency" in result.stderr


@requires_checker
def test_source_and_callee_binding_changes_are_refused(tmp_path):
    source = CALLS.read_text(encoding="utf-8")
    module, path = write_module(tmp_path, source)
    module.first_or_zero.check()
    assert module.first_or_zero.certified

    path.write_text(source.replace("return xs[0]", "return xs[-1]"), encoding="utf-8")
    with pytest.raises(LogosProofError) as caught:
        module.first_or_zero.inspect()
    assert "changed" in str(caught.value) or "no current" in str(caught.value)


@requires_checker
def test_rebinding_the_callee_is_refused(tmp_path):
    module, _ = write_module(tmp_path, CALLS.read_text(encoding="utf-8"))
    module.first_or_zero.check()
    module.first = lambda xs: 0
    with pytest.raises(LogosContractError) as caught:
        module.first_or_zero.check()
    assert "was rebound" in str(caught.value)


@requires_checker
def test_a_literal_true_clause_is_a_real_trivial_precondition(tmp_path):
    text = (
        "import logos\n"
        "\n"
        "@logos.function\n"
        "def identity(x: int) -> int:\n"
        "    return x\n"
        "\n"
        "@identity.requires\n"
        "def anything(x):\n"
        "    return True\n"
        "\n"
        "@identity.ensures\n"
        "def same(x, *, result):\n"
        "    return result == x\n"
    )
    module, _ = write_module(tmp_path, text)
    module.identity.check()
    assert module.identity.certified
    assert "read0" not in module.identity.program.obligations


@requires_checker
def test_binary_search_named_clauses_and_runtime_counterexample(tmp_path):
    module = load(BINARY)
    module.binary_search.check()
    assert module.binary_search.certified
    obligations = list(module.binary_search.program.obligations)
    for expected in (
        "loop0.preserve.bounds",
        "loop0.preserve.keeps_order",
        "loop0.preserve.below_cut",
        "loop0.preserve.above_cut",
        "loop0.preserve.answer_or_searching",
        "loop0.variant_decreases.remaining",
    ):
        assert expected in obligations
    reading = module.binary_search.inspect()
    for name in ("bounds", "keeps_order", "below_cut", "above_cut", "remaining"):
        assert name in reading
    certificate = tmp_path / "binary_search.logos"
    logos.export_proof(module.binary_search, certificate)
    result = check_strict(certificate)
    assert result.returncode == 0, result.stderr
    assert "Verified with 0 custom axioms" in result.stdout
    example = [2, 0, 1]
    assert module.binary_search(example, 2) == -1
    assert 2 in example


@requires_checker
@pytest.mark.parametrize(
    "old, new, expected",
    [
        (
            "mid = (low + high) // 2",
            "mid = (low + high + 1) // 2",
            "loop0.preserve",
        ),
        ("& (low <= high)", "& (low < high)", "high < high"),
        (
            "@binary_search.requires\ndef ordered(xs):\n    return logos.sorted(xs)",
            "@binary_search.requires\ndef ordered(xs):\n    return 0 <= logos.length(xs)",
            "main: no proof found for sorted(xs)",
        ),
    ],
)
def test_binary_search_negative_controls(tmp_path, old, new, expected):
    source = BINARY.read_text(encoding="utf-8")
    assert old in source
    module, _ = write_module(tmp_path, source.replace(old, new, 1))
    with pytest.raises(LogosContractError) as caught:
        module.binary_search.check()
    assert expected in str(caught.value), str(caught.value)[:600]
    assert not module.binary_search.certified
