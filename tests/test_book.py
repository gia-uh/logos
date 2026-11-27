"""The first book lesson: tangle the Spanish page and check the proof."""
from __future__ import annotations

import importlib.util
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

import logos

BOOK = Path(__file__).resolve().parents[1] / "book"
SCRIPTORIUM = shutil.which("scriptorium")
CHECKER = shutil.which("logos")

pytestmark = pytest.mark.skipif(
    SCRIPTORIUM is None, reason="install Scriptorium to tangle the book chapter"
)


def tangle(directory: Path, text: str | None = None) -> Path:
    source = BOOK / "vecinos.md"
    page = directory / "vecinos.md"
    page.write_text(source.read_text(encoding="utf-8") if text is None else text, encoding="utf-8")
    subprocess.run(
        [SCRIPTORIUM, "tangle", "vecinos.md"],
        cwd=directory,
        check=True,
        capture_output=True,
        text=True,
    )
    # The restored file has the same size as the broken one, so a bytecode
    # cache from this second could otherwise hide the change.
    shutil.rmtree(directory / "__pycache__", ignore_errors=True)
    return directory / "vecinos.py"


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def test_the_lesson_tangles_proves_and_exports(tmp_path):
    module_path = tangle(tmp_path)
    subprocess.run(
        [SCRIPTORIUM, "tangle", "--test", "vecinos.md"],
        cwd=tmp_path,
        check=True,
        capture_output=True,
        text=True,
    )
    module = load(module_path, "book_vecinos_ok")

    for name in ("first_fact", "even_sum", "common_divisor"):
        theorem = getattr(module, name)
        theorem._run_proof(theorem.statement)

    if CHECKER is None:
        pytest.skip("install the Rust logos checker to certify the lesson")

    for name in ("first_fact", "even_sum", "common_divisor"):
        getattr(module, name).check()
    assert module.common_divisor.certified
    logos.export_proof(module.common_divisor, tmp_path / "vecinos.logos")
    result = subprocess.run(
        [CHECKER, "check", "--strict", "vecinos.logos"],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        check=True,
    )
    assert "Verified with 0 custom axioms" in result.stdout
    assert "common_divisor" in result.stdout


def test_one_sign_inversion_reports_the_authored_line_and_both_equalities(tmp_path):
    source = (BOOK / "vecinos.md").read_text(encoding="utf-8")
    assert source.count("    quotient = j - k") == 1
    broken = source.replace("    quotient = j - k", "    quotient = k - j", 1)
    module_path = tangle(tmp_path, broken)
    generated = module_path.read_text(encoding="utf-8")
    module = load(module_path, "book_vecinos_broken")

    with pytest.raises(logos.LogosProofError) as failure:
        module.common_divisor._run_proof(module.common_divisor.statement)

    details = failure.value.details
    assert details["kind"] == "ring_goal_unreachable"
    assert details["file"].endswith("vecinos.py")
    assert details["source_line"].startswith("one = p.ring(")
    assert details["goal"]["text"] == "1 = d * (k - j)"
    assert [item["label"] for item in details["opened"]] == ["left", "right"]
    assert details["opened"][0]["statement"]["text"] == "a = d * k"
    assert details["opened"][1]["statement"]["text"] == "a + 1 = d * j"
    inverted = next(
        line for line in generated.splitlines() if line.strip() == "quotient = k - j"
    )
    assert any(item["source_line"] == inverted.strip() for item in details["related"])
    # The human message carries the same facts as the machine data.
    text = str(failure.value)
    assert "expected goal: 1 = d * (k - j)" in text
    assert "left: a = d * k" in text
    assert "right: a + 1 = d * j" in text

    # Restoring the sign restores the proof.
    restored = load(tangle(tmp_path, source), "book_vecinos_restored")
    restored.common_divisor._run_proof(restored.common_divisor.statement)


NEGATIVES = """\
import logos
from logos import Int, Prop, exists
from logos.expr import Var


@logos.theorem
def first_fact(P: Prop, Q: Prop):
    return (P & Q) >> P


@first_fact.proof
def prove_first(p, P, Q):
    both = p.assume(P & Q)
    return both.right()


@logos.definition
def zdivides(d: Int, a: Int):
    return exists(Int, lambda k: a == d * k)


@logos.theorem
def wrong_witness(d: Int, a: Int):
    return (zdivides(d, a) & zdivides(d, a + 1)) >> zdivides(d, 1)


@wrong_witness.proof
def prove_wrong(p, d, a):
    h = p.assume(zdivides(d, a) & zdivides(d, a + 1))
    k, left = p.obtain(h.left())
    j, right = p.obtain(h.right())
    quotient = j - k
    one = p.ring(1 == d * quotient, using=[left, right])
    return p.witness(k - j, one)


@logos.theorem
def escaped_witness(d: Int, a: Int):
    return (zdivides(d, a) & zdivides(d, a + 1)) >> zdivides(d, 1)


@escaped_witness.proof
def prove_escape(p, d, a):
    h = p.assume(zdivides(d, a) & zdivides(d, a + 1))
    k, left = p.obtain(h.left())
    j, right = p.obtain(h.right())
    quotient = j - k
    one = p.ring(1 == d * quotient, using=[left, right])
    outside = Var("outside", int)
    return p.witness(outside, one)
"""


def test_mismatched_evidence_and_an_escaping_witness_are_rejected(tmp_path):
    path = tmp_path / "negatives.py"
    path.write_text(NEGATIVES, encoding="utf-8")
    module = load(path, "book_negatives")

    with pytest.raises(logos.LogosProofError) as mismatch:
        module.first_fact._run_proof(module.first_fact.statement)
    assert mismatch.value.details["kind"] == "proof_mismatch"
    assert mismatch.value.details["source_line"] == "return both.right()"
    assert mismatch.value.details["expected"]["text"] == "P"
    assert mismatch.value.details["got"]["text"] == "Q"

    with pytest.raises(logos.LogosProofError) as wrong:
        module.wrong_witness._run_proof(module.wrong_witness.statement)
    assert wrong.value.details["kind"] == "witness_mismatch"
    assert wrong.value.details["expected"]["text"] == "1 = d * (k - j)"
    assert wrong.value.details["got"]["text"] == "1 = d * (j - k)"

    with pytest.raises(logos.LogosProofError) as escape:
        module.escaped_witness._run_proof(module.escaped_witness.statement)
    assert escape.value.details["kind"] == "witness_escape"
    assert escape.value.details["unbound"] == ["outside"]
