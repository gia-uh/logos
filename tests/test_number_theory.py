"""The reusable number theory domain: every lemma, its certificate and its failures."""
from __future__ import annotations

import importlib.util
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

import logos
from logos.domains import number_theory

ROOT = Path(__file__).resolve().parents[1]
DOMAIN = ROOT / "logos" / "domains" / "number_theory.py"
CHECKER = shutil.which("logos")

pytestmark = pytest.mark.skipif(
    CHECKER is None, reason="install the Rust logos checker to check the domain"
)


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def mutated(tmp_path: Path, old: str, new: str, name: str):
    source = DOMAIN.read_text(encoding="utf-8")
    assert source.count(old) == 1, old
    path = tmp_path / f"{name}.py"
    path.write_text(source.replace(old, new, 1), encoding="utf-8")
    return load(path, f"domain_{name}")


def test_every_lemma_checks():
    for lemma in number_theory.LEMMAS:
        lemma.check()
        assert lemma.certified, lemma.name


def test_the_example_computes_the_least_factor_of_five_factorial_plus_one():
    assert number_theory.example() == 121


def test_euclid_exports_a_strict_certificate(tmp_path):
    number_theory.check_all()
    certificate = tmp_path / "euclid.logos"
    logos.export_proof(number_theory.euclid, certificate)
    checked = subprocess.run(
        [CHECKER, "check", "--strict", certificate.name],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        check=True,
    )
    assert "Verified with 0 custom axioms" in checked.stdout
    assert "euclid" in checked.stdout
    assert "prime" in checked.stdout


def test_the_inverted_difference_fails_in_the_consecutive_divisor_lemma(tmp_path):
    module = mutated(tmp_path, "    quotient = j - k", "    quotient = k - j", "sign")
    with pytest.raises(logos.LogosProofError) as failure:
        module.common_divisor.check()
    details = failure.value.details
    assert details["kind"] == "ring_goal_unreachable"
    assert details["source_line"] == "one = p.ring(1 == d * quotient, using=[left, right])"
    text = str(failure.value)
    assert "expected goal: 1 = d * (k - j)" in text
    assert "left: a = d * k" in text
    assert "right: a + 1 = d * j" in text


def test_the_wrong_rewrite_direction_fails_in_the_factorial_lemma(tmp_path):
    module = mutated(
        tmp_path,
        "            step.finish(p.subst(product, p.symm(equation)))",
        "            step.finish(p.subst(product, equation))",
        "rewrite",
    )
    with pytest.raises(logos.LogosProofError) as failure:
        module.factorial_positive.check()
    details = failure.value.details
    assert details["kind"] == "subst_occurrence"
    assert details["expected"]["text"] == "factorial(k + 1)"
    assert "the equality's left side does not occur in the fact" in str(failure.value)


def test_the_wrong_divisor_fails_in_the_least_prime_divisor_proof(tmp_path):
    module = mutated(
        tmp_path,
        "        clash = p.not_elim(no_proper, p.and_intro(d_above_one, d_dvd_m))",
        "        clash = p.not_elim(no_proper, p.and_intro(d_above_one, d_dvd_q))",
        "divisor",
    )
    module.divides_self.check()
    module.divides_trans.check()
    with pytest.raises(logos.LogosProofError) as failure:
        module.least_prime_divisor.check()
    details = failure.value.details
    assert details["kind"] == "evidence_mismatch"
    assert details["expected"]["text"] == "1 < d & exists k:Int. m = d * k"
    assert details["got"]["text"] == "1 < d & exists k:Int. q = d * k"
    assert "the evidence does not prove the expected statement" in str(failure.value)
