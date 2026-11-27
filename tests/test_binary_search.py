"""Total correctness of the executable binary search contract."""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

import pytest

import logos
from logos.expr import ForallNode, Lit, Var

CHECKER = shutil.which("logos")
requires_checker = pytest.mark.skipif(CHECKER is None, reason="install the Rust logos CLI")


def binary_search(xs: list[int], target: int) -> int:
    low = 0
    high = len(xs)
    answer = -1
    while low < high:
        mid = (low + high) // 2
        if xs[mid] == target:
            answer = mid
            low = high
        elif xs[mid] < target:
            low = mid + 1
        else:
            high = mid
    return answer


def _contract_body(xs, target, *, result):
    low = Var("low", int)
    high = Var("high", int)
    answer = Var("answer", int)
    i = Var("i", int)
    n = logos.length(xs)
    lower_cut = ForallNode(
        i, (Lit(0) <= i) >> ((i < low) >> (logos.nth(xs, i) < target))
    )
    upper_cut = ForallNode(
        i, (high <= i) >> ((i < n) >> (target < logos.nth(xs, i)))
    )
    found = (
        (Lit(0) <= answer)
        & (answer < n)
        & (logos.nth(xs, answer) == target)
        & ~(answer == -1)
    )
    searching = (answer == -1) & lower_cut & upper_cut
    invariant = (
        logos.sorted(xs)
        & (Lit(0) <= low)
        & (low <= high)
        & (high <= n)
        & (found | searching)
    )
    ensures = (
        ((result == -1) & logos.absent(xs, target))
        | ((Lit(0) <= result) & (result < n) & (logos.nth(xs, result) == target))
    )
    return logos.program_contract(
        requires=logos.sorted(xs),
        ensures=ensures,
        invariant=invariant,
        variant=high - low,
    )


binary_search_correct = logos.theorem(about=binary_search)(_contract_body)


def _import(tmp_path, name, source):
    path = tmp_path / f"{name}.py"
    path.write_text(source)
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    try:
        spec.loader.exec_module(module)
    finally:
        sys.modules.pop(name, None)
    return module


def test_contract_proves_every_input_and_exports_with_zero_axioms(tmp_path):
    logos.check(binary_search_correct)
    assert binary_search_correct.certified
    artifact = tmp_path / "binary_search.logos"
    logos.export_proof(binary_search_correct, artifact)

    if CHECKER is not None:
        result = subprocess.run(
            [CHECKER, "check", "--strict", str(artifact)], capture_output=True, text=True
        )
        assert result.returncode == 0, result.stderr
        assert "Verified with 0 custom axioms" in result.stdout
        inspected = json.loads(
            subprocess.run(
                [CHECKER, "inspect", "--json", "--strict", str(artifact)],
                capture_output=True,
                text=True,
                check=True,
            ).stdout
        )
        assert inspected["status"] == "verified"
        assert inspected["custom_axioms"] == []
        data = json.loads(artifact.read_text())
        assert data["programs"][0]["body"]
        assert data["programs"][0]["obligations"]


def test_the_statement_quantifies_sequences_and_the_result():
    statement = binary_search_correct.statement
    names = []
    while isinstance(statement, ForallNode):
        names.append(statement.var.name)
        statement = statement.body
    assert names == ["xs", "target", "result"]


def test_executable_edges_agree_with_the_contract():
    cases = [
        ([], 1),
        ([1], 1),
        ([1], 0),
        ([1, 2, 2, 2, 3], 2),
        ([1, 2, 2, 2, 3], 9),
        ([-5, -2, 0, 7], -2),
    ]
    for xs, target in cases:
        result = binary_search(xs, target)
        if result == -1:
            assert target not in xs
        else:
            assert 0 <= result < len(xs) and xs[result] == target


WRONG_MIDPOINT = '''\
import logos
from logos.expr import ForallNode, Lit, Var


def binary_search(xs: list[int], target: int) -> int:
    low = 0
    high = len(xs)
    answer = -1
    while low < high:
        mid = (low + high + 1) // 2
        if xs[mid] == target:
            answer = mid
            low = high
        elif xs[mid] < target:
            low = mid + 1
        else:
            high = mid
    return answer


@logos.theorem(about=binary_search)
def binary_search_correct(xs, target, *, result):
    low = Var("low", int)
    high = Var("high", int)
    answer = Var("answer", int)
    i = Var("i", int)
    n = logos.length(xs)
    lower = ForallNode(i, (Lit(0) <= i) >> ((i < low) >> (logos.nth(xs, i) < target)))
    upper = ForallNode(i, (high <= i) >> ((i < n) >> (target < logos.nth(xs, i))))
    found = (Lit(0) <= answer) & (answer < n) & (logos.nth(xs, answer) == target) & ~(answer == -1)
    searching = (answer == -1) & lower & upper
    invariant = logos.sorted(xs) & (Lit(0) <= low) & (low <= high) & (high <= n) & (found | searching)
    ensures = ((result == -1) & logos.absent(xs, target)) | ((Lit(0) <= result) & (result < n) & (logos.nth(xs, result) == target))
    return logos.program_contract(requires=logos.sorted(xs), ensures=ensures, invariant=invariant, variant=high - low)


binary_search_correct.check()
'''

WRONG_INVARIANT = WRONG_MIDPOINT.replace(
    "mid = (low + high + 1) // 2", "mid = (low + high) // 2"
).replace(
    "invariant = logos.sorted(xs) & (Lit(0) <= low) & (low <= high) & (high <= n) & (found | searching)",
    "invariant = logos.sorted(xs) & (Lit(0) <= low) & (low < high) & (high <= n) & (found | searching)",
)


def _run_module(tmp_path, source):
    path = tmp_path / "attempt.py"
    path.write_text(source)
    return subprocess.run(
        [sys.executable, str(path)],
        capture_output=True,
        text=True,
        cwd=tmp_path,
        env={**os.environ, "PYTHONPATH": str(Path(__file__).resolve().parents[1])},
    )


def test_a_wrong_midpoint_is_refused(tmp_path):
    result = _run_module(tmp_path, WRONG_MIDPOINT)
    assert result.returncode != 0
    assert "LogosProofError" in result.stderr or "cannot prove" in result.stderr


def test_a_wrong_invariant_is_refused(tmp_path):
    result = _run_module(tmp_path, WRONG_INVARIANT)
    assert result.returncode != 0


@requires_checker
def test_a_forged_program_body_is_rejected(tmp_path):
    logos.check(binary_search_correct)
    artifact = tmp_path / "binary_search.logos"
    logos.export_proof(binary_search_correct, artifact)
    data = json.loads(artifact.read_text())
    program = data["programs"][0]
    found = program["body"][-2]
    # Mutate the loop's found branch assignment from answer = mid to answer = 0.
    for statement in found["body"]:
        if statement.get("tag") == "if":
            for item in statement["then_body"]:
                if item.get("tag") == "assign":
                    item["value"] = {"tag": "int", "value": "0"}
                    break
    forged = tmp_path / "forged.logos"
    forged.write_text(json.dumps(data))
    result = subprocess.run(
        [CHECKER, "check", "--json", str(forged)], capture_output=True, text=True
    )
    assert result.returncode != 0


@requires_checker
def test_a_missing_obligation_is_rejected(tmp_path):
    logos.check(binary_search_correct)
    artifact = tmp_path / "binary_search.logos"
    logos.export_proof(binary_search_correct, artifact)
    data = json.loads(artifact.read_text())
    data["programs"][0]["obligations"].pop()
    forged = tmp_path / "forged-missing.logos"
    forged.write_text(json.dumps(data))
    result = subprocess.run(
        [CHECKER, "check", "--json", str(forged)], capture_output=True, text=True
    )
    assert result.returncode != 0
    assert "missing proof" in result.stderr or "missing" in result.stderr
