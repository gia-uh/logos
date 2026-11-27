"""The executable prime-number example, checked by the installed Rust CLI."""
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

pytestmark = pytest.mark.skipif(shutil.which("logos") is None, reason="install the Rust logos CLI")

EXAMPLES = Path(__file__).resolve().parents[1] / "examples"
STATEMENT = "∃p:int"


def run(argv, cwd, code=0):
    environment = {**os.environ, "PYTHONPATH": str(EXAMPLES.parent)}
    result = subprocess.run(argv, cwd=cwd, capture_output=True, text=True, env=environment)
    assert result.returncode == code, (result.stdout, result.stderr)
    return result


def test_the_example_builds_a_strict_certificate(tmp_path):
    run([sys.executable, str(EXAMPLES / "primes.py"), "primes.logos"], tmp_path)
    replay = run(["logos", "check", "--strict", "primes.logos"], tmp_path)
    assert "Verified with 0 custom axioms" in replay.stdout
    assert STATEMENT in replay.stdout

    inspected = json.loads(
        run(["logos", "inspect", "--json", "--strict", "primes.logos"], tmp_path).stdout
    )
    assert inspected["status"] == "verified"
    assert inspected["custom_axioms"] == []
    assert inspected["theory"] == "logos-core-v1"

    rendered = run(
        ["logos", "inspect", "--markdown", "--strict", "primes.logos"], tmp_path
    ).stdout
    assert "Verified with 0 custom axioms" not in rendered


def test_a_forged_target_is_rejected(tmp_path):
    run([sys.executable, str(EXAMPLES / "primes.py"), "primes.logos"], tmp_path)
    artifact = json.loads((tmp_path / "primes.logos").read_text())
    order = artifact["target"]["body"]["right"]["body"]["right"]
    order["left"], order["right"] = order["right"], order["left"]
    (tmp_path / "forged.logos").write_text(json.dumps(artifact))
    rejected = run(["logos", "check", "--strict", "forged.logos"], tmp_path, code=1)
    assert "proof conclusion mismatch" in rejected.stderr
