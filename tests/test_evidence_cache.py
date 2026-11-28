"""Persistent compiled-evidence reuse across fresh interpreters.

These tests drive the public authoring API in child Python processes because
the cache is meant to be observed between processes: a cold process writes
records, a warm process reuses them, and Rust still checks every artifact.
"""
from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

import logos
from logos import evidence_cache

PACKAGE_ROOT = Path(logos.__file__).resolve().parent.parent
CHECKER = shutil.which("logos")
requires_checker = pytest.mark.skipif(CHECKER is None, reason="install the Rust logos CLI")

LIBRARY = """\
from logos import theorem, lit

def _eq(a, b):
    return (lit(a) - lit(a)) == (lit(b) - lit(b))

@theorem
def f_0_1():
    return _eq(0, 1)

@f_0_1.proof
def prove_f_0_1(p):
    return p.ring(_eq(0, 1))

@theorem
def f_1_2():
    return _eq(1, 2)

@f_1_2.proof
def prove_f_1_2(p):
    return p.ring(_eq(1, 2))

@theorem
def f_0_2():
    return _eq(0, 2)

@f_0_2.proof
def prove_f_0_2(p):
    return p.trans(p.apply(f_0_1), p.apply(f_1_2))

@theorem
def f_2_4():
    return _eq(2, 4)

@f_2_4.proof
def prove_f_2_4(p):
    return p.ring(_eq(2, 4))

@theorem
def f_0_4():
    return _eq(0, 4)

@f_0_4.proof
def prove_f_0_4(p):
    return p.trans(p.apply(f_0_2), p.apply(f_2_4))

roots = (f_0_2, f_2_4)

@theorem
def result():
    return _eq(0, 4)

@result.proof
def prove_result(p):
    return p.trans(p.apply(roots[0]), p.apply(roots[1]))
"""

RUNNER = """\
import json, sys, hashlib
import logos
from logos.theorem import _Proof
from logos import evidence_cache

executed = []
_original = _Proof._run_proof
def record(self, *args, **kwargs):
    executed.append(self.name)
    return _original(self, *args, **kwargs)
_Proof._run_proof = record

checks = []
import logos.portable as portable
_run = portable.subprocess.run
def counting(argv, *args, **kwargs):
    result = _run(argv, *args, **kwargs)
    if len(argv) > 1 and argv[1] == "check":
        checks.append(result.returncode)
    return result
portable.subprocess.run = counting

import os
import library
target = getattr(library, sys.argv[1] if len(sys.argv) > 1 else "result")
try:
    logos.check(target)
    ok = True
    error = None
except Exception as exc:
    ok = False
    error = str(exc)
reading = None
if ok:
    open("artifact.logos", "wb").write(target.receipt.artifact)
    if os.environ.get("LOGOS_INSPECT") == "1":
        reading = target.inspect()
    if os.environ.get("LOGOS_EXPORT") == "1":
        logos.export_proof(target, "exported.logos")
print(json.dumps({
    "ok": ok,
    "error": error,
    "executed": executed,
    "checks": checks,
    "artifact": hashlib.sha256(target.receipt.artifact).hexdigest() if ok else None,
    "reading": reading,
    "package": logos.__file__,
}))
"""


def write_library(tmp_path: Path, source: str = LIBRARY) -> Path:
    path = tmp_path / "library.py"
    path.write_text(source, encoding="utf-8")
    (tmp_path / "runner.py").write_text(RUNNER, encoding="utf-8")
    return path


def run(tmp_path: Path, cache: Path, *, target: str = "result", env_extra=None):
    environment = os.environ.copy()
    environment["LOGOS_CACHE_DIR"] = str(cache)
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["PYTHONPATH"] = str(PACKAGE_ROOT)
    if env_extra:
        environment.update(env_extra)
    result = subprocess.run(
        [sys.executable, "-B", str(tmp_path / "runner.py"), target],
        cwd=tmp_path,
        env=environment,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    return json.loads(result.stdout)


def records(cache: Path) -> list[dict]:
    found = []
    for path in cache.rglob("*.json"):
        found.append(json.loads(path.read_text()))
    return found


def record_for(cache: Path, name: str) -> Path:
    for path in cache.rglob("*.json"):
        record = json.loads(path.read_text())
        if record.get("name") == name:
            return path
    raise AssertionError(f"no cache record for {name}")


@requires_checker
def test_cold_then_warm_process_reuses_every_proof(tmp_path):
    write_library(tmp_path)
    cache = tmp_path / "cache"

    cold = run(tmp_path, cache)
    assert cold["ok"] and cold["executed"]
    assert Path(cold["package"]).resolve() == Path(logos.__file__).resolve()
    assert len(cold["checks"]) == 1
    assert len(records(cache)) == 5

    warm = run(tmp_path, cache)
    assert warm["ok"]
    assert warm["executed"] == []
    assert len(warm["checks"]) == 1
    assert warm["artifact"] == cold["artifact"]


@requires_checker
def test_new_theorem_reuses_two_roots_through_a_module_tuple(tmp_path):
    write_library(tmp_path)
    cache = tmp_path / "cache"
    seed = LIBRARY.split("roots = (")[0]
    result_block = "roots = (f_0_2, f_2_4)\n" + LIBRARY.split(
        "roots = (f_0_2, f_2_4)\n", 1
    )[1]
    (tmp_path / "library.py").write_text(seed, encoding="utf-8")
    seeded = run(tmp_path, cache, target="f_0_2")
    assert seeded["executed"] == ["f_0_2", "f_0_1", "f_1_2"]
    assert run(tmp_path, cache, target="f_2_4")["executed"] == ["f_2_4"]

    (tmp_path / "library.py").write_text(seed + result_block, encoding="utf-8")
    new = run(tmp_path, cache)
    assert new["ok"]
    assert new["executed"] == ["result"]
    assert len(new["checks"]) == 1
    assert len(records(cache)) == 5


@requires_checker
def test_branch_and_base_edits_recompile_only_the_edited_proof(tmp_path):
    write_library(tmp_path)
    cache = tmp_path / "cache"
    assert run(tmp_path, cache)["ok"]

    source = (tmp_path / "library.py").read_text()
    branch = source.replace(
        "return p.ring(_eq(1, 2))",
        "return p.symm(p.symm(p.ring(_eq(1, 2))))",
    )
    (tmp_path / "library.py").write_text(branch, encoding="utf-8")
    edited = run(tmp_path, cache)
    assert edited["ok"] and edited["executed"] == ["f_1_2"]

    (tmp_path / "library.py").write_text(
        branch.replace(
            "return p.ring(_eq(0, 1))",
            "return p.symm(p.symm(p.ring(_eq(0, 1))))",
        ),
        encoding="utf-8",
    )
    base = run(tmp_path, cache)
    assert base["ok"] and base["executed"] == ["f_0_1"]


@requires_checker
def test_edited_proof_with_wrong_evidence_fails_with_an_old_certificate(tmp_path):
    write_library(tmp_path)
    cache = tmp_path / "cache"
    cold = run(tmp_path, cache)
    assert cold["ok"]
    old_bytes = (tmp_path / "artifact.logos").read_bytes()

    source = (tmp_path / "library.py").read_text()
    (tmp_path / "library.py").write_text(
        source.replace("return p.ring(_eq(1, 2))", "return p.refl(lit(7))"),
        encoding="utf-8",
    )
    broken = run(tmp_path, cache)
    assert not broken["ok"]
    assert "does not prove" in broken["error"] or "does not match" in broken["error"]
    assert broken["executed"] == ["f_1_2"]

    # The old certificate is still independently valid.
    old = subprocess.run(
        [CHECKER, "check", "--strict", "-"],
        input=old_bytes,
        capture_output=True,
        check=False,
    )
    assert old.returncode == 0, old.stderr.decode()


@requires_checker
def test_changed_dependency_statement_is_not_reused(tmp_path):
    write_library(tmp_path)
    cache = tmp_path / "cache"
    assert run(tmp_path, cache)["ok"]

    source = (tmp_path / "library.py").read_text()
    changed = source.replace("return _eq(1, 2)", "return _eq(1, 3)").replace(
        "return p.ring(_eq(1, 2))", "return p.ring(_eq(1, 3))"
    )
    (tmp_path / "library.py").write_text(changed, encoding="utf-8")

    leaf = run(tmp_path, cache, target="f_1_2")
    assert leaf["ok"] and leaf["executed"] == ["f_1_2"]

    parent = run(tmp_path, cache)
    assert not parent["ok"]
    assert "f_0_2" in parent["executed"]
    assert "f_1_2" in (parent["error"] or "")


@requires_checker
def test_corrupt_and_incompatible_records_fall_back_and_recover(tmp_path):
    write_library(tmp_path)
    cache = tmp_path / "cache"
    assert run(tmp_path, cache)["ok"]

    target = record_for(cache, "f_1_2")
    target.write_text("{not json", encoding="utf-8")
    recovered = run(tmp_path, cache)
    assert recovered["ok"] and recovered["executed"] == ["f_1_2"]
    json.loads(target.read_text())

    record = json.loads(target.read_text())
    record["format"] = "other-evidence-format"
    target.write_text(json.dumps(record), encoding="utf-8")
    recovered = run(tmp_path, cache)
    assert recovered["ok"] and recovered["executed"] == ["f_1_2"]


@requires_checker
def test_tampered_record_is_rejected_by_rust(tmp_path):
    write_library(tmp_path)
    cache = tmp_path / "cache"
    assert run(tmp_path, cache)["ok"]

    target = record_for(cache, "f_1_2")
    record = json.loads(target.read_text())
    record["evidence"] = {
        "k": "proof",
        "c": "Refl",
        "f": {"expr": {"k": "lit", "i": "7"}},
    }
    target.write_text(json.dumps(record), encoding="utf-8")

    tampered = run(tmp_path, cache)
    assert not tampered["ok"]
    assert tampered["executed"] == []
    assert "f_1_2" in (tampered["error"] or "")


BINDER_LIBRARY = """\
from logos import theorem, Int
from logos.expr import ExistsNode, Var

def _even(a):
    i = Var("i", int)
    return ExistsNode(i, a == 2 * i)

@theorem
def even_same(a: Int):
    return _even(a) >> _even(a)

@even_same.proof
def prove_even_same(p, a):
    premise = p.assume(_even(a))
    i, a_eq = p.obtain(premise)
    return p.witness(i, a_eq)
"""


@requires_checker
def test_fresh_eigenvariables_survive_a_cache_hit(tmp_path):
    write_library(tmp_path, BINDER_LIBRARY)
    cache = tmp_path / "cache"
    cold = run(tmp_path, cache, target="even_same")
    assert cold["ok"] and cold["executed"] == ["even_same"]
    warm = run(tmp_path, cache, target="even_same")
    assert warm["ok"] and warm["executed"] == []
    assert warm["artifact"] == cold["artifact"]


AXIOM_LIBRARY = """\
from logos import theorem, axiom, lit

assumption = axiom((lit(1) - lit(1)) == (lit(2) - lit(2)))

@theorem
def from_axiom():
    return (lit(1) - lit(1)) == (lit(2) - lit(2))

@from_axiom.proof
def prove_from_axiom(p):
    return p.apply(assumption)
"""


@requires_checker
def test_axiom_policy_is_bound_to_the_cached_evidence(tmp_path):
    write_library(tmp_path, AXIOM_LIBRARY)
    cache = tmp_path / "cache"
    assert run(tmp_path, cache, target="from_axiom")["ok"]
    assert run(tmp_path, cache, target="from_axiom")["executed"] == []

    import importlib.util

    spec = importlib.util.spec_from_file_location("axiom_library", tmp_path / "library.py")
    loaded = importlib.util.module_from_spec(spec)
    sys.modules["axiom_library"] = loaded
    spec.loader.exec_module(loaded)
    first = evidence_cache._plan(loaded.from_axiom)
    assert first is not None
    loaded.assumption.statement = logos.lit(7) == logos.lit(7)
    second = evidence_cache._plan(loaded.from_axiom)
    assert second is not None and second.key != first.key


@requires_checker
def test_unwritable_cache_does_not_block_checking(tmp_path):
    write_library(tmp_path)
    blocker = tmp_path / "blocked"
    blocker.write_text("not a directory", encoding="utf-8")
    result = run(tmp_path, blocker / "cache")
    assert result["ok"] and len(result["executed"]) == 5


@requires_checker
def test_disabled_cache_forces_execution(tmp_path):
    write_library(tmp_path)
    cache = tmp_path / "cache"
    assert run(tmp_path, cache)["ok"]
    disabled = run(tmp_path, cache, env_extra={"LOGOS_CACHE": "off"})
    assert disabled["ok"] and len(disabled["executed"]) == 5


@requires_checker
def test_concurrent_cold_writers_leave_a_usable_cache(tmp_path):
    write_library(tmp_path)
    cache = tmp_path / "cache"
    environment = os.environ.copy()
    environment["LOGOS_CACHE_DIR"] = str(cache)
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["PYTHONPATH"] = str(PACKAGE_ROOT)
    first = subprocess.Popen(
        [sys.executable, "-B", str(tmp_path / "runner.py")],
        cwd=tmp_path, env=environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    second = subprocess.Popen(
        [sys.executable, "-B", str(tmp_path / "runner.py")],
        cwd=tmp_path, env=environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    first_out, first_err = first.communicate(timeout=60)
    second_out, second_err = second.communicate(timeout=60)
    assert first.returncode == 0, first_err.decode()
    assert second.returncode == 0, second_err.decode()
    assert json.loads(first_out)["ok"] and json.loads(second_out)["ok"]
    assert run(tmp_path, cache)["executed"] == []


NOTE_LIBRARY = """\
from logos import theorem, lit

@theorem
def noted():
    \"\"\"Claim: the integer one equals itself.\"\"\"
    return lit(1) == lit(1)

@noted.proof
def prove_noted(p):
    \"\"\"Strategy: reflexivity, with a note for the reader.\"\"\"
    fact = p.refl(lit(1))
    p.note("The checker reads this note after the evidence.")
    return fact
"""


@requires_checker
def test_warm_reading_and_export_keep_docstrings_and_notes(tmp_path):
    write_library(tmp_path, NOTE_LIBRARY)
    cache = tmp_path / "cache"
    assert run(tmp_path, cache, target="noted")["ok"]
    warm = run(
        tmp_path, cache, target="noted",
        env_extra={"LOGOS_INSPECT": "1", "LOGOS_EXPORT": "1"},
    )
    assert warm["ok"] and warm["executed"] == []
    assert "Checked proof" in warm["reading"]
    assert "The checker reads this note after the evidence." in warm["reading"]
    assert (tmp_path / "exported.logos").read_bytes() == (tmp_path / "artifact.logos").read_bytes()


MUTABLE = []


def _loaded_module(tmp_path, name, source):
    import importlib.util

    path = tmp_path / f"{name}.py"
    path.write_text(source, encoding="utf-8")
    spec = importlib.util.spec_from_file_location(name, path)
    loaded = importlib.util.module_from_spec(spec)
    sys.modules[name] = loaded
    spec.loader.exec_module(loaded)
    return loaded


def test_ineligible_proof_reruns_on_every_explicit_check(tmp_path, monkeypatch):
    loaded = _loaded_module(
        tmp_path,
        "mutable_state",
        """\
from logos import theorem, lit
state = [True]

@theorem
def mutable():
    return lit(1) == lit(1)

@mutable.proof
def prove_mutable(p):
    if state[0]:
        return p.refl(lit(1))
    return p.refl(lit(2))
""",
    )
    logos.check(loaded.mutable)
    loaded.state[0] = False
    with pytest.raises(logos.LogosProofError, match="does not prove"):
        logos.check(loaded.mutable)

    # The same failure must not depend on the cache being enabled.
    loaded.state[0] = True
    logos.check(loaded.mutable)
    loaded.state[0] = False
    monkeypatch.setenv("LOGOS_CACHE", "off")
    with pytest.raises(logos.LogosProofError, match="does not prove"):
        logos.check(loaded.mutable)


def test_unordered_or_opaque_python_is_not_eligible(tmp_path):
    loaded = _loaded_module(
        tmp_path,
        "nondeterministic",
        """\
from logos import theorem, lit

def choose():
    return next(iter(set(("alpha", "beta"))))

@theorem
def target():
    return lit(1) == lit(1)

@target.proof
def prove_target(p):
    if choose() == "alpha":
        return p.refl(lit(1))
    return p.refl(lit(2))
""",
    )
    assert evidence_cache._plan(loaded.target) is None

    loaded2 = _loaded_module(
        tmp_path,
        "opaque_attribute",
        """\
from logos import theorem, lit

@theorem
def target():
    return lit(1) == lit(1)

@target.proof
def prove_target(p):
    return p.refl(target._evidence)
""",
    )
    assert evidence_cache._plan(loaded2.target) is None


@requires_checker
def test_nondeterministic_set_proof_writes_no_record(tmp_path):
    source = """\
from logos import theorem, lit

def choose():
    return next(iter(set(("alpha", "beta"))))

@theorem
def target():
    return lit(1) == lit(1)

@target.proof
def prove_target(p):
    if choose() == "alpha":
        return p.refl(lit(1))
    return p.refl(lit(2))
"""
    write_library(tmp_path, source)
    cache = tmp_path / "cache"
    first = run(tmp_path, cache, target="target")
    second = run(tmp_path, cache, target="target")
    assert records(cache) == []
    assert first["executed"] == ["target"] and second["executed"] == ["target"]


def test_plain_tactics_and_unsafe_python_are_not_eligible(tmp_path):
    statement = logos.lit(1) == logos.lit(1)

    plain = logos.Theorem(statement, name="plain")
    plain.proof([lambda goal: logos.kernel.Refl(logos.lit(1))])
    assert evidence_cache._plan(plain) is None

    def factory():
        @logos.theorem
        def nested():
            return logos.lit(1) == logos.lit(1)

        @nested.proof
        def prove_nested(p):
            return p.ring(logos.lit(1) == logos.lit(1))

        return nested

    assert evidence_cache._plan(factory()) is None

    @logos.theorem
    def mutable():
        return logos.lit(1) == logos.lit(1)

    @mutable.proof
    def prove_mutable(p):
        MUTABLE.append(1)
        return p.ring(logos.lit(1) == logos.lit(1))

    assert evidence_cache._plan(mutable) is None


def test_declared_statement_change_changes_the_key(tmp_path):
    module = tmp_path / "statement_library.py"
    module.write_text(LIBRARY, encoding="utf-8")
    import importlib.util

    spec = importlib.util.spec_from_file_location("statement_library", module)
    loaded = importlib.util.module_from_spec(spec)
    sys.modules["statement_library"] = loaded
    spec.loader.exec_module(loaded)

    first = evidence_cache._plan(loaded.f_0_1)
    assert first is not None
    loaded.f_0_1.statement = (logos.lit(0) - logos.lit(0)) == (
        logos.lit(2) - logos.lit(2)
    )
    second = evidence_cache._plan(loaded.f_0_1)
    assert second is not None and second.key != first.key


def test_dependency_on_a_global_constant_changes_the_key(tmp_path):
    module = tmp_path / "constant_library.py"
    module.write_text(
        textwrap.dedent(
            """\
            from logos import theorem, lit
            LIMIT = 1

            @theorem
            def constant():
                return (lit(1) - lit(1)) == (lit(2) - lit(2))

            @constant.proof
            def prove_constant(p):
                if LIMIT:
                    return p.ring((lit(1) - lit(1)) == (lit(2) - lit(2)))
                return p.ring((lit(1) - lit(1)) == (lit(2) - lit(2)))
            """
        ),
        encoding="utf-8",
    )
    import importlib.util

    spec = importlib.util.spec_from_file_location("constant_library", module)
    loaded = importlib.util.module_from_spec(spec)
    sys.modules["constant_library"] = loaded
    spec.loader.exec_module(loaded)

    first = evidence_cache._plan(loaded.constant)
    assert first is not None
    loaded.LIMIT = 2
    second = evidence_cache._plan(loaded.constant)
    assert second is not None and second.key != first.key
