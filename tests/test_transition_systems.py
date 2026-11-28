"""Finite induction certificates and replay of the lock's concrete violation."""
import json
from pathlib import Path
import shutil
import subprocess
import sys

import pytest

from logos import LogosProofError
from logos.domains.transition_systems import FiniteTransitionSystem

EXAMPLE = Path(__file__).resolve().parents[1] / "examples" / "two_client_lock.py"
CHECKER = shutil.which("logos")
needs_checker = pytest.mark.skipif(CHECKER is None, reason="install the Rust logos checker")


def small_model(*, initial=("start",), edges=None, safe=None):
    return FiniteTransitionSystem(
        ("start", "next", "bad"),
        initial,
        {"advance": edges if edges is not None else [("start", "next"), ("bad", "bad")]},
        safe if safe is not None else lambda state: state != "bad",
    )


def test_rejects_initial_or_endpoint_outside_the_declared_universe():
    with pytest.raises(ValueError, match="initial state is outside"):
        small_model(initial=("unknown",))
    with pytest.raises(ValueError, match="endpoint outside"):
        small_model(edges=[("start", "unknown")])


@pytest.mark.parametrize(
    ("model", "invariant", "diagnostic"),
    [
        (small_model(), ("next",), "failed initial inclusion at 'start'"),
        (small_model(edges=[("start", "next"), ("start", "bad")]), ("start", "next"),
         "failed closure under 'advance': 'start' -> 'bad'"),
        (small_model(), ("start", "next", "bad"), "failed invariant safety at 'bad'"),
    ],
)
def test_failed_obligation_writes_no_evidence(tmp_path, model, invariant, diagnostic):
    path = tmp_path / "invalid.logos"
    with pytest.raises(LogosProofError, match=diagnostic):
        model.export_safety(invariant, path)
    assert not path.exists()


@needs_checker
def test_unreachable_bad_state_and_strict_checker(tmp_path):
    model = small_model()
    assert "bad" in model.universe and "bad" not in model.safe_states
    path = tmp_path / "safety.logos"
    receipt = model.export_safety(("start", "next"), path)
    assert model.verify_safety(("next", "start"), path) == receipt
    result = subprocess.run(
        [CHECKER, "check", "--strict", str(path)], capture_output=True, text=True, check=True,
    )
    assert "Verified with 0 custom axioms" in result.stdout

    bundle = json.loads(path.read_bytes())
    # Preserve the entire expected target while replacing the evidence with
    # a valid proof of the fingerprint alone. Rust must reject the mismatch.
    proof = bundle["proof"]
    bundle["proof"] = proof["left"]["left"]
    path.write_text(json.dumps(bundle))
    with pytest.raises(LogosProofError):
        model.verify_safety(("start", "next"), path)
    forged = subprocess.run([CHECKER, "check", "--strict", str(path)], capture_output=True)
    assert forged.returncode == 1


@needs_checker
def test_stale_certificate_rejected_even_when_obligations_still_hold(tmp_path):
    original = small_model(safe=lambda _: True)
    path = tmp_path / "safety.logos"
    invariant = ("start", "next")
    original.export_safety(invariant, path)
    for other_model in (
        small_model(safe=lambda _: True, edges=[("start", "next")]),
        small_model(safe=lambda _: True, initial=("next",)),
        small_model(),
        FiniteTransitionSystem(
            ("start", "next", "bad"), ("start",), {"renamed": original.transitions["advance"]},
            lambda _: True,
        ),
        FiniteTransitionSystem(
            ("start", "next", "other"), ("start",),
            {"advance": [("start", "next"), ("other", "other")]}, lambda _: True,
        ),
    ):
        with pytest.raises(LogosProofError, match="does not match"):
            other_model.verify_safety(invariant, path)
    with pytest.raises(LogosProofError, match="does not match"):
        original.verify_safety(("start", "next", "bad"), path)


def test_replay_checks_start_names_successors_and_final_predicate():
    model = small_model(edges=[("start", "next"), ("start", "bad")])
    assert model.replay_violation("start", [("advance", "bad")]) == "bad"
    for start, steps, diagnostic in (
        ("next", [], "outside the initial set"),
        ("start", [("wrong", "bad")], "illegal step 1"),
        ("start", [("advance", "next"), ("advance", "bad")], "illegal step 2"),
        ("start", [("advance", "next")], "ends in a safe state"),
    ):
        with pytest.raises(ValueError, match=diagnostic):
            model.replay_violation(start, steps)


@needs_checker
def test_standalone_lock_exports_and_replays(tmp_path):
    path = tmp_path / "lock.logos"

    def run(*args, check=True):
        return subprocess.run(
            [sys.executable, "-I", str(EXAMPLE), *args], cwd=tmp_path,
            text=True, capture_output=True, check=check,
        )

    run("--export", str(path))
    run("--verify", str(path))
    mutant = run("--replay", "mutant")
    assert mutant.stdout.splitlines() == [
        "('idle', 'idle', 'free')",
        "  --A.acquire--> ('critical', 'idle', 'A')",
        "  --B.acquire--> ('critical', 'critical', 'B')",
        "Mutual exclusion violated.",
    ]
    correct = run("--replay", "correct", check=False)
    assert correct.returncode == 1
    assert "illegal step 2" in correct.stderr
