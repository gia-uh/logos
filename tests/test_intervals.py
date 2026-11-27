"""The interval domain: checked lemmas, tactic diagnostics and offline replay."""
from __future__ import annotations

import json
import shutil
import subprocess

import pytest

import logos
from logos import Int, tactics as t
from logos.domains import intervals

CHECKER = shutil.which("logos")

pytestmark = pytest.mark.skipif(
    CHECKER is None, reason="install the Rust logos checker to certify the domain"
)


def test_every_lemma_checks_with_zero_custom_axioms():
    for theorem in intervals.check_all():
        assert theorem.certified
        reading = theorem.inspect()
        assert "Uses zero custom axioms." in reading


def test_the_interval_tactic_closes_an_overlap_from_a_common_point():
    @logos.theorem
    def common_point_by_tactic(a_lo: Int, a_hi: Int, b_lo: Int, b_hi: Int, x: Int):
        return (intervals.contains(a_lo, a_hi, x) & intervals.contains(b_lo, b_hi, x)) >> (
            intervals.overlaps(a_lo, a_hi, b_lo, b_hi)
        )

    logos.check(common_point_by_tactic.proof(
        t.intro("a_lo", "a_hi", "b_lo", "b_hi", "x", "both"),
        intervals.interval,
    ))
    assert common_point_by_tactic.certified


def test_the_tactic_refuses_an_overlap_it_cannot_derive():
    @logos.theorem
    def impossible(a_lo: Int, a_hi: Int, b_lo: Int, b_hi: Int):
        return (a_hi < b_lo) >> intervals.overlaps(a_lo, a_hi, b_lo, b_hi)

    with pytest.raises(logos.LogosProofError) as failure:
        logos.check(impossible.proof(
            t.intro("a_lo", "a_hi", "b_lo", "b_hi", "before"),
            intervals.interval,
        ))
    assert "interval: no linear certificate for" in str(failure.value)
    assert not impossible.certified


def test_the_tactic_refuses_a_goal_that_is_not_an_overlap():
    @logos.theorem
    def wrong_direction(a_lo: Int, a_hi: Int, b_lo: Int, b_hi: Int, x: Int):
        return (intervals.contains(a_lo, a_hi, x) & intervals.contains(b_lo, b_hi, x)) >> (
            ~intervals.overlaps(a_lo, a_hi, b_lo, b_hi)
        )

    with pytest.raises(logos.LogosProofError) as failure:
        logos.check(wrong_direction.proof(
            t.intro("a_lo", "a_hi", "b_lo", "b_hi", "x", "both"),
            intervals.interval,
        ))
    assert "interval: expected an overlap after unfolding" in str(failure.value)


def test_the_exported_certificate_replays_offline(tmp_path):
    target = tmp_path / "common_point.logos"
    logos.export_proof(intervals.common_point_overlaps, target)
    checked = subprocess.run(
        [CHECKER, "check", "--strict", target.name],
        cwd=tmp_path,
        capture_output=True,
        text=True,
    )
    assert checked.returncode == 0, checked.stderr
    assert "Verified with 0 custom axioms" in checked.stdout
    data = json.loads(subprocess.run(
        [CHECKER, "inspect", "--json", "--strict", target.name],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        check=True,
    ).stdout)
    assert data["status"] == "verified"
    assert data["custom_axioms"] == []
    assert any(step["rule"] == "linear" for step in data["steps"])
