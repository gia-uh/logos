"""Checked readings from the Python API, including authored commentary."""
from __future__ import annotations

import json
import shutil
import subprocess

import pytest

import logos
from logos import Prop

pytestmark = pytest.mark.skipif(shutil.which("logos") is None, reason="install the Rust logos CLI")

CLAIM = "Two implications compose: if P implies Q and Q implies R, then P implies R."
STRATEGY = "Reach R through Q, the proposition both implications mention."
FIRST_NOTE = "We now have Q, the premise the second implication needs."
SECOND_NOTE = "The next application reaches R."


def composed(docs: bool = True):
    if docs:
        @logos.theorem
        def compose(P: Prop, Q: Prop, R: Prop):
            """Two implications compose: if P implies Q and Q implies R, then P implies R."""
            return (P >> Q) >> ((Q >> R) >> (P >> R))

        @compose.proof
        def prove_compose(p, P, Q, R):
            """Reach R through Q, the proposition both implications mention."""
            p_to_q = p.assume(P >> Q)
            q_to_r = p.assume(Q >> R)
            given_p = p.assume(P)
            have_q = p.apply(p_to_q, given_p)
            p.note(FIRST_NOTE)
            p.note(SECOND_NOTE)
            return p.apply(q_to_r, have_q)
    else:
        @logos.theorem
        def compose(P: Prop, Q: Prop, R: Prop):
            return (P >> Q) >> ((Q >> R) >> (P >> R))

        @compose.proof
        def prove_compose(p, P, Q, R):
            p_to_q = p.assume(P >> Q)
            q_to_r = p.assume(Q >> R)
            given_p = p.assume(P)
            have_q = p.apply(p_to_q, given_p)
            return p.apply(q_to_r, have_q)

    return compose


def test_inspect_reads_the_current_receipt_and_keeps_authored_prose(tmp_path, monkeypatch):
    theorem = composed()
    logos.check(theorem)
    receipt = theorem.receipt
    assert receipt is not None

    inspected = []
    run = subprocess.run

    def record(argv, **kwargs):
        result = run(argv, **kwargs)
        if len(argv) > 1 and argv[1] == "inspect" and kwargs.get("input") is not None:
            inspected.append((argv, kwargs["input"], result))
        return result

    monkeypatch.setattr(logos.portable.subprocess, "run", record)
    markdown = theorem.inspect()
    assert inspected and inspected[0][1] == receipt.artifact
    assert inspected[0][2].returncode == 0
    assert markdown.startswith("# Checked proof\n")
    assert "## Author's commentary (not checked)" in markdown
    assert CLAIM in markdown and STRATEGY in markdown
    assert "Uses zero custom axioms." in markdown
    assert markdown.count(FIRST_NOTE) == 1
    assert markdown.count(SECOND_NOTE) == 1

    first = markdown.index(FIRST_NOTE)
    second = markdown.index(SECOND_NOTE)
    have_q = markdown.index("**(7)**")
    reach_r = markdown.index("**(8)**")
    assert have_q < first < second < reach_r

    # Repeated reads describe the same receipt and do not duplicate notes.
    assert theorem.inspect() == markdown
    logos.check(theorem)
    assert theorem.inspect() == markdown

    # The authored prose travels in the exported evidence.
    path = tmp_path / "compose.logos"
    logos.export_proof(theorem, path)
    artifact = json.loads(path.read_bytes())
    assert artifact["annotations"] == {"claim": CLAIM, "strategy": STRATEGY}
    assert FIRST_NOTE in json.dumps(artifact["proof"])
    assert SECOND_NOTE in json.dumps(artifact["proof"])

    # An independent checker process reads the same commentary.
    independent = subprocess.run(
        [shutil.which("logos"), "inspect", "--markdown", str(path)],
        capture_output=True,
        text=True,
        check=True,
    )
    assert CLAIM in independent.stdout
    assert FIRST_NOTE in independent.stdout
    first_index = independent.stdout.index(FIRST_NOTE)
    assert independent.stdout.index("**(7)**") < first_index < independent.stdout.index("**(8)**")


def test_inspect_rejects_a_missing_or_stale_receipt():
    theorem = composed()
    with pytest.raises(logos.LogosProofError, match="call logos.check first"):
        theorem.inspect()

    logos.check(theorem)
    theorem._strategy = "A different strategy than the one that was checked."
    with pytest.raises(logos.LogosProofError, match="evidence has changed"):
        theorem.inspect()


def test_no_authored_prose_keeps_the_plain_reading():
    theorem = composed(docs=False)
    logos.check(theorem)
    markdown = theorem.inspect()
    assert "Author's commentary" not in markdown
    assert "Author's note" not in markdown
    assert "Verified." in markdown


def test_a_note_cannot_change_the_proof_obligation():
    @logos.theorem
    def mismatch(P: Prop, Q: Prop):
        return (P >> Q) >> (P >> Q)

    @mismatch.proof
    def prove_mismatch(p, P, Q):
        p.assume(P >> Q)
        p.note("This sentence cannot supply the missing evidence.")
        return p.assume(P)

    with pytest.raises(logos.LogosProofError, match="does not prove the current goal"):
        logos.check(mismatch)
    assert mismatch.receipt is None
    with pytest.raises(logos.LogosProofError, match="call logos.check first"):
        mismatch.inspect()


def test_a_note_needs_an_earlier_checked_step():
    @logos.theorem
    def early(P: Prop):
        return P >> P

    @early.proof
    def prove_early(p, P):
        p.note("There is nothing to attach this to yet.")
        hypothesis = p.assume(P)
        return hypothesis

    with pytest.raises(logos.LogosProofError, match="needs an earlier proof step"):
        logos.check(early)
