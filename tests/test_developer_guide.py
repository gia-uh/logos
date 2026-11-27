"""The Developer Guide renders from the installed wheel and matches the module.

The chapter quotes the interval domain section by section. This test compares
every quote with the source, renders both new chapters, replays the exported
certificate and regenerates the API reference in memory.
"""
from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

import logos
from logos import Int, tactics as t
from logos.domains.intervals import overlaps

ROOT = Path(__file__).resolve().parents[1]
CHAPTERS = ROOT / "book" / "chapters"
DOMAIN = ROOT / "logos" / "domains" / "intervals.py"
SCRIPTORIUM = shutil.which("scriptorium")
CHECKER = shutil.which("logos")

pytestmark = pytest.mark.skipif(
    SCRIPTORIUM is None or CHECKER is None,
    reason="install Scriptorium and the Rust logos checker to render the guide",
)

GUIDE = "14-developer-guide.md"
REFERENCE = "15-api-reference.md"

SOURCE_REF = re.compile(
    r"<!-- source: ([\w-]+) -->\s*\n```python[^\n]*\n(.*?)\n```", re.S
)


def environment() -> dict[str, str]:
    env = dict(os.environ)
    env["PATH"] = os.pathsep.join(
        [str(Path(CHECKER).parent), str(Path(sys.executable).parent), env.get("PATH", "")]
    )
    return env


def render(tmp_path: Path, name: str):
    source = (CHAPTERS / name).read_text(encoding="utf-8")
    page = tmp_path / name
    page.write_text(source, encoding="utf-8")
    output = tmp_path / f"{page.stem}.html"
    result = subprocess.run(
        [SCRIPTORIUM, "render", page.name, "--html", "-o", str(output)],
        cwd=tmp_path,
        env=environment(),
        capture_output=True,
        text=True,
        check=False,
    )
    html = output.read_text(encoding="utf-8") if output.exists() else ""
    return result, html


def domain_snippets() -> dict[str, str]:
    found: dict[str, list[str]] = {}
    current: str | None = None
    for line in DOMAIN.read_text(encoding="utf-8").splitlines():
        start = re.match(r"^# --8<-- \[start:([\w-]+)\]$", line.strip())
        end = re.match(r"^# --8<-- \[end:([\w-]+)\]$", line.strip())
        if start:
            current = start.group(1)
            found[current] = []
            continue
        if end:
            current = None
            continue
        if current is not None:
            found[current].append(line)
    return {name: "\n".join(body).strip("\n") for name, body in found.items()}


def test_every_quoted_snippet_matches_the_interval_module():
    quoted = SOURCE_REF.findall((CHAPTERS / GUIDE).read_text(encoding="utf-8"))
    library = domain_snippets()
    assert quoted, "the guide does not quote the domain"
    for snippet, text in quoted:
        assert snippet in library, snippet
        assert textwrap.dedent(text).strip() == textwrap.dedent(library[snippet]).strip(), (
            snippet,
        )


def test_the_guide_renders_and_replays_its_certificate(tmp_path):
    result, html = render(tmp_path, GUIDE)
    assert result.returncode == 0, result.stderr
    assert "Traceback (most recent call last)" not in html
    for marker in (
        "compose: Rust replay verified and the checked reading includes the note",
        "overlap_self: True",
        "common_point_by_tactic: True",
        "diagnostic: Theorem 'impossible': interval: no linear certificate for a_lo &lt;= b_hi",
        "diagnostic: Theorem 'wrong_shape': interval: expected an overlap after unfolding",
        "construction diagnostic: Theorem 'common_point_by_tactic': "
        "linear arithmetic could not derive the goal from these facts",
        "expected goal: b_lo &lt;= a_hi",
        "From (5) and (17).",
        "The conclusion follows from (50).",
        "zero custom axioms: True",
        "certificate: intervals.logos",
    ):
        assert marker in html, marker
    assert html.count('<section class="proof">') == 2
    assert (tmp_path / "intervals.logos").exists()
    checked = subprocess.run(
        [CHECKER, "check", "--strict", "intervals.logos"],
        cwd=tmp_path,
        capture_output=True,
        text=True,
    )
    assert checked.returncode == 0, checked.stderr
    assert "Verified with 0 custom axioms" in checked.stdout
    markdown = subprocess.run(
        [CHECKER, "inspect", "--markdown", "--strict", "intervals.logos"],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        check=True,
    )
    assert markdown.stdout.startswith("# Checked proof\n")
    assert "## Conclusion" in markdown.stdout

    artifact = json.loads((tmp_path / "intervals.logos").read_bytes())
    proof = artifact["proof"]
    while proof["tag"] in {"forall_intro", "implies_intro"}:
        proof = proof["body"]
    assert proof["tag"] == "and_intro"
    first = proof["left"]
    for suffix in ("ll", "lr", "rl", "rr"):
        assert first["tag"] == "have"
        assert first["binder"] == f"__interval_5{suffix}"
        first = first["body"]
    assert first["tag"] == "linear"
    assert {item["binder"]: item["coefficient"] for item in first["terms"]} == {
        "__interval_5ll": "1",
        "__interval_5rr": "1",
    }

    first["terms"][0]["coefficient"] = "0"
    forged = tmp_path / "forged.logos"
    forged.write_text(json.dumps(artifact), encoding="utf-8")
    rejected = subprocess.run(
        [CHECKER, "check", "--strict", forged],
        capture_output=True,
        text=True,
        check=False,
    )
    assert rejected.returncode != 0
    assert "linear: the certified combination is not contradictory" in rejected.stderr


def test_instructor_interval_solutions(tmp_path):
    """Solutions for the Chapter 14 exit exercise."""

    @logos.definition
    def touches(a_lo: Int, a_hi: Int, b_lo: Int, b_hi: Int):
        return (a_hi == b_lo) | (b_hi == a_lo)

    @logos.theorem
    def touches_symmetric(a_lo: Int, a_hi: Int, b_lo: Int, b_hi: Int):
        return touches(a_lo, a_hi, b_lo, b_hi) >> touches(b_lo, b_hi, a_lo, a_hi)

    # Swapping the intervals swaps the two disjuncts. In each branch,
    # the original equality closes the opposite side of the new goal.
    touches_symmetric.proof(t.unfold(touches), t.intro(), t.auto())

    @logos.theorem
    def singleton_touches(x: Int):
        return touches(x, x, x, x)

    # Both endpoint equalities reduce to x == x. Either disjunct suffices.
    singleton_touches.proof(t.unfold(touches), t.intro(), t.auto())

    @logos.definition
    def inside(a_lo: Int, a_hi: Int, b_lo: Int, b_hi: Int):
        return (b_lo <= a_lo) & (a_hi <= b_hi)

    @logos.theorem
    def inner_overlap_extends(a_lo: Int, a_hi: Int, b_lo: Int, b_hi: Int,
                              c_lo: Int, c_hi: Int):
        return (
            inside(a_lo, a_hi, b_lo, b_hi) & overlaps(a_lo, a_hi, c_lo, c_hi)
        ) >> overlaps(b_lo, b_hi, c_lo, c_hi)

    @inner_overlap_extends.proof
    def prove_inner_overlap_extends(p, a_lo, a_hi, b_lo, b_hi, c_lo, c_hi):
        premises = p.assume(inside(a_lo, a_hi, b_lo, b_hi) &
                            overlaps(a_lo, a_hi, c_lo, c_hi))
        containment, inner_overlap = premises.left(), premises.right()
        # b_lo <= a_lo <= c_hi
        first = p.linear(b_lo <= c_hi, using=[containment.left(), inner_overlap.left()])
        # c_lo <= a_hi <= b_hi
        second = p.linear(c_lo <= b_hi, using=[inner_overlap.right(), containment.right()])
        return p.and_intro(first, second)

    # These definitions and certificates use existing equality and order rules.
    for theorem in (touches_symmetric, singleton_touches, inner_overlap_extends):
        theorem.check()
        target = tmp_path / f"{theorem.name}.logos"
        logos.export_proof(theorem, target)
        checked = subprocess.run(
            [CHECKER, "check", "--strict", target], capture_output=True, text=True, check=True,
        )
        assert "Verified with 0 custom axioms" in checked.stdout


def test_instructor_interval_counterexamples():
    def endpoint_contact(a, b):
        return a[1] == b[0] or b[1] == a[0]

    def cross_bounds(a, b):
        return a[0] <= b[1] and b[0] <= a[1]

    separated_a, separated_b = (0, 1), (2, 3)
    assert separated_a[1] < separated_b[0]
    assert not endpoint_contact(separated_a, separated_b)
    assert not cross_bounds(separated_a, separated_b)

    nonempty = (0, 2)
    assert nonempty[0] < nonempty[1]
    assert not endpoint_contact(nonempty, nonempty)

    inner, outer, third = (0, 1), (0, 10), (9, 10)
    assert outer[0] <= inner[0] <= inner[1] <= outer[1]
    assert cross_bounds(outer, third)
    assert not cross_bounds(inner, third)

    invalid, valid = (3, 1), (0, 4)
    assert cross_bounds(invalid, valid)
    assert not set(range(invalid[0], invalid[1] + 1))


def test_the_reference_renders_witness_lookups(tmp_path):
    result, html = render(tmp_path, REFERENCE)
    assert result.returncode == 0, result.stderr
    assert "Traceback (most recent call last)" not in html
    assert "Tactic witness certified</p>" in html
    assert "Proof-context witness and existential fact certified</p>" in html

    ids = re.findall(r'<h[1-6] id="([^"]+)"', html)
    assert len(ids) == len(set(ids))
    assert set(re.findall(r'href="#([^"]+)"', html)) <= set(ids)
    for contract in (
        "from logos.tactics import witness",
        "witness(val: Expr)",
        "witness(value: Expr, evidence: Fact | ProofTerm) -&gt; ProofTerm",
        "exists(goal: Expr, value: Expr, evidence: Fact) -&gt; Fact",
        "a*m + b*m == (a+b)*m",
    ):
        assert f"<code>{contract}</code>" in html
    for private in ("_Ring", "_Scope", "_Generator", "_finite"):
        assert private not in html


def test_reference_witness_failures():
    from logos import LogosProofError, check, exists, lit, prove, theorem, var
    from logos.goal import Goal
    from logos.runner import TacticFailed

    statement = exists(Int, lambda x: x > 4)
    with pytest.raises(TacticFailed, match="witness: expected Exists"):
        t.witness(lit(5))(Goal({}, lit(5) > 4))
    with pytest.raises(LogosProofError, match="proposition is False"):
        check(prove(statement, [t.witness(lit(4)), t.decide()]))

    @theorem
    def above_four():
        return statement

    @above_four.proof
    def wrong_evidence(p):
        return p.witness(5, p.linear(lit(6) > 4))

    with pytest.raises(LogosProofError) as error:
        check(above_four)
    assert error.value.details["kind"] == "witness_mismatch"

    @above_four.proof
    def escaped_symbol(p):
        return p.witness(var("outside", Int), p.linear(lit(5) > 4))

    with pytest.raises(LogosProofError) as error:
        check(above_four)
    assert error.value.details["kind"] == "witness_escape"

    @above_four.proof
    def wrong_existential_evidence(p):
        return p.exists(statement, 5, p.linear(lit(6) > 4))

    with pytest.raises(LogosProofError) as error:
        check(above_four)
    assert error.value.details["kind"] == "evidence_mismatch"

    @above_four.proof
    def wrong_existential_target(p):
        target = lit(5) > 4
        return p.exists(target, 5, p.linear(target))

    with pytest.raises(LogosProofError) as error:
        check(above_four)
    assert error.value.details["kind"] == "exists_goal"


def test_the_reference_matches_a_fresh_render():
    from tools.generate_api_reference import INVENTORY, inventory, render as generate

    current = (CHAPTERS / REFERENCE).read_text(encoding="utf-8")
    assert current == generate(), "book/chapters/15-api-reference.md is stale"
    assert INVENTORY.read_text(encoding="utf-8") == inventory()
