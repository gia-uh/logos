"""Render the English book from the installed wheel and the Rust checker.

Each chapter is a native Scriptorium page: it runs its Python blocks directly.
The tests copy one chapter into a temporary directory so the renderer imports
the installed wheel, never the repository checkout.
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

BOOK = Path(__file__).resolve().parents[1] / "book"
CHAPTERS = BOOK / "chapters"
SCRIPTORIUM = shutil.which("scriptorium")
CHECKER = shutil.which("logos")

pytestmark = pytest.mark.skipif(
    SCRIPTORIUM is None or CHECKER is None,
    reason="install Scriptorium and the Rust logos checker to render the book",
)

ORDER = [
    "00-introduction.md",
    "01-quick-start.md",
    "02-first-proof.md",
    "03-conjunction.md",
    "04-cases.md",
    "05-witnesses.md",
    "06-definitions.md",
]

EXPECTED = {
    "00-introduction.md": ["trusted", "Rust checker"],
    "01-quick-start.md": ["checked: True"],
    "02-first-proof.md": ["Author's claim (not checked)."],
    "03-conjunction.md": ["and_swap: True", "and_regroup: True"],
    "04-cases.md": [
        "dilemma: True",
        "or_elim_negation: True",
        "no_contradiction: True",
        "zero_not_positive: True",
    ],
    "05-witnesses.md": ["even_sum: True", "even_multiple: True", "pair_witness: True"],
    "06-definitions.md": ["zero custom axioms: True"],
}

LESSONS = ORDER[3:]


def environment() -> dict[str, str]:
    env = dict(os.environ)
    env["PATH"] = os.pathsep.join(
        [str(Path(CHECKER).parent), str(Path(sys.executable).parent), env.get("PATH", "")]
    )
    return env


def render(tmp_path: Path, name: str, text: str | None = None):
    source = (CHAPTERS / name).read_text(encoding="utf-8")
    page = tmp_path / name
    page.write_text(source if text is None else text, encoding="utf-8")
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


@pytest.mark.parametrize("name", ORDER)
def test_each_chapter_renders_without_a_traceback(tmp_path, name):
    source = (CHAPTERS / name).read_text(encoding="utf-8")
    assert "export=" not in source, f"{name} still uses a tangle block"
    assert "from subprocess import" not in source, f"{name} runs a shell instead of the package"

    result, html = render(tmp_path, name)
    assert result.returncode == 0, result.stderr
    assert html, result.stderr
    assert "Traceback (most recent call last)" not in html
    for marker in EXPECTED[name]:
        assert marker in html, (name, marker)


def test_the_project_lists_every_chapter_in_order():
    config = (BOOK / "scriptorium.yaml").read_text(encoding="utf-8")
    listed = re.findall(r"^\s*-\s+chapters/([\w.-]+)$", config, re.M)
    assert listed == ORDER
    assert "format: docs" in config
    assert "format: pdf" in config
    assert "dir: site" in config


@pytest.mark.parametrize("name", ["00-introduction.md", "01-quick-start.md"] + LESSONS)
def test_the_chapter_states_what_the_reader_needs(name):
    source = (CHAPTERS / name).read_text(encoding="utf-8")
    if name == "00-introduction.md":
        assert "## Scope" in source
        assert "## What the trusted checker owns" in source
    elif name == "01-quick-start.md":
        assert "**Prerequisites.**" in source
        assert "**Outcomes.**" in source
        assert "cargo install" in source
        assert "compose.check()" in source
    else:
        assert "**Prerequisites.**" in source
        assert "**Outcomes.**" in source


@pytest.mark.parametrize("name", LESSONS)
def test_each_lesson_has_a_diagnostic_and_an_exit_exercise(name):
    source = (CHAPTERS / name).read_text(encoding="utf-8")
    assert "## When a step fails" in source
    assert "## Exit exercise" in source


def test_quick_start_reports_a_real_receipt(tmp_path):
    result, html = render(tmp_path, "01-quick-start.md")
    assert result.returncode == 0, result.stderr
    assert re.search(r"artifact: [0-9a-f]{16}", html)
    assert "installed Rust logos checker not found on PATH" in html


def test_conjunction_names_the_goal_and_the_evidence(tmp_path):
    source = (CHAPTERS / "03-conjunction.md").read_text(encoding="utf-8")
    broken = source.replace(
        "    return p.and_intro(q_fact, p_fact)",
        "    return both",
        1,
    )
    _, html = render(tmp_path, "03-conjunction.md", broken)
    assert "the returned evidence does not prove the current goal" in html
    assert "expected goal: Q &amp; P" in html
    assert "got: P &amp; Q" in html


def test_cases_reports_the_unfinished_branch(tmp_path):
    source = (CHAPTERS / "04-cases.md").read_text(encoding="utf-8")
    broken = source.replace(
        "            cases.finish(p.apply(from_p, p_case))",
        "            cases.finish(p_case)",
        1,
    )
    _, html = render(tmp_path, "04-cases.md", broken)
    assert "the evidence does not prove the expected statement" in html
    assert "expected: R" in html
    assert "got: P" in html


def test_witnesses_report_the_instantiated_predicate(tmp_path):
    source = (CHAPTERS / "05-witnesses.md").read_text(encoding="utf-8")
    broken = source.replace(
        "    return p.witness(i + j, sum_eq)",
        "    return p.witness(i + j + 1, sum_eq)",
        1,
    )
    _, html = render(tmp_path, "05-witnesses.md", broken)
    assert "the evidence does not prove the instantiated existential predicate" in html


def test_definitions_report_the_lemma_premise(tmp_path):
    source = (CHAPTERS / "06-definitions.md").read_text(encoding="utf-8")
    broken = source.replace(
        "    return p.apply(chain, p.and_intro(multiple, square))",
        "    return p.apply(chain, p.and_intro(square, multiple))",
        1,
    )
    _, html = render(tmp_path, "06-definitions.md", broken)
    assert "does not prove the antecedent needed by divides_trans" in html
    assert "expected: divides(a, b)" in html
