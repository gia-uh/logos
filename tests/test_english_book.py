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
import textwrap
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
BOOK = ROOT / "book"
CHAPTERS = BOOK / "chapters"
DOMAIN = ROOT / "logos" / "domains" / "number_theory.py"
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
    "07-parity.md",
    "08-neighbours.md",
    "09-factorial.md",
    "10-least-prime.md",
    "11-euclid.md",
    "12-binary-search.md",
    "13-production-contract.md",
    "14-developer-guide.md",
    "15-api-reference.md",
]

EXPECTED = {
    "00-introduction.md": ["trusted", "Rust checker"],
    "01-quick-start.md": ["checked: True"],
    "02-first-proof.md": ["Checked proof", "Author's commentary (not checked)", "Uses zero custom axioms."],
    "03-conjunction.md": ["and_swap: True", "and_regroup: True"],
    "04-cases.md": [
        "dilemma: True",
        "or_elim_negation: True",
        "no_contradiction: True",
        "zero_not_positive: True",
    ],
    "05-witnesses.md": ["even_sum: True", "even_multiple: True", "pair_witness: True"],
    "06-definitions.md": ["zero custom axioms: True"],
    "07-parity.md": ["even_sum: True", "odd_successor: True", "divides_mul: True"],
    "08-neighbours.md": [
        "common_divisor: True",
        "not_dvd_one: True",
        "common_divisor_not_above_one: True",
    ],
    "09-factorial.md": [
        "factorial_positive: True",
        "factorial_above_one: True",
        "factorial_dvd: True",
    ],
    "10-least-prime.md": ["least_prime_divisor: True", "least: 7"],
    "11-euclid.md": ["euclid: True", "certificate: euclid.logos"],
    "12-binary-search.md": [
        "binary_search_correct: True",
        "certificate: binary_search.logos",
        "result: -1",
        "postcondition holds: False",
    ],
    "13-production-contract.md": [
        "adapt_bias_nonnegative: True",
        "certificate: adapt.logos",
        "obligations: loop0.preserve",
    ],
    "14-developer-guide.md": [
        "overlap_self: True",
        "common_point_by_tactic: True",
        "interval: no linear certificate for",
        "zero custom axioms: True",
        "certificate: intervals.logos",
    ],
    "15-api-reference.md": [
        "Classes",
        "Functions and methods",
        "Theorem",
        "export_proof",
    ],
}

LESSONS = ORDER[3:-1]


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
    assert "from subprocess import" not in source, f"{name} runs a shell instead of the package"
    for workaround in (
        "BINARY_SEARCH =",
        "PUNYCODE_ADAPT =",
        "importlib.util",
        "tempfile",
        "spec_from_file_location",
        "write_text(",
    ):
        assert workaround not in source, f"{name} hides the executable source behind {workaround!r}"

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


SOURCE_REF = re.compile(
    r"<!-- source: ([\w-]+) -->\s*\n```python[^\n]*\n(.*?)\n```", re.S
)


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


@pytest.mark.parametrize("name", [chapter for chapter in ORDER if chapter < "14"])
def test_quoted_number_theory_snippets_match_the_module(name):
    source = (CHAPTERS / name).read_text(encoding="utf-8")
    quoted = SOURCE_REF.findall(source)
    library = domain_snippets()
    for snippet, text in quoted:
        assert snippet in library, (name, snippet)
        assert textwrap.dedent(text).strip() == textwrap.dedent(library[snippet]).strip(), (
            name,
            snippet,
        )


def test_euclid_chapter_exports_a_strict_certificate(tmp_path):
    result, html = render(tmp_path, "11-euclid.md")
    assert result.returncode == 0, result.stderr
    assert "euclid: True" in html
    assert (tmp_path / "euclid.logos").exists()
    checked = subprocess.run(
        [CHECKER, "check", "--strict", "euclid.logos"],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        check=True,
    )
    assert "Verified with 0 custom axioms" in checked.stdout
    assert "euclid" in checked.stdout


def test_euclid_chapter_recovers_from_the_constructed_number(tmp_path):
    source = (CHAPTERS / "11-euclid.md").read_text(encoding="utf-8")
    assert source.count("    m = f + 1") == 1
    broken = source.replace("    m = f + 1", "    m = f", 1)

    broken_dir = tmp_path / "broken"
    broken_dir.mkdir()
    _, html = render(broken_dir, "11-euclid.md", broken)
    assert not (broken_dir / "euclid.logos").exists()
    assert "needed by common_divisor" in html
    assert "factorial(n) + 1" in html
    assert html.count("factorial(n) = q * k") >= 2

    restored_dir = tmp_path / "restored"
    restored_dir.mkdir()
    result, html = render(restored_dir, "11-euclid.md", source)
    assert result.returncode == 0, result.stderr
    assert (restored_dir / "euclid.logos").exists()
    subprocess.run(
        [CHECKER, "check", "--strict", "euclid.logos"],
        cwd=restored_dir,
        capture_output=True,
        text=True,
        check=True,
    )


def test_parity_reports_the_wrong_witness(tmp_path):
    source = (CHAPTERS / "07-parity.md").read_text(encoding="utf-8")
    assert source.count("    return p.witness(i + j, total)") == 1
    broken = source.replace("    return p.witness(i + j, total)", "    return p.witness(i, total)", 1)
    _, html = render(tmp_path, "07-parity.md", broken)
    assert "the evidence does not prove the instantiated existential predicate" in html
    assert "expected: a + b = 2 * i" in html
    assert "got: a + b = 2 * (i + j)" in html
