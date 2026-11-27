"""The Developer Guide renders from the installed wheel and matches the module.

The chapter quotes the interval domain section by section. This test compares
every quote with the source, renders both new chapters, replays the exported
certificate and regenerates the API reference in memory.
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
        "overlap_self: True",
        "common_point_by_tactic: True",
        "interval: no linear certificate for",
        "interval: expected an overlap after unfolding",
        "zero custom axioms: True",
        "certificate: intervals.logos",
    ):
        assert marker in html, marker
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


def test_the_reference_renders_and_names_every_public_entry(tmp_path):
    result, html = render(tmp_path, REFERENCE)
    assert result.returncode == 0, result.stderr
    assert "Traceback (most recent call last)" not in html
    assert "Classes" in html and "Functions and methods" in html
    from tools.generate_api_reference import _entries

    classes, functions = _entries()
    for name, _, _ in classes:
        assert name in html, name
    for name, _, _ in functions:
        assert name in html, name


def test_the_reference_matches_a_fresh_render():
    from tools.generate_api_reference import render as generate

    current = (CHAPTERS / REFERENCE).read_text(encoding="utf-8")
    assert current == generate(), "book/chapters/15-api-reference.md is stale"
