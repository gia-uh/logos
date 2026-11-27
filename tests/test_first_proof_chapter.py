"""Render the native English first chapter from the installed wheel.

The chapter is not tangled. Scriptorium runs its Python blocks directly, so the
test fails when `compose.check()` or `compose.inspect()` stops working.
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
SOURCE = BOOK / "first-proof.md"
SCRIPTORIUM = shutil.which("scriptorium")
CHECKER = shutil.which("logos")

pytestmark = pytest.mark.skipif(
    SCRIPTORIUM is None or CHECKER is None,
    reason="install Scriptorium and the Rust logos checker to render the chapter",
)


def render(tmp_path: Path, text: str | None = None) -> subprocess.CompletedProcess:
    page = tmp_path / "first-proof.md"
    page.write_text(SOURCE.read_text(encoding="utf-8") if text is None else text, encoding="utf-8")
    output = tmp_path / "first-proof.html"
    env = dict(os.environ)
    env["PATH"] = os.pathsep.join(
        [str(Path(CHECKER).parent), str(Path(sys.executable).parent), env.get("PATH", "")]
    )
    return subprocess.run(
        [SCRIPTORIUM, "render", page.name, "--html", "-o", str(output)],
        cwd=tmp_path,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )


def test_the_chapter_renders_a_compact_checked_quote_from_the_installed_wheel(tmp_path):
    source = SOURCE.read_text(encoding="utf-8")
    assert "export=" not in source
    assert "from subprocess import" not in source
    assert source.count("    return p.apply(q_to_r, have_q)") == 1

    # The renderer's python3 is the interpreter running this test, so the
    # chapter imports the installed wheel rather than the repository checkout.
    env = dict(os.environ)
    env["PATH"] = os.pathsep.join(
        [str(Path(CHECKER).parent), str(Path(sys.executable).parent), env.get("PATH", "")]
    )
    assert Path(shutil.which("python3", path=env["PATH"])).resolve() == Path(sys.executable).resolve()
    probe = subprocess.run(
        [sys.executable, "-c", "import logos; print(logos.__file__)"],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        check=True,
    )
    assert "site-packages" in probe.stdout
    assert str(BOOK.parent) not in probe.stdout

    result = render(tmp_path)
    assert result.returncode == 0, result.stderr
    html = (tmp_path / "first-proof.html").read_text(encoding="utf-8")
    assert "Traceback (most recent call last)" not in html
    assert "expected: Q" in html  # the authored failure example, not a crash

    quotes = re.findall(r"<blockquote\b.*?</blockquote>", html, re.S)
    assert len(quotes) == 1
    quote = quotes[0]
    assert not re.search(r"<h[1-6]\b", quote)
    assert "Author's claim (not checked)." in quote
    assert "Author's strategy (not checked)." in quote
    assert "Author's note (authored, not checked)." in quote
    assert "Checked result." in quote and "Uses zero custom axioms." in quote
    assert "Checked proof" not in quote
    assert "Domains and definitions" not in quote
    latex = " ".join(re.findall(r'data-latex="([^"]*)"', quote))
    assert r"\forall P \in \mathsf{Prop}" in latex
    assert r"P \implies R" in latex
    assert "We now have Q, the premise the second implication needs." in quote
    # Steps 7-9 only, never the full 14-step dump.
    for step in ("(7)", "(8)", "(9)"):
        assert step in quote
    assert "(10)" not in quote
    assert "(1)" not in quote


def test_a_broken_application_fails_the_native_chapter(tmp_path):
    source = SOURCE.read_text(encoding="utf-8")
    broken = source.replace(
        "    return p.apply(q_to_r, have_q)",
        "    return p.apply(q_to_r, given_p)",
        1,
    )
    result = render(tmp_path, broken)
    html = (tmp_path / "first-proof.html").read_text(encoding="utf-8")
    assert result.returncode != 0 or "Traceback (most recent call last)" in html
    assert "expected: Q" in html
    assert "got: P" in html
