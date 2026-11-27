"""Render the native English first chapter from the installed wheel.

The chapter is not tangled. Scriptorium runs its Python blocks directly, so the
test fails when `compose.check()` or `compose.inspect()` stops working. The
whole Markdown reading is embedded in a `::: proof` panel; the test compares it,
in order, with the same reading printed standalone.
"""
from __future__ import annotations

import importlib.util
import os
import re
import shutil
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

BOOK = Path(__file__).resolve().parents[1] / "book"
SOURCE = BOOK / "chapters" / "02-first-proof.md"
SCRIPTORIUM = shutil.which("scriptorium")
CHECKER = shutil.which("logos")

pytestmark = pytest.mark.skipif(
    SCRIPTORIUM is None or CHECKER is None,
    reason="install Scriptorium and the Rust logos checker to render the chapter",
)

SECTIONS = [
    "Author's commentary (not checked)",
    "Theorem",
    "Domains and definitions",
    "Custom axioms",
    "Proof",
    "Conclusion",
]
CLAIM = "If P implies Q and Q implies R, then P implies R."
STRATEGY = "Reach R through Q, the proposition both implications mention."
NOTE = "We now have Q, the premise the second implication needs."

STANDALONE = '''
import logos
from logos import Prop

@logos.theorem
def compose(P: Prop, Q: Prop, R: Prop):
    """If P implies Q and Q implies R, then P implies R."""
    return (P >> Q) >> ((Q >> R) >> (P >> R))

@compose.proof
def prove_compose(p, P, Q, R):
    """Reach R through Q, the proposition both implications mention."""
    p_to_q = p.assume(P >> Q)
    q_to_r = p.assume(Q >> R)
    given_p = p.assume(P)
    have_q = p.apply(p_to_q, given_p)
    p.note("We now have Q, the premise the second implication needs.")
    return p.apply(q_to_r, have_q)

compose.check()
print(compose.inspect())
'''


def _env() -> dict:
    env = dict(os.environ)
    env["PATH"] = os.pathsep.join(
        [str(Path(CHECKER).parent), str(Path(sys.executable).parent), env.get("PATH", "")]
    )
    return env


def _render(tmp_path: Path, text: str | None = None, *, html: bool = True) -> subprocess.CompletedProcess:
    page = tmp_path / "first-proof.md"
    page.write_text(SOURCE.read_text(encoding="utf-8") if text is None else text,
                    encoding="utf-8")
    output = tmp_path / ("first-proof.html" if html else "first-proof.pdf")
    command = [SCRIPTORIUM, "render", page.name, "-o", str(output)]
    if html:
        command.append("--html")
    return subprocess.run(command, cwd=tmp_path, env=_env(),
                          capture_output=True, text=True, check=False)


def _proof(html: str) -> str:
    match = re.search(r'<section class="proof">(.*?)</section>', html, re.S)
    assert match, "the chapter has no proof panel"
    return match.group(1)


def _normalise(html: str) -> str:
    """Compare content, not the glyph ids each math render happens to allocate."""
    return re.sub(r"MJX-\d+", "MJX-N", html).strip()


def _headings(proof: str) -> list[tuple[str, str]]:
    return [(tag, re.sub(r"<[^>]+>", "", text).strip())
            for tag, text in re.findall(r"<(h[1-6])[^>]*>(.*?)</\1>", proof, re.S)]


def test_the_chapter_embeds_the_whole_inspect_reading(tmp_path):
    source = SOURCE.read_text(encoding="utf-8")
    assert "export=" not in source
    assert "from subprocess import" not in source
    assert source.count("    return p.apply(q_to_r, have_q)") == 1
    assert "compact_reading" not in source
    assert "import re" not in source
    assert "reading = compose.inspect()" not in source
    assert source.count("::: proof") == 1
    assert "print(compose.inspect())" in source

    # The renderer's python3 is the interpreter running this test, so the
    # chapter imports the installed wheel rather than the repository checkout.
    env = _env()
    assert Path(shutil.which("python3", path=env["PATH"])).resolve() == Path(sys.executable).resolve()
    probe = subprocess.run(
        [sys.executable, "-c", "import logos; print(logos.__file__)"],
        cwd=tmp_path, capture_output=True, text=True, check=True,
    )
    assert "site-packages" in probe.stdout
    assert str(BOOK.parent) not in probe.stdout

    result = _render(tmp_path)
    assert result.returncode == 0, result.stderr
    html = (tmp_path / "first-proof.html").read_text(encoding="utf-8")
    assert "Traceback (most recent call last)" not in html
    assert "expected: Q" in html  # the authored failure example, not a crash

    proof = _proof(html)
    # The verifier's title is scoped below the chapter. No heading inside the
    # panel can be an h1 or h2: those belong to the book, not the reading.
    assert not re.search(r"<h[12]\b", proof)
    assert _headings(proof) == [
        ("h3", "Checked proof"),
        *[("h4", section) for section in SECTIONS],
    ]

    # The exact content the verifier printed, in source order.
    assert "Verified." in proof
    assert "logos-core-v1" in proof
    assert CLAIM in proof and STRATEGY in proof
    assert "Uses zero custom axioms." in proof
    assert "The conclusion follows from (14)." in proof
    latex = " ".join(re.findall(r'data-latex="([^"]*)"', proof))
    assert r"\forall P \in \mathsf{Prop}" in latex
    assert r"P \implies R" in latex

    markers = [f"<strong>({step})</strong>" for step in range(1, 15)]
    assert all(marker in proof for marker in markers)
    positions = [proof.index(marker) for marker in markers]
    assert positions == sorted(positions)
    assert proof.index(markers[6]) < proof.index(NOTE) < proof.index(markers[7])
    assert "Author's note (authored, not checked)." in proof


def test_the_same_markdown_renders_standalone_and_embedded(tmp_path):
    standalone = subprocess.run(
        [sys.executable, "-c", STANDALONE], cwd=tmp_path, env=_env(),
        capture_output=True, text=True, check=True,
    )
    assert standalone.stdout.startswith("# Checked proof\n")
    assert standalone.stdout.count("**(") == 14
    (tmp_path / "reading.md").write_text(standalone.stdout, encoding="utf-8")

    wrapper = textwrap.dedent('''\
        ---
        theme: book
        title: Standalone reading
        ---

        # Standalone reading

        ::: proof
        ```python {run echo=false}
        print(open("reading.md").read())
        ```
        :::
    ''')
    wrapper_result = _render(tmp_path, wrapper)
    assert wrapper_result.returncode == 0, wrapper_result.stderr
    wrapper_html = (tmp_path / "first-proof.html").read_text(encoding="utf-8")

    chapter_result = _render(tmp_path)
    assert chapter_result.returncode == 0, chapter_result.stderr
    chapter_html = (tmp_path / "first-proof.html").read_text(encoding="utf-8")

    assert _normalise(_proof(chapter_html)) == _normalise(_proof(wrapper_html))


def test_the_proof_never_becomes_a_chapter_in_the_toc(tmp_path):
    source = SOURCE.read_text(encoding="utf-8")
    with_toc = source.replace("\n# Writing Your First Proof", "\n::: toc\n:::\n\n# Writing Your First Proof", 1)
    result = _render(tmp_path, with_toc)
    assert result.returncode == 0, result.stderr
    html = (tmp_path / "first-proof.html").read_text(encoding="utf-8")

    entries = re.findall(r'<a class="toc-entry[^"]*"[^>]*>(.*?)</a>', html, re.S)
    joined = "".join(entries)
    assert "Writing Your First Proof" in joined
    assert "Checked proof" not in joined
    assert "Theorem" not in joined


@pytest.mark.skipif(
    importlib.util.find_spec("weasyprint") is None,
    reason="install scriptorium[pdf] to render the chapter's PDF",
)
def test_the_chapter_renders_the_same_reading_to_pdf(tmp_path):
    result = _render(tmp_path, html=False)
    assert result.returncode == 0, result.stderr
    pdf = tmp_path / "first-proof.pdf"
    assert pdf.stat().st_size > 10_000

    if shutil.which("pdftotext") is None:
        pytest.skip("install poppler-utils to read the PDF text")
    text = subprocess.run(["pdftotext", str(pdf), "-"], capture_output=True,
                          text=True, check=True).stdout
    assert "Traceback (most recent call last)" not in text
    for section in ["Checked proof", *SECTIONS]:
        assert section in text
    for step in range(1, 15):
        assert f"({step})" in text
    note_heading = text.index("Author's note (authored, not checked).", text.index("(7)"))
    assert text.index("(7)") < note_heading < text.index("(8)")
    assert "Uses zero custom axioms." in text
    assert "The conclusion follows from (14)." in text


def test_a_broken_application_fails_the_native_chapter(tmp_path):
    source = SOURCE.read_text(encoding="utf-8")
    broken = source.replace(
        "    return p.apply(q_to_r, have_q)",
        "    return p.apply(q_to_r, given_p)",
        1,
    )
    result = _render(tmp_path, broken)
    html = (tmp_path / "first-proof.html").read_text(encoding="utf-8")
    assert result.returncode != 0 or "Traceback (most recent call last)" in html
    assert "expected: Q" in html
    assert "got: P" in html
