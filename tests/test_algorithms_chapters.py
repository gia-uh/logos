"""Render the binary-search and production-contract chapters.

These tests exercise the algorithm pages after the number theory sequence. They
use the same installed-wheel renderer as ``test_english_book`` and run the
exported certificates with the standalone Rust checker.
"""
from __future__ import annotations

import importlib.util
import re
import subprocess
import sys

import pytest

from tests.test_english_book import CHAPTERS, CHECKER, SCRIPTORIUM, environment, render

pytestmark = pytest.mark.skipif(
    SCRIPTORIUM is None or CHECKER is None,
    reason="install Scriptorium and the Rust logos checker to render the book",
)


EXPORT = re.compile(r"```python \{export=([\w./-]+)\}\n(.*?)\n```", re.S)


def exported_blocks(name: str) -> dict[str, str]:
    """The files a chapter tangles, joined the way Scriptorium joins blocks."""
    text = (CHAPTERS / name).read_text(encoding="utf-8")
    files: dict[str, list[str]] = {}
    for path, body in EXPORT.findall(text):
        files.setdefault(path, []).append(body)
    return {path: "\n".join(blocks).rstrip("\n") + "\n" for path, blocks in files.items()}


def production_source() -> str:
    return exported_blocks("13-production-contract.md")["examples/punycode_adapt.py"]


def test_binary_search_exports_a_strict_certificate(tmp_path):
    result, _ = render(tmp_path, "12-binary-search.md")
    assert result.returncode == 0, result.stderr
    assert (tmp_path / "binary_search.logos").exists()
    checked = subprocess.run(
        [CHECKER, "check", "--strict", "binary_search.logos"],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        check=True,
    )
    assert "Verified with 0 custom axioms" in checked.stdout
    assert "binary_search" in checked.stdout


def test_binary_search_shifted_midpoint_is_refused(tmp_path):
    source = (CHAPTERS / "12-binary-search.md").read_text(encoding="utf-8")
    broken = source.replace(
        "mid = (low + high) // 2", "mid = (low + high + 1) // 2", 1
    )
    _, html = render(tmp_path, "12-binary-search.md", broken)
    assert "loop0.preserve.bounds" in html
    assert "cannot prove order atom" in html
    assert not (tmp_path / "binary_search.logos").exists()


def test_binary_search_weakened_invariant_is_refused(tmp_path):
    source = (CHAPTERS / "12-binary-search.md").read_text(encoding="utf-8")
    assert source.count("& (low <= high)") == 1
    broken = source.replace("& (low <= high)", "& (low < high)", 1)
    _, html = render(tmp_path, "12-binary-search.md", broken)
    assert "loop0.preserve.bounds" in html
    assert "cannot prove order atom high &lt; high" in html
    assert not (tmp_path / "binary_search.logos").exists()


def test_binary_search_missing_precondition_needs_a_counterexample(tmp_path):
    source = (CHAPTERS / "12-binary-search.md").read_text(encoding="utf-8")
    broken = source.replace(
        "def ordered(xs):\n    return logos.sorted(xs)",
        "def ordered(xs):\n    return 0 <= logos.length(xs)",
        1,
    )
    _, html = render(tmp_path, "12-binary-search.md", broken)
    assert "main: no proof found for sorted(xs)" in html
    assert not (tmp_path / "binary_search.logos").exists()


def test_binary_search_executable_counterexample():
    path = CHAPTERS.parent / "examples" / "binary_search.py"
    spec = importlib.util.spec_from_file_location("book_binary_search", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules["book_binary_search"] = module
    spec.loader.exec_module(module)
    xs = [2, 0, 1]
    result = module.binary_search(xs, 2)
    assert result == -1
    assert 2 in xs


def test_production_chapter_exports_a_strict_certificate(tmp_path):
    result, html = render(tmp_path, "13-production-contract.md")
    assert result.returncode == 0, result.stderr
    assert "halving_total_nonnegative: True" in html
    assert (tmp_path / "adapt.logos").exists()
    checked = subprocess.run(
        [CHECKER, "check", "--strict", "adapt.logos"],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        check=True,
    )
    assert "Verified with 0 custom axioms" in checked.stdout
    assert "adapt" in checked.stdout


def test_production_body_matches_the_standard_library(tmp_path):
    import encodings.punycode

    path = tmp_path / "punycode_adapt.py"
    path.write_text(production_source())
    spec = importlib.util.spec_from_file_location("book_punycode_adapt", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    ours = module.adapt.__code__
    theirs = encodings.punycode.adapt.__code__
    fields = (
        "co_argcount",
        "co_posonlyargcount",
        "co_kwonlyargcount",
        "co_nlocals",
        "co_flags",
        "co_code",
        "co_names",
        "co_varnames",
        "co_freevars",
        "co_cellvars",
        "co_consts",
    )
    assert all(getattr(ours, field) == getattr(theirs, field) for field in fields)
    for adapt in (module.adapt, encodings.punycode.adapt):
        assert (adapt(72, 1, 1), adapt(72, 0, 1)) == (0, 23)


def test_production_mutation_is_refused(tmp_path):
    source = (CHAPTERS / "13-production-contract.md").read_text(encoding="utf-8")
    broken = source.replace(
        "bias = divisions + (36 * delta // (delta + 38))",
        "bias = divisions - 1",
        1,
    )
    _, html = render(tmp_path, "13-production-contract.md", broken)
    assert "loop0.exit" in html
    assert "cannot prove order atom 0 &lt;= divisions - 1" in html
    assert not (tmp_path / "adapt.logos").exists()


def run_production_declaration(tmp_path, body, commands):
    chapter = (CHAPTERS / "13-production-contract.md").read_text(encoding="utf-8")
    declaration = chapter.split("```python {run}\n", 1)[1].split("```", 1)[0]
    examples = tmp_path / "examples"
    examples.mkdir()
    (examples / "punycode_adapt.py").write_text(body, encoding="utf-8")
    script = tmp_path / "prove_adapt.py"
    script.write_text(declaration + commands, encoding="utf-8")
    return subprocess.run(
        [sys.executable, "-B", str(script)],
        cwd=tmp_path,
        env=environment(),
        capture_output=True,
        text=True,
    )


def test_production_mutation_binds_fresh_and_returns_negative(tmp_path):
    changed_body = production_source().replace(
        "bias = divisions + (36 * delta // (delta + 38))", "bias = divisions - 1"
    )
    result = run_production_declaration(
        tmp_path,
        changed_body,
        """
print(adapt(0, 0, 1), adapt(0, 1, 1))
adapt_bias_nonnegative.check()
logos.export_proof(adapt_bias_nonnegative, "mutated.logos")
""",
    )
    assert result.stdout.strip() == "-1 -1"
    assert result.returncode != 0
    assert result.stderr.splitlines()[-1].startswith(
        "logos.proofs.ProofSearchError: loop0.exit: cannot prove order atom 0 <= divisions - 1"
    )
    assert not (tmp_path / "mutated.logos").exists()


def test_production_source_drift_is_refused(tmp_path):
    result = run_production_declaration(
        tmp_path,
        production_source(),
        """
from pathlib import Path

adapt_bias_nonnegative.check()
assert adapt_bias_nonnegative.receipt is not None
path = Path("examples/punycode_adapt.py")
path.write_text(path.read_text().replace("delta > 455", "delta > 456"))
assert adapt_bias_nonnegative.receipt is None
operations = (
    adapt_bias_nonnegative.check,
    lambda: logos.export_proof(adapt_bias_nonnegative, "stale.logos"),
)
for operation in operations:
    try:
        operation()
    except logos.LogosProofError as error:
        print(error)
    else:
        raise AssertionError("stale source accepted")
""",
    )
    assert result.returncode == 0, result.stderr
    diagnostics = result.stdout.splitlines()
    assert len(diagnostics) == 2
    for line in diagnostics:
        assert line.startswith("source of 'adapt' in ")
        assert line.endswith(
            "does not match the imported code object; "
            "the module is stale or the file changed after import; "
            "reimport it before declaring the theorem"
        )
    assert not (tmp_path / "stale.logos").exists()


@pytest.mark.parametrize(
    "name,path",
    [
        ("12-binary-search.md", "examples/binary_search.py"),
        ("12-binary-search.md", "examples/declarative_calls.py"),
        ("13-production-contract.md", "examples/punycode_adapt.py"),
        ("13-production-contract.md", "examples/halving_total.py"),
    ],
)
def test_book_examples_are_the_generated_modules(name, path):
    committed = (CHAPTERS.parent / path).read_text(encoding="utf-8")
    assert exported_blocks(name)[path] == committed


def test_book_examples_are_imported_normally():
    binary = (CHAPTERS / "12-binary-search.md").read_text(encoding="utf-8")
    punycode = (CHAPTERS / "13-production-contract.md").read_text(encoding="utf-8")
    assert "from examples.binary_search import binary_search" in binary
    assert "from examples.binary_search import main" in binary
    assert "from examples.declarative_calls import main" in binary
    assert "from examples.declarative_calls import first" in binary
    assert "from examples.punycode_adapt import adapt" in punycode
    for text in (binary, punycode):
        assert "importlib" not in text
        assert "tempfile" not in text
        assert "write_text(" not in text
        assert "= '''" not in text
