"""Render the finite-graph, binary-search and production-contract chapters.

These tests exercise the pages added after the number theory sequence. They use
the same installed-wheel renderer as ``test_english_book`` and run the exported
certificates with the standalone Rust checker.
"""
from __future__ import annotations

import importlib.util
import re
import subprocess
import sys
import textwrap

import pytest

from tests.test_english_book import CHAPTERS, CHECKER, SCRIPTORIUM, environment, render

pytestmark = pytest.mark.skipif(
    SCRIPTORIUM is None or CHECKER is None,
    reason="install Scriptorium and the Rust logos checker to render the book",
)


def production_source() -> str:
    text = (CHAPTERS / "14-production-contract.md").read_text(encoding="utf-8")
    match = re.search(r"PUNYCODE_ADAPT = '''\\\n(.*?)\n'''", text, re.S)
    assert match is not None
    return match.group(1)


def test_finite_graph_reports_a_descending_edge(tmp_path):
    source = (CHAPTERS / "12-finite-graph.md").read_text(encoding="utf-8")
    broken = source.replace("| ((u == 3) & (v == 4))", "| ((u == 3) & (v == 1))", 1)
    _, html = render(tmp_path, "12-finite-graph.md", broken)
    assert "linear arithmetic could not derive the goal" in html
    assert "expected goal: u &lt; v" in html
    assert "u = 3" in html


def test_binary_search_exports_a_strict_certificate(tmp_path):
    result, _ = render(tmp_path, "13-binary-search.md")
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
    source = (CHAPTERS / "13-binary-search.md").read_text(encoding="utf-8")
    broken = source.replace(
        "mid = (low + high) // 2", "mid = (low + high + 1) // 2", 1
    )
    _, html = render(tmp_path, "13-binary-search.md", broken)
    assert "loop0.preserve" in html
    assert "cannot prove disjunction" in html
    assert not (tmp_path / "binary_search.logos").exists()


def test_binary_search_weakened_invariant_is_refused(tmp_path):
    source = (CHAPTERS / "13-binary-search.md").read_text(encoding="utf-8")
    assert source.count("& (low <= high)") == 1
    broken = source.replace("& (low <= high)", "& (low < high)", 1)
    _, html = render(tmp_path, "13-binary-search.md", broken)
    assert "cannot prove order atom high &lt; high" in html
    assert not (tmp_path / "binary_search.logos").exists()


def test_binary_search_missing_precondition_needs_a_counterexample(tmp_path):
    source = (CHAPTERS / "13-binary-search.md").read_text(encoding="utf-8")
    broken = source.replace(
        "requires=logos.sorted(xs),", "requires=logos.lit(True),", 1
    )
    _, html = render(tmp_path, "13-binary-search.md", broken)
    assert "main: no proof found for sorted(xs)" in html
    assert not (tmp_path / "binary_search.logos").exists()


def test_binary_search_executable_counterexample():
    path = CHAPTERS.parent.parent / "examples" / "binary_search.py"
    spec = importlib.util.spec_from_file_location("book_binary_search", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules["book_binary_search"] = module
    spec.loader.exec_module(module)
    xs = [2, 0, 1]
    result = module.binary_search(xs, 2)
    assert result == -1
    assert 2 in xs


def test_production_chapter_exports_a_strict_certificate(tmp_path):
    result, _ = render(tmp_path, "14-production-contract.md")
    assert result.returncode == 0, result.stderr
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


def test_production_mutation_is_refused(tmp_path):
    source = (CHAPTERS / "14-production-contract.md").read_text(encoding="utf-8")
    broken = source.replace(
        "bias = divisions + (36 * delta // (delta + 38))",
        "bias = divisions - 1",
        1,
    )
    _, html = render(tmp_path, "14-production-contract.md", broken)
    assert "loop0.exit" in html
    assert "cannot prove order atom 0 &lt;= divisions - 1" in html
    assert not (tmp_path / "adapt.logos").exists()


def test_production_source_drift_is_refused(tmp_path):
    path = tmp_path / "punycode_adapt.py"
    path.write_text(production_source())
    script = tmp_path / "drift.py"
    script.write_text(
        textwrap.dedent(
            """\
            import importlib.util
            import sys
            from pathlib import Path
            import logos
            from logos.expr import Lit, Var

            path = Path(__file__).with_name("punycode_adapt.py")
            spec = importlib.util.spec_from_file_location("drift_adapt", path)
            module = importlib.util.module_from_spec(spec)
            sys.modules["drift_adapt"] = module
            spec.loader.exec_module(module)

            @logos.theorem(about=module.adapt)
            def drift(delta, first, numchars, *, result):
                divisions = Var("divisions", int)
                return logos.program_contract(
                    requires=(Lit(0) <= delta) & (Lit(0) < numchars),
                    ensures=(Lit(0) <= result),
                    invariant=(Lit(0) <= delta) & (Lit(0) <= divisions),
                    variant=delta,
                )

            drift.check()
            path.write_text(path.read_text().replace("455", "456"))
            try:
                drift.check()
            except logos.LogosProofError as error:
                print("refused:", error)
                raise SystemExit(0)
            raise SystemExit(1)
            """
        )
    )
    result = subprocess.run(
        [sys.executable, str(script)],
        cwd=tmp_path,
        env=environment(),
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stderr
    assert "refused:" in result.stdout
    assert "does not match the imported code object" in result.stdout
