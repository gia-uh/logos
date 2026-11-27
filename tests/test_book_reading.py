"""The installed wheel exposes the rendered book without a repository checkout."""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

from logos import book

ROOT = Path(__file__).resolve().parents[1]


def _fake_book(tmp_path: Path) -> Path:
    root = tmp_path / "book"
    (root / "site").mkdir(parents=True)
    (root / "site" / "index.html").write_text("<!doctype html><h1>Logos</h1>", encoding="utf-8")
    (root / "site" / "introduction.html").write_text("<h1>Introduction</h1>", encoding="utf-8")
    (root / "book.pdf").write_bytes(b"%PDF-1.4\n")
    (root / "manifest.json").write_text(json.dumps({"pages": 2, "format": 1}), encoding="utf-8")
    return root


def test_the_environment_can_point_at_a_rendered_book(monkeypatch, tmp_path):
    root = _fake_book(tmp_path)
    monkeypatch.setenv("LOGOS_BOOK", str(root))
    assert book.root() == root
    assert book.site() == root / "site"
    assert book.pdf() == root / "book.pdf"
    assert book.index() == root / "site" / "index.html"
    assert book.manifest()["pages"] == 2


def test_a_missing_book_names_the_fix(monkeypatch, tmp_path):
    monkeypatch.delenv("LOGOS_BOOK", raising=False)
    monkeypatch.setattr(book, "PACKAGE_BOOK", tmp_path / "missing-package")
    monkeypatch.setattr(book, "REPO_BOOK", tmp_path / "missing-checkout")
    with pytest.raises(book.BookNotInstalled, match="tools/package_reading.py"):
        book.root()


def test_the_cli_reports_the_installed_paths(monkeypatch, tmp_path):
    root = _fake_book(tmp_path)
    env = dict(os.environ, LOGOS_BOOK=str(root))
    result = subprocess.run(
        [sys.executable, "-m", "logos", "book", "--json"],
        cwd=tmp_path,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    data = json.loads(result.stdout)
    assert data["site"] == str(root / "site")
    assert data["pdf"] == str(root / "book.pdf")
    assert data["pages"] == 2


def test_the_cli_prints_the_pdf_and_the_site(monkeypatch, tmp_path):
    root = _fake_book(tmp_path)
    env = dict(os.environ, LOGOS_BOOK=str(root))
    pdf = subprocess.run(
        [sys.executable, "-m", "logos", "book", "--pdf"],
        cwd=tmp_path, env=env, capture_output=True, text=True, check=False,
    )
    site = subprocess.run(
        [sys.executable, "-m", "logos", "book", "--path"],
        cwd=tmp_path, env=env, capture_output=True, text=True, check=False,
    )
    assert pdf.returncode == 0 and pdf.stdout.strip() == str(root / "book.pdf")
    assert site.returncode == 0 and site.stdout.strip() == str(root / "site")


def test_the_top_level_module_points_at_the_book():
    result = subprocess.run(
        [sys.executable, "-m", "logos"], cwd=ROOT, capture_output=True, text=True, check=False
    )
    assert result.returncode == 0
    assert "python -m logos book" in result.stdout
