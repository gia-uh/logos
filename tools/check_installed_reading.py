"""Check that an installed wheel carries a readable copy of the book.

Run from a directory outside the repository, with the wheel installed and no
Python path pointing at the checkout. This is the release-style check; it fails
when the build silently dropped ``logos/_book``.
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import logos.book as book


def main() -> int:
    site = book.site()
    pdf = book.pdf()
    assert (site / "index.html").is_file(), "the bundled site has no index.html"
    assert (site / "search.json").is_file(), "the bundled site has no search index"
    assert pdf.is_file() and pdf.read_bytes()[:5] == b"%PDF-", "the bundled PDF is missing"
    assert "site-packages" in str(site) or "dist-packages" in str(site), f"reading came from {site}"
    data = json.loads(
        subprocess.run(
            [sys.executable, "-m", "logos", "book", "--json"],
            check=True,
            capture_output=True,
            text=True,
        ).stdout
    )
    assert data["site"] == str(site)
    assert data["pdf"] == str(pdf)
    assert data["pages"] >= 15
    manifest = book.manifest()
    assert manifest.get("pdf_sha256") == __import__("hashlib").sha256(pdf.read_bytes()).hexdigest()
    print(f"installed reading: {data['pages']} pages, PDF {pdf.stat().st_size} bytes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
