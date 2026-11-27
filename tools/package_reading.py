"""Copy the rendered book into the Python package for the release wheel.

Run after `tools/publish_book.py`. The generated directory is ignored by git;
a wheel built without it still installs, but has no offline reading.
"""
from __future__ import annotations

import hashlib
import json
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BOOK = ROOT / "book"
SITE = BOOK / "site"
PDF = BOOK / "book.pdf"
TARGET = ROOT / "logos" / "_book"


class PackagingError(RuntimeError):
    pass


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def package() -> tuple[int, int]:
    if not (SITE / "index.html").is_file():
        raise PackagingError("book/site is missing; render and publish the site first")
    if not PDF.is_file() or PDF.read_bytes()[:5] != b"%PDF-":
        raise PackagingError("book/book.pdf is missing or is not a PDF")
    if TARGET.exists():
        shutil.rmtree(TARGET)
    shutil.copytree(SITE, TARGET / "site")
    shutil.copyfile(PDF, TARGET / "book.pdf")
    files = [p for p in TARGET.rglob("*") if p.is_file()]
    pages = len([p for p in (TARGET / "site").glob("*.html") if p.name != "404.html"])
    manifest = {
        "format": 1,
        "site_url": "https://logos.uhgia.org/",
        "site": "site/index.html",
        "pdf": "book.pdf",
        "pages": pages,
        "files": len(files),
        "pdf_sha256": _sha256(TARGET / "book.pdf"),
        "index_sha256": _sha256(TARGET / "site" / "index.html"),
    }
    (TARGET / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return manifest["pages"], manifest["files"] + 1


def main() -> int:
    try:
        pages, files = package()
    except PackagingError as exc:
        print(f"packaging error: {exc}", file=sys.stderr)
        return 1
    print(f"packaged {pages} pages and {files} files into logos/_book")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
