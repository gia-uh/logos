"""Read the Logos book that ships with the installed distribution.

The release wheel carries the rendered HTML book and its PDF under
``logos/_book``. A source checkout that has just rendered the book can read the
same files from ``book/``. The CLI entry is ``python -m logos book``; the Python
entry is ``logos.book``.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import webbrowser
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

PACKAGE_BOOK = Path(__file__).resolve().parent / "_book"
REPO_BOOK = Path(__file__).resolve().parents[1] / "book"


class BookNotInstalled(RuntimeError):
    """The distribution has no offline book and no rendered checkout."""


def _is_book(root: Path) -> bool:
    return (root / "site" / "index.html").is_file() and (root / "book.pdf").is_file()


def root() -> Path:
    """The directory holding ``site/`` and ``book.pdf``."""
    override = os.environ.get("LOGOS_BOOK")
    if override:
        candidate = Path(override).expanduser()
        if not _is_book(candidate):
            raise BookNotInstalled(f"LOGOS_BOOK={candidate} does not hold site/index.html and book.pdf")
        return candidate
    for candidate in (PACKAGE_BOOK, REPO_BOOK):
        if _is_book(candidate):
            return candidate
    raise BookNotInstalled(
        "this distribution has no bundled book; render book/scriptorium.yaml and run "
        "tools/package_reading.py, or install the release wheel"
    )


def site() -> Path:
    """The directory that holds ``index.html`` and the offline pages."""
    return root() / "site"


def pdf() -> Path:
    """The downloadable, self-contained PDF."""
    return root() / "book.pdf"


def index() -> Path:
    """The book's home page."""
    return site() / "index.html"


def manifest() -> dict:
    """The packaged book's metadata, or an empty mapping for a checkout render."""
    path = root() / "manifest.json"
    if not path.is_file():
        return {}
    return json.loads(path.read_text(encoding="utf-8"))


def _page_count() -> int:
    return len([p for p in site().glob("*.html") if p.name not in ("404.html",)])


def serve(host: str = "127.0.0.1", port: int = 0) -> None:
    """Serve the offline pages on localhost until interrupted."""
    handler = lambda *args, **kwargs: SimpleHTTPRequestHandler(  # noqa: E731
        *args, directory=str(site()), **kwargs
    )
    httpd = ThreadingHTTPServer((host, port), handler)
    address, actual = httpd.server_address[:2]
    print(f"Serving the Logos book at http://{address}:{actual}/ (Ctrl-C to stop)")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print()
    finally:
        httpd.server_close()


def _summary() -> dict:
    return {
        "site": str(site()),
        "pdf": str(pdf()),
        "pages": _page_count(),
        "manifest": manifest(),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="python -m logos book",
        description="Read the installed Logos book offline.",
    )
    output = parser.add_mutually_exclusive_group()
    output.add_argument("--json", action="store_true", help="print the paths and page count as JSON")
    output.add_argument("--path", action="store_true", help="print the directory of HTML pages")
    output.add_argument("--pdf", action="store_true", help="print the path of the downloadable PDF")
    output.add_argument("--open", action="store_true", help="open the home page in the default browser")
    output.add_argument("--serve", action="store_true", help="serve the pages on localhost")
    parser.add_argument("--host", default="127.0.0.1", help="address for --serve (default 127.0.0.1)")
    parser.add_argument("--port", type=int, default=0, help="port for --serve (default: choose one)")
    args = parser.parse_args(argv)
    try:
        if args.json:
            print(json.dumps(_summary(), ensure_ascii=False, sort_keys=True))
        elif args.path:
            print(site())
        elif args.pdf:
            print(pdf())
        elif args.open:
            webbrowser.open(index().as_uri())
        elif args.serve:
            serve(args.host, args.port)
        else:
            data = _summary()
            print("Logos book")
            print(f"  pages  {data['pages']}")
            print(f"  site   {data['site']}")
            print(f"  pdf    {data['pdf']}")
            print("Use --open, --serve, --pdf or --json.")
    except BookNotInstalled as exc:
        print(f"logos book: {exc}", file=sys.stderr)
        return 1
    except OSError as exc:
        print(f"logos book: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
