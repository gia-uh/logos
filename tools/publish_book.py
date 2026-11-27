"""Finish the rendered book site and check the published surface.

The Scriptorium docs renderer writes the pages, search index and sitemap. GitHub
Pages also needs the custom domain, a PDF at a stable URL, redirects for the old
Quarto routes, and a robots file. This script adds those files and fails when a
redirect points at a page or section that the render did not produce.

Run it after both `scriptorium render ... --only site` and
`scriptorium render ... --only print`.
"""
from __future__ import annotations

import json
import os
import shutil
import sys
from html import escape
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
BOOK = ROOT / "book"
SITE = BOOK / "site"
PDF = BOOK / "book.pdf"
CNAME = BOOK / "CNAME"
REDIRECTS = BOOK / "redirects.json"


class PublicationError(RuntimeError):
    pass


def _page_and_anchor(target: str) -> tuple[str, str | None]:
    page, _, anchor = target.partition("#")
    return page, anchor or None


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise PublicationError(message)


def _redirect_html(route: dict, site_url: str) -> str:
    page, anchor = _page_and_anchor(route["to"])
    source = SITE / route["from"]
    target = Path(os.path.relpath(SITE / page, source.parent)).as_posix()
    if anchor:
        target_with_anchor = f"{target}#{anchor}"
    else:
        target_with_anchor = target
    canonical = site_url.rstrip("/") + "/" + page
    mapping = json.dumps(route.get("anchors") or {}, ensure_ascii=False, sort_keys=True)
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Redirecting to the Logos book</title>
<link rel="canonical" href="{escape(canonical)}">
<meta name="robots" content="noindex">
<meta http-equiv="refresh" content="0; url={escape(target_with_anchor)}">
<script>
(function () {{
  var target = {json.dumps(target)};
  var anchors = {mapping};
  var old = decodeURIComponent(location.hash.replace(/^#/, ""));
  if (old) target += "#" + (Object.prototype.hasOwnProperty.call(anchors, old) ? anchors[old] : old);
  location.replace(target);
}})();
</script>
</head>
<body>
<p>This page moved to <a href="{escape(target_with_anchor)}">the Logos book</a>.</p>
</body>
</html>
"""


def _check_target(route: dict) -> None:
    page, anchor = _page_and_anchor(route["to"])
    target = SITE / page
    _require(target.is_file(), f"{route['from']}: target page {page!r} was not rendered")
    html = target.read_text(encoding="utf-8")
    if anchor:
        _require(f'id="{anchor}"' in html, f"{route['from']}: target section #{anchor} is missing from {page}")
    for old, new in (route.get("anchors") or {}).items():
        _require(isinstance(new, str) and f'id="{new}"' in html,
                 f"{route['from']}#{old}: mapped section #{new} is missing from {page}")


class _Links(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.links: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        for name, value in attrs:
            if name in ("href", "src") and value:
                self.links.append(value)


def _check_links() -> int:
    missing: list[str] = []
    checked = 0
    for page in SITE.rglob("*.html"):
        parser = _Links()
        parser.feed(page.read_text(encoding="utf-8"))
        for link in parser.links:
            parts = urlsplit(link)
            if parts.scheme or parts.netloc or not parts.path:
                continue
            if link.startswith(("mailto:", "tel:", "javascript:", "data:")):
                continue
            target = (page.parent / unquote(parts.path)).resolve()
            checked += 1
            if not target.exists():
                missing.append(f"{page.relative_to(SITE)} -> {link}")
    _require(not missing, "broken internal links: " + "; ".join(missing[:5]))
    return checked


def publish() -> tuple[int, int, int]:
    _require(SITE.is_dir(), "book/site does not exist; render the site first")
    _require(PDF.is_file(), "book/book.pdf does not exist; render the print output first")
    _require(PDF.read_bytes()[:5] == b"%PDF-", f"{PDF} is not a PDF")
    _require(CNAME.is_file(), "book/CNAME does not exist")
    data = json.loads(REDIRECTS.read_text(encoding="utf-8"))
    site_url = str(data.get("site") or "").rstrip("/") + "/"

    shutil.copyfile(CNAME, SITE / "CNAME")
    shutil.copyfile(PDF, SITE / "book.pdf")
    (SITE / ".nojekyll").write_text("", encoding="utf-8")
    (SITE / "robots.txt").write_text(
        f"User-agent: *\nAllow: /\nSitemap: {site_url}sitemap.xml\n", encoding="utf-8"
    )

    routes = data.get("routes") or []
    seen: set[str] = set()
    for route in routes:
        _require(isinstance(route, dict), "each redirect must be an object")
        source, target = route.get("from"), route.get("to")
        _require(isinstance(source, str) and source.endswith(".html"), f"bad redirect source {source!r}")
        _require(isinstance(target, str) and (target.endswith(".html") or "#" in target),
                 f"bad redirect target {target!r}")
        _require(source not in seen, f"duplicate redirect source {source!r}")
        seen.add(source)
        _require(source != _page_and_anchor(target)[0], f"redirect {source!r} points at itself")
        _check_target(route)
        destination = SITE / source
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(_redirect_html(route, site_url), encoding="utf-8")

    home = (SITE / "index.html").read_text(encoding="utf-8")
    _require("Logos" in home, "index.html does not name the book")
    _require("book.pdf" in home, "index.html does not link the downloadable PDF")
    sitemap = (SITE / "sitemap.xml").read_text(encoding="utf-8")
    _require(f"<loc>{site_url}</loc>" in sitemap, "sitemap does not list the homepage")
    _require((SITE / "public-api-reference.html").is_file(), "the API reference page is missing")
    _require((SITE / "search.json").is_file(), "the search index is missing")
    links = _check_links()
    return len(routes), len([p for p in SITE.rglob("*.html") if p.is_file()]), links


def main() -> int:
    try:
        redirects, pages, links = publish()
    except PublicationError as exc:
        print(f"publication error: {exc}", file=sys.stderr)
        return 1
    print(f"published {pages} HTML pages, {redirects} Quarto redirects, {links} internal links, PDF and CNAME")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
