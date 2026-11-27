"""Render the public API reference chapter from the source tree.

The chapter is generated so it cannot describe a class or function that no
longer exists. ``--check`` compares the file with a fresh render; the test suite
and the docs gate run it that way, and ``--write`` updates it after a public
change. The extraction mirrors the rift rule in ``.rift.yaml``: every
non-underscore class and every public function or method.
"""
from __future__ import annotations

import argparse
import ast
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / "logos"
CHAPTER = ROOT / "book" / "chapters" / "16-api-reference.md"

CLASS = re.compile(r"^class ([A-Za-z]\w*)")
FUNCTION = re.compile(r"^def ([a-z]\w*)|^    def ([a-z]\w*)\((?:self|cls)\b")

FRONT = """---
theme: book
title: Public API Reference
stem: api-reference
---

# Public API Reference

This chapter is generated from the installed source by
`tools/generate_api_reference.py`. It exists so every public class, function and
method has a named place in the book. The rift rule in `.rift.yaml` reports a
class missing from the chapters as an error; the reference test fails when this
page and the source disagree.

“Public” here means a non-underscore top-level class, or a non-underscore
function or a method declared with `self` or `cls`. Names that begin with an
underscore are implementation details, even when another module imports them.

## Classes

| Class | Module | Purpose |
| --- | --- | --- |
"""

MIDDLE = """
## Functions and methods

| Name | Module | Purpose |
| --- | --- | --- |
"""

TAIL = """
## Where to read next

The [Developer Guide](15-developer-guide.md) shows how these pieces fit when
you extend the checked language. The [proof format](../docs/portable-proof-format.md)
states the bytes an independent recipient verifies. For a use-case path through
the same API, start at the introduction and follow the chapters in order.
"""


def _docstring(node: ast.AST) -> str:
    text = ast.get_docstring(node) or ""
    first = next((line.strip() for line in text.splitlines() if line.strip()), "")
    return first.replace("|", "\\|") or "—"


def _module_name(path: Path) -> str:
    relative = path.relative_to(ROOT).with_suffix("")
    parts = list(relative.parts)
    if parts[-1] == "__init__":
        parts = parts[:-1]
    return ".".join(parts)


def _entries():
    classes = []
    functions = []
    for path in sorted(PACKAGE.rglob("*.py")):
        if "__pycache__" in path.parts:
            continue
        source = path.read_text(encoding="utf-8")
        module = _module_name(path)
        tree = ast.parse(source)
        for node in tree.body:
            if isinstance(node, ast.ClassDef):
                if not node.name.startswith("_"):
                    classes.append((node.name, module, _docstring(node)))
                for child in node.body:
                    if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        if child.name.startswith("_"):
                            continue
                        arguments = child.args.args
                        if arguments and arguments[0].arg in ("self", "cls"):
                            functions.append(
                                (child.name, f"{module}.{node.name}", _docstring(child))
                            )
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if not node.name.startswith("_"):
                    functions.append((node.name, module, _docstring(node)))
    return classes, functions


def render() -> str:
    classes, functions = _entries()
    lines = [FRONT]
    for name, module, purpose in classes:
        lines.append(f"| `{name}` | `{module}` | {purpose} |\n")
    lines.append(MIDDLE)
    for name, module, purpose in functions:
        lines.append(f"| `{name}` | `{module}` | {purpose} |\n")
    lines.append(TAIL)
    return "".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="update the chapter")
    options = parser.parse_args()
    rendered = render()
    if options.write:
        CHAPTER.write_text(rendered, encoding="utf-8")
        print(f"wrote {CHAPTER.relative_to(ROOT)}")
        return 0
    current = CHAPTER.read_text(encoding="utf-8") if CHAPTER.exists() else ""
    if current != rendered:
        print(f"{CHAPTER.relative_to(ROOT)} is stale; run {Path(__file__).name} --write")
        return 1
    print(f"{CHAPTER.relative_to(ROOT)} matches the source")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
