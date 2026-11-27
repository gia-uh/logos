"""`python -m logos book`: read the installed book without importing the library."""
from __future__ import annotations

import sys

from logos.book import main as book_main

USAGE = "usage: python -m logos book [--json|--path|--pdf|--open|--serve]"


def main(argv: list[str] | None = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    if not args or args[0] in ("-h", "--help"):
        print(USAGE)
        return 0
    if args[0] != "book":
        print(USAGE, file=sys.stderr)
        return 2
    return book_main(args[1:])


if __name__ == "__main__":
    raise SystemExit(main())
