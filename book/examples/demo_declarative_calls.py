"""Check the chapter's declarative examples and write the caller's certificate.

Run from any directory with ``python book/examples/demo_declarative_calls.py``.
The driver imports the module the chapter tangles; it is not a second copy.
"""
import logos
from declarative_calls import first, first_or_zero


def main() -> None:
    first.check()
    first_or_zero.check()
    print("first:", first.certified)
    print("first_or_zero:", first_or_zero.certified)
    print("obligations:", ", ".join(first_or_zero.program.obligations))
    logos.export_proof(first_or_zero, "first_or_zero.logos")
    print("certificate: first_or_zero.logos")


if __name__ == "__main__":
    main()
