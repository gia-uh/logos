"""Check the chapter's binary search and write its certificate.

Run from any directory with ``python book/examples/demo_binary_search.py``.
The driver imports the module the chapter tangles; it is not a second copy.
"""
import logos
from binary_search import binary_search


def main() -> None:
    binary_search.check()
    print("binary_search:", binary_search.certified)
    print("obligations:", ", ".join(binary_search.program.obligations))
    logos.export_proof(binary_search, "binary_search.logos")
    print("certificate: binary_search.logos")


if __name__ == "__main__":
    main()
