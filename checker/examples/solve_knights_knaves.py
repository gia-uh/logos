"""Describe and solve a Knights and Knaves puzzle, then export its proof."""
import argparse

from logos.domains.logic_puzzles import KnightsKnaves


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", help="path for the checked .logos proof")
    args = parser.parse_args()

    puzzle = KnightsKnaves()
    a, b = puzzle.entity("A"), puzzle.entity("B")
    a.says(a.is_knave() & b.is_knave())
    print(puzzle.solve())
    puzzle.export_proof(args.output)


if __name__ == "__main__":
    main()
