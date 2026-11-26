"""Guide a proof that A is a knave, then export the checked evidence."""
import argparse

import logos
from logos import tactics as t
from logos.domains.logic_puzzles import KnightsKnaves


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", help="path for the checked .logos proof")
    args = parser.parse_args()

    puzzle = KnightsKnaves()
    a, b = puzzle.entity("A"), puzzle.entity("B")
    a.says(a.is_knave() & b.is_knave())

    proof = puzzle.prove(a.is_knave(), by=[
        puzzle.cases_on_role(a),
        [puzzle.use_statements(), puzzle.auto()],
        [t.assumption()],
    ])
    logos.export_proof(proof, args.output)
    print(args.output)


if __name__ == "__main__":
    main()
