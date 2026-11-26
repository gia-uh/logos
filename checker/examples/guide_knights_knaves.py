"""Describe A's utterance and a proposed conclusion, with optional proof export."""
import argparse

import logos
from logos import tactics as t
from logos.domains.logic_puzzles import KnightsKnaves


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", nargs="?", help="path for the checked .logos proof")
    args = parser.parse_args()

    puzzle = KnightsKnaves()
    a, b = puzzle.entity("A"), puzzle.entity("B")
    utterance = a.is_knave() & b.is_knave()
    claim = a.is_knave()
    a.says(utterance)

    print(f'A says, “{puzzle.describe(utterance)}”')
    print(f"Proposed conclusion — {puzzle.describe(claim)}")
    if args.output is None:
        return

    proof = puzzle.prove(claim, by=[
        puzzle.cases_on_role(a),
        [puzzle.use_statements(), puzzle.auto()],
        [t.assumption()],
    ])
    logos.export_proof(proof, args.output)
    print("Checked conditional proof from the role and utterance premises.")
    print(args.output)


if __name__ == "__main__":
    main()
