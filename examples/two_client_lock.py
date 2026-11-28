#!/usr/bin/env python3
"""Build a two-client lock certificate, or replay its occupied-lock mutation."""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from logos.domains.transition_systems import FiniteTransitionSystem

IDLE = "idle"
CRITICAL = "critical"
FREE = "free"
START = (IDLE, IDLE, FREE)
A_INSIDE = (CRITICAL, IDLE, "A")
B_INSIDE = (IDLE, CRITICAL, "B")
BOTH_INSIDE = (CRITICAL, CRITICAL, "B")
INVARIANT = (START, A_INSIDE, B_INSIDE)
VIOLATION = (("A.acquire", A_INSIDE), ("B.acquire", BOTH_INSIDE))
UNIVERSE = tuple(product((IDLE, CRITICAL), (IDLE, CRITICAL), (FREE, "A", "B")))


def lock_model(*, occupied_acquire: bool = False) -> FiniteTransitionSystem:
    """Declare the model with one optional change to B's acquire guard."""
    transitions = {}
    for index, client in enumerate(("A", "B")):
        acquire, release = [], []
        for state in UNIVERSE:
            location, owner = state[index], state[2]
            if location == IDLE and (owner == FREE or (client == "B" and occupied_acquire)):
                target = list(state)
                target[index], target[2] = CRITICAL, client
                acquire.append((state, tuple(target)))
            if location == CRITICAL and owner == client:
                target = list(state)
                target[index], target[2] = IDLE, FREE
                release.append((state, tuple(target)))
        transitions[f"{client}.acquire"] = acquire
        transitions[f"{client}.release"] = release
    return FiniteTransitionSystem(
        UNIVERSE, (START,), transitions,
        safe=lambda state: state[:2] != (CRITICAL, CRITICAL),
    )


def main() -> None:
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--export", type=Path, metavar="FILE")
    mode.add_argument("--verify", type=Path, metavar="FILE")
    mode.add_argument("--replay", choices=("mutant", "correct"))
    args = parser.parse_args()
    model = lock_model(occupied_acquire=args.replay == "mutant")
    if args.export:
        receipt = model.export_safety(INVARIANT, args.export)
        print(f"Exported {args.export} (SHA-256 {receipt.artifact_sha256})")
    elif args.verify:
        receipt = model.verify_safety(INVARIANT, args.verify)
        print(f"Verified exact lock model and invariant (SHA-256 {receipt.artifact_sha256})")
    else:
        try:
            model.replay_violation(START, VIOLATION)
        except ValueError as error:
            parser.exit(1, f"{error}\n")
        print(START)
        for name, target in VIOLATION:
            print(f"  --{name}--> {target}")
        print("Mutual exclusion violated.")


if __name__ == "__main__":
    main()
