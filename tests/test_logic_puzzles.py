import json
import subprocess

import pytest

import logos
from logos.domains import _finite
from logos.domains.logic_puzzles import KnightsKnaves


@pytest.mark.parametrize(("describe", "expected"), [
    (lambda a, b: a.says(a.is_knave() & b.is_knave()), {"A": "knave", "B": "knight"}),
    # A says they differ. B says A is a knave. The second statement requires
    # different roles, so A is truthful and B is lying.
    (lambda a, b: (a.says(~(a.is_knight() >> b.is_knight()) | ~(b.is_knight() >> a.is_knight())),
                   b.says(a.is_knave())), {"A": "knight", "B": "knave"}),
    # A lies because a contradiction is always false. B's two observations
    # are both true once A lies. The final negation has open atoms in some cases.
    (lambda a, b: (a.says(a.is_knave() & ~a.is_knave()),
                   b.says(~(a.is_knight() | logos.lit(False))).says(a.is_knave())),
     {"A": "knave", "B": "knight"}),
])
def test_unique_assignment_and_strict_replay(tmp_path, describe, expected):
    puzzle = KnightsKnaves()
    a, b = puzzle.entity("A"), puzzle.entity("B")
    describe(a, b)
    assert puzzle.solve() == expected
    assert puzzle.solve_status == "unique"

    path = tmp_path / "assignment.logos"
    receipt = puzzle.export_proof(path)
    assert receipt.artifact == path.read_bytes()
    result = subprocess.run(
        ["logos", "check", "--json", "--strict", str(path)],
        check=True, capture_output=True, text=True,
    )
    checked = json.loads(result.stdout)
    assert checked["custom_axioms"] == []
    assert checked["artifact_sha256"] == receipt.artifact_sha256
    target = checked["statement"]
    while target["tag"] == "implies":
        target = target["right"]
    names = {symbol["id"]: symbol["name"] for symbol in checked["declarations"]}
    suffix = {"knight": "kn", "knave": "kv"}
    assert target["tag"] == "and"
    assert [names[target[side]["id"]] for side in ("left", "right")] == [
        f"{name}_{suffix[role]}" for name, role in expected.items()
    ]


def test_alternatives_and_no_model_are_distinct(tmp_path):
    puzzle = KnightsKnaves()
    a, b = puzzle.entity("A"), puzzle.entity("B")
    a.says(b.is_knight())
    assert puzzle.solve() == [
        {"A": "knight", "B": "knight"}, {"A": "knave", "B": "knave"},
    ]
    assert puzzle.solve_status == "underdetermined"
    with pytest.raises(logos.LogosProofError, match="unique assignment"):
        puzzle.export_proof(tmp_path / "ambiguous.logos")

    b.says(b.is_knave())
    assert puzzle.solve() is None
    assert puzzle.solve_status == "inconsistent"
    with pytest.raises(logos.LogosProofError, match="unique assignment"):
        puzzle.export_proof(tmp_path / "inconsistent.logos")
    assert not list(tmp_path.iterdir())


def test_timeout_discards_a_partial_search(monkeypatch, tmp_path):
    puzzle = KnightsKnaves()
    puzzle.entity("A")
    puzzle.entity("B")
    # Expire after reaching the first model and before checking the next branch.
    times = iter([0, 0, 0, 0, 1])
    monkeypatch.setattr(_finite, "monotonic", lambda: next(times))
    assert puzzle.solve(timeout=0.5) is None
    assert puzzle.solve_status == "unknown"
    with pytest.raises(logos.LogosProofError, match="unique assignment"):
        puzzle.export_proof(tmp_path / "partial.logos")
    assert not list(tmp_path.iterdir())


def test_mutation_invalidates_the_previous_proof(tmp_path):
    puzzle = KnightsKnaves()
    a = puzzle.entity("A")
    a.says(a.is_knight() | a.is_knave())
    assert puzzle.solve() == {"A": "knight"}
    puzzle.entity("B")
    assert puzzle.solve_status is None
    with pytest.raises(logos.LogosProofError, match="unique assignment"):
        puzzle.export_proof(tmp_path / "stale.logos")
    assert len(puzzle.solve()) == 2


def test_unsupported_statements_report_the_expression_or_foreign_atom():
    puzzle = KnightsKnaves()
    a = puzzle.entity("A")
    a.says(a.is_knight() == a.is_knave())
    with pytest.raises(ValueError, match="unsupported statement Eq"):
        puzzle.solve()

    other = KnightsKnaves()
    b = other.entity("B")
    b.says(a.is_knave())
    with pytest.raises(ValueError, match="A_kv.*must belong to this puzzle"):
        other.solve()
