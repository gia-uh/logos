"""Strict integer order in the portable core and in source-bound contracts."""
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
from types import CodeType

import pytest

import logos
from logos import tactics as t
from logos.expr import Add, Eq, ForallNode, Implies, Lit, Lt, Not, Var
from logos.goal import Goal
from logos.helpers import structural_eq
from logos.order import ORDER_LAWS, order_law, split_implications
from logos.portable import artifact_bytes, statement_declarations
from logos.runner import TacticFailed, run


CHECKER = shutil.which("logos")
requires_checker = pytest.mark.skipif(CHECKER is None, reason="install the Rust logos CLI")

MINIMUM_SOURCE = (
    "def minimum(x: int, y: int) -> int:\n"
    "    if x < y:\n"
    "        return x\n"
    "    else:\n"
    "        return y\n"
)


def minimum(x: int, y: int) -> int:
    if x < y:
        return x
    else:
        return y


@logos.theorem(about=minimum)
def minimum_then(x, y, *, result):
    return logos.contract(requires=(x < y), ensures=(result == x))


@logos.theorem(about=minimum)
def minimum_else(x, y, *, result):
    return logos.contract(requires=~(x < y), ensures=(result == y))


def test_order_law_schemas_are_explicit():
    a, b, c = (Var(name, int) for name in "abc")
    assert ORDER_LAWS == ("lt_irrefl", "lt_trans", "lt_add", "lt_neq")
    assert structural_eq(order_law("lt_irrefl", (a,)), Not(Lt(a, a)))
    assert structural_eq(
        order_law("lt_trans", (a, b, c)),
        Implies(Lt(a, b), Implies(Lt(b, c), Lt(a, c))),
    )
    assert structural_eq(
        order_law("lt_add", (a, b, c)),
        Implies(Lt(a, b), Lt(Add(a, c), Add(b, c))),
    )
    assert structural_eq(
        order_law("lt_neq", (a, b)),
        Implies(Lt(a, b), Not(Eq(a, b))),
    )
    premises, conclusion = split_implications(order_law("lt_trans", (a, b, c)))
    assert len(premises) == 2 and structural_eq(conclusion, Lt(a, c))
    with pytest.raises(ValueError, match="unknown order law"):
        order_law("lt_reverse", (a, b))
    with pytest.raises(ValueError, match="takes 3 integer arguments"):
        order_law("lt_add", (a, b))


def test_order_tactic_emits_only_core_law_evidence():
    statement = logos.forall(
        int, int, int, lambda x, y, c: (x < y) >> ((x + c) < (y + c))
    )
    evidence = run(
        Goal({}, statement),
        [t.intro("x", "y", "c", "h"), t.order("lt_add")],
    )
    artifact = artifact_bytes(
        "transport", statement, statement_declarations(statement), evidence
    )
    bundle = json.loads(artifact)
    assert bundle["custom_axioms"] == []
    assert bundle["target"]["body"]["body"]["body"]["right"]["tag"] == "lt"
    assert bundle["proof"]["body"]["body"]["body"]["body"]["implication"] == {
        "tag": "core_law",
        "id": "lt_add",
        "args": [
            {"tag": "bound", "index": 2},
            {"tag": "bound", "index": 1},
            {"tag": "bound", "index": 0},
        ],
    }


def test_order_tactic_rejects_a_wrong_goal_or_a_missing_premise():
    x, y, c = Var("x", int), Var("y", int), Var("c", int)
    wrong = logos.forall(
        int, int, int, lambda x, y, c: (x < y) >> ((y + c) < (x + c))
    )
    with pytest.raises(TacticFailed, match="proof conclusion mismatch|does not match"):
        run(Goal({}, wrong), [t.intro("x", "y", "c", "h"), t.order("lt_add")])

    missing = ((x + c) < (y + c))
    with pytest.raises(TacticFailed, match="does not match"):
        run(Goal({}, missing), [t.order("lt_add")])

    with pytest.raises(TacticFailed, match="unknown core order law"):
        run(Goal({}, x < y), [t.order("lt_reverse")])


@requires_checker
def test_one_genuine_order_consequence_strict_checks(tmp_path):
    x, y, c = logos.vars("x y c", int)

    transport = logos.Theorem(
        logos.forall(int, int, int, lambda x, y, c: (x < y) >> ((x + c) < (y + c))),
        name="lt_add_transport",
    ).proof(t.intro("x", "y", "c", "h"), t.order("lt_add"))
    disequality = logos.Theorem(
        logos.forall(int, int, lambda x, y: (x < y) >> ~(x == y)),
        name="lt_neq_from_lt",
    ).proof(t.intro("x", "y", "h"), t.order("lt_neq"))

    for theorem, expected_law in (
        (transport, "lt_add"),
        (disequality, "lt_neq"),
    ):
        logos.check(theorem)
        assert theorem.certified
        path = tmp_path / f"{theorem.name}.logos"
        receipt = logos.export_proof(theorem, path)
        assert path.read_bytes() == receipt.artifact
        result = subprocess.run(
            ["logos", "check", "--strict", str(path)], capture_output=True, text=True
        )
        assert result.returncode == 0, result.stderr
        assert "Verified with 0 custom axioms" in result.stdout
        inspected = subprocess.run(
            ["logos", "inspect", "--json", "--strict", str(path)],
            capture_output=True,
            text=True,
        )
        assert inspected.returncode == 0, inspected.stderr
        trace = json.loads(inspected.stdout)
        assert trace["custom_axioms"] == []
        assert expected_law in {step["rule"] for step in trace["steps"]} or any(
            step.get("reference_id") == expected_law for step in trace["steps"]
        )
        assert all(step["rule"] != "axiom_ref" for step in trace["steps"])


@requires_checker
def test_both_minimum_paths_strict_check(tmp_path):
    for theorem in (minimum_then, minimum_else):
        theorem.check()
        assert theorem.certified
        path = tmp_path / f"{theorem.name}.logos"
        logos.export_proof(theorem, path)
        result = subprocess.run(
            ["logos", "check", "--strict", str(path)], capture_output=True, text=True
        )
        assert result.returncode == 0, result.stderr
        assert "Verified with 0 custom axioms" in result.stdout


def test_branch_selection_uses_the_order_complement():
    assert minimum_then._branch == "then"
    assert minimum_else._branch == "else"
    guard = minimum_then._fragment.guard
    assert isinstance(guard, Lt)
    statement = minimum_else.statement
    assert statement.var.name == "x"
    requires = statement.body.body.body.antecedent
    assert structural_eq(requires, Not(Lt(Var("x", int), Var("y", int))))

    with pytest.raises(logos.LogosContractError, match="must select one path"):
        @logos.theorem(about=minimum)
        def no_requires(x, y, *, result):
            return logos.contract(ensures=(result == x))

    with pytest.raises(logos.LogosContractError, match="does not select a branch"):
        @logos.theorem(about=minimum)
        def equality_does_not_select(x, y, *, result):
            return logos.contract(requires=(x == y), ensures=(result == y))

    with pytest.raises(logos.LogosContractError, match="does not select a branch"):
        @logos.theorem(about=minimum)
        def reversed_order_is_not_the_complement(x, y, *, result):
            return logos.contract(requires=(y < x), ensures=(result == y))


def test_equality_boundary_belongs_to_the_else_path():
    assert minimum(3, 3) == 3
    assert minimum(2, 5) == 2
    assert minimum(5, 2) == 2
    # The else theorem's premise is the complement, not a separate > case.
    assert isinstance(minimum_else._fragment.guard, Lt)
    assert structural_eq(
        minimum_else._fragment.guard,
        Lt(Var("x", int), Var("y", int)),
    )


@requires_checker
def test_guard_and_branch_mutations_invalidate_both_paths(tmp_path):
    name = "minimum_mutation"
    module = _import(tmp_path, name, MINIMUM_SOURCE)

    @logos.theorem(about=module.minimum)
    def then_path(x, y, *, result):
        return logos.contract(requires=(x < y), ensures=(result == x))

    @logos.theorem(about=module.minimum)
    def else_path(x, y, *, result):
        return logos.contract(requires=~(x < y), ensures=(result == y))

    then_path.check()
    else_path.check()
    path = Path(module.__file__)
    original_source = path.read_text()
    original_code = module.minimum.__code__

    changes = [
        (MINIMUM_SOURCE.replace("x < y", "y < x"), "guard changed"),
        (MINIMUM_SOURCE.replace("x < y", "x == y"), "guard changed"),
        (MINIMUM_SOURCE.replace("return x", "return x + 1", 1), "then branch changed"),
        (MINIMUM_SOURCE.replace("return y", "return x"), "else branch changed"),
    ]
    for changed, label in changes:
        assert changed != original_source
        path.write_text(changed)
        module.minimum.__code__ = _function_code(changed, path, "minimum")
        for theorem in (then_path, else_path):
            assert not theorem.certified
            with pytest.raises(logos.LogosContractError, match=label):
                theorem.check()
            with pytest.raises(logos.LogosProofError, match=label):
                logos.export_proof(theorem, tmp_path / "stale.logos")
            assert not (tmp_path / "stale.logos").exists()
        path.write_text(original_source)
        module.minimum.__code__ = original_code

    then_path.check()
    else_path.check()
    assert then_path.certified and else_path.certified


def test_unsupported_order_syntax_fails_closed(tmp_path):
    for index, source in enumerate(
        [
            "def minimum(x: int, y: int) -> int:\n"
            "    if x <= y:\n"
            "        return x\n"
            "    else:\n"
            "        return y\n",
            "def minimum(x: int, y: int) -> int:\n"
            "    if y > x:\n"
            "        return x\n"
            "    else:\n"
            "        return y\n",
        ]
    ):
        module = _import(tmp_path, f"order_shape_{index}", source)
        with pytest.raises(logos.LogosContractError, match="only <, == and !=|unsupported comparison"):
            @logos.theorem(about=module.minimum)
            def chosen(x, y, *, result):
                return logos.contract(requires=(x < y), ensures=(result == x))


@requires_checker
def test_mutated_selected_symbol_body_is_refused(tmp_path):
    module = _import(tmp_path, "minimum_body_mutation", MINIMUM_SOURCE)

    @logos.theorem(about=module.minimum)
    def then_path(x, y, *, result):
        return logos.contract(requires=(x < y), ensures=(result == x))

    then_path.check()
    original = then_path.symbol.body
    then_path.symbol.body = Lit(0)
    assert not then_path.certified
    with pytest.raises(logos.LogosContractError, match="translated body changed"):
        then_path.check()
    then_path.symbol.body = original
    then_path.check()
    assert then_path.certified


def _import(tmp_path, name, source):
    path = tmp_path / f"{name}.py"
    path.write_text(source)
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _function_code(source, path, name):
    compiled = compile(source, str(path), "exec")
    return next(
        value for value in compiled.co_consts
        if isinstance(value, CodeType) and value.co_name == name
    )
