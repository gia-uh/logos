"""Contracts bound to the source of an ordinary Python function."""
import importlib.util
import os
from pathlib import Path
import subprocess
import sys
from types import CodeType

import pytest

import logos
from logos.expr import Add, App, Eq, ForallNode, Implies, Lit, Var
from logos.helpers import structural_eq


STEP_SOURCE = "def step(x: int) -> int:\n    return x + 1\n"


def advance(mid: int) -> int:
    return mid + 1


def bump(mid: int) -> int:
    return mid + 1


def combine(x: int, y: int) -> int:
    return x + y


@logos.theorem(about=advance)
def advances(mid, *, result):
    return logos.contract(ensures=(result - mid == 1))


@logos.theorem(about=bump)
def bump_under_zero(mid, *, result):
    return logos.contract(requires=(mid == 0), ensures=(result - mid == 1))


@logos.theorem(about=advance)
def result_on_the_right(mid, *, result):
    return logos.contract(ensures=(mid + 1 == result))


@logos.theorem(about=combine)
def combine_swaps(x, y, *, result):
    return logos.contract(ensures=(result == y + x))


def test_contract_is_checked_and_exported(tmp_path):
    advances.check()
    assert advances.certified
    assert advances.receipt is not None
    artifact = tmp_path / "advance.logos"
    receipt = logos.export_proof(advances, artifact)
    assert receipt.artifact == artifact.read_bytes()

    checker = "logos"
    result = subprocess.run(
        [checker, "check", "--strict", str(artifact)], capture_output=True, text=True
    )
    assert result.returncode == 0, result.stderr
    assert "Verified with 0 custom axioms" in result.stdout


def test_statement_quantifies_every_int_and_mentions_the_result():
    statement = advances.statement
    bound = []
    while isinstance(statement, ForallNode):
        bound.append((statement.var.name, statement.var.type))
        statement = statement.body
    assert bound == [("mid", int), ("result", int)]
    assert isinstance(statement, Implies)
    assert isinstance(statement.antecedent, Eq)
    assert isinstance(statement.antecedent.right, App)
    assert statement.antecedent.right.func_name == "advance"
    assert structural_eq(
        statement.antecedent.right.symbol.body, Add(Var("mid", int), Lit(1))
    )
    assert structural_eq(
        statement.consequent, Eq(Var("result", int) - Var("mid", int), Lit(1))
    )


def test_requires_is_an_explicit_antecedent():
    statement = bump_under_zero.statement
    outer = statement.var
    assert (outer.name, outer.type) == ("mid", int)
    requires = statement.body.body.antecedent
    assert structural_eq(requires, Eq(Var("mid", int), Lit(0)))
    bump_under_zero.check()
    assert "mid = 0" in _plain_statement(bump_under_zero)


def test_a_result_on_the_right_side_is_rewritten_through_the_body():
    result_on_the_right.check()
    assert result_on_the_right.certified


def test_extra_parameters_are_quantified_in_signature_order():
    combine_swaps.check()
    statement = combine_swaps.statement
    names = []
    while isinstance(statement, ForallNode):
        names.append(statement.var.name)
        statement = statement.body
    assert names == ["x", "y", "result"]


def test_mutated_source_breaks_the_contract(tmp_path):
    module = _import(tmp_path, "mutated", "def step(x: int) -> int:\n    return x + 1\n")

    @logos.theorem(about=module.step)
    def step_contract(x, *, result):
        return logos.contract(ensures=(result - x == 1))

    step_contract.check()
    _rewrite(module, "def step(x: int) -> int:\n    return x\n")
    fresh = _import(tmp_path, "mutated_fresh", "def step(x: int) -> int:\n    return x\n")

    @logos.theorem(about=fresh.step)
    def wrong_contract(x, *, result):
        return logos.contract(ensures=(result - x == 1))

    with pytest.raises(logos.LogosContractError, match="does not follow from its source body"):
        wrong_contract.check()


def test_same_size_source_change_is_detected(tmp_path):
    module = _import(tmp_path, "mismatch", "def move(x: int) -> int:\n    return x + 1\n")
    path = Path(module.__file__)
    before = path.stat()

    path.write_text("def move(x: int) -> int:\n    return x - 1\n")
    os.utime(path, ns=(before.st_atime_ns, before.st_mtime_ns))
    assert path.stat().st_size == before.st_size

    with pytest.raises(logos.LogosContractError, match="does not match the imported code object"):
        @logos.theorem(about=module.move)
        def moved(x, *, result):
            return logos.contract(ensures=(result - x == 1))


def test_source_change_after_certification_is_refused_and_recovers(tmp_path):
    module = _import(tmp_path, "late_source", STEP_SOURCE)

    @logos.theorem(about=module.step)
    def step_contract(x, *, result):
        return logos.contract(ensures=(result - x == 1))

    step_contract.check()
    assert step_contract.certified
    path = Path(module.__file__)
    original = STEP_SOURCE
    path.write_text("def step(x: int) -> int:\n    return x\n")

    assert not step_contract.certified
    with pytest.raises(logos.LogosContractError, match="does not match the imported code object"):
        step_contract.check()
    with pytest.raises(logos.LogosProofError, match="does not match the imported code object"):
        logos.export_proof(step_contract, tmp_path / "stale.logos")
    assert not (tmp_path / "stale.logos").exists()

    path.write_text(original)
    step_contract.check()
    assert step_contract.certified


def test_replaced_code_object_after_decoration_is_refused(tmp_path):
    module = _import(
        tmp_path, "late_code",
        "def step(x: int) -> int:\n    return x + 1\n\n"
        "def other(x: int) -> int:\n    return x\n",
    )

    @logos.theorem(about=module.step)
    def step_contract(x, *, result):
        return logos.contract(ensures=(result - x == 1))

    step_contract.check()
    assert step_contract.certified
    original = module.step.__code__
    module.step.__code__ = module.other.__code__

    assert not step_contract.certified
    with pytest.raises(logos.LogosContractError, match="does not match the imported code object"):
        step_contract.check()
    with pytest.raises(logos.LogosProofError):
        logos.export_proof(step_contract, tmp_path / "stale.logos")
    assert not (tmp_path / "stale.logos").exists()

    module.step.__code__ = original
    step_contract.check()
    assert step_contract.certified


def test_parameter_rebinding_after_certification_is_refused(tmp_path):
    module = _import(
        tmp_path, "late_params",
        "def first(x: int, y: int) -> int:\n    return x\n",
    )

    @logos.theorem(about=module.first)
    def first_is_x(x, y, *, result):
        return logos.contract(ensures=(result == x))

    first_is_x.check()
    assert first_is_x.certified
    path = Path(module.__file__)
    original_code = module.first.__code__
    mutated = "def first(y: int, x: int) -> int:\n    return x\n"
    path.write_text(mutated)
    module.first.__code__ = _function_code(mutated, path, "first")

    assert not first_is_x.certified
    with pytest.raises(logos.LogosContractError, match="parameter binding changed"):
        first_is_x.check()
    with pytest.raises(logos.LogosProofError):
        logos.export_proof(first_is_x, tmp_path / "stale.logos")
    assert not (tmp_path / "stale.logos").exists()

    path.write_text("def first(x: int, y: int) -> int:\n    return x\n")
    module.first.__code__ = original_code
    first_is_x.check()
    assert first_is_x.certified


def test_mutated_translated_body_is_refused(tmp_path):
    module = _import(tmp_path, "late_body", "def step(x: int) -> int:\n    return x + 1\n")

    @logos.theorem(about=module.step)
    def step_contract(x, *, result):
        return logos.contract(ensures=(result - x == 1))

    step_contract.check()
    assert step_contract.certified
    original = step_contract.symbol.body
    step_contract.symbol.body = Add(Var("x", int), Lit(2))

    assert not step_contract.certified
    with pytest.raises(logos.LogosContractError, match="translated body changed"):
        step_contract.check()
    with pytest.raises(logos.LogosProofError):
        logos.export_proof(step_contract, tmp_path / "stale.logos")
    assert not (tmp_path / "stale.logos").exists()

    step_contract.symbol.body = original
    step_contract.check()
    assert step_contract.certified


def test_global_name_is_refused(tmp_path):
    module = _import(
        tmp_path, "globals_app", "OFFSET = 1\n\ndef shift(x: int) -> int:\n    return x + OFFSET\n"
    )
    with pytest.raises(logos.LogosContractError, match="'OFFSET' .* is not a parameter"):
        @logos.theorem(about=module.shift)
        def shifted(x, *, result):
            return logos.contract(ensures=(result - x == 1))


def test_branching_statement_is_refused(tmp_path):
    source = (
        "def choose(x: int) -> int:\n"
        "    if x:\n"
        "        return x + 1\n"
        "    return x\n"
    )
    module = _import(tmp_path, "branch_app", source)
    with pytest.raises(logos.LogosContractError, match="single return statement"):
        @logos.theorem(about=module.choose)
        def chosen(x, *, result):
            return logos.contract(ensures=(result - x == 1))


def test_wrapped_function_is_refused(tmp_path):
    source = (
        "import functools\n\n"
        "def decorate(fn):\n"
        "    @functools.wraps(fn)\n"
        "    def wrapper(*args, **kwargs):\n"
        "        return fn(*args, **kwargs)\n"
        "    return wrapper\n\n"
        "@decorate\n"
        "def wrapped(x: int) -> int:\n"
        "    return x + 1\n"
    )
    module = _import(tmp_path, "wrapper_app", source)
    with pytest.raises(logos.LogosContractError, match="wrapped or decorated"):
        @logos.theorem(about=module.wrapped)
        def wrapped_contract(x, *, result):
            return logos.contract(ensures=(result - x == 1))


def test_ambiguous_module_definition_is_refused(tmp_path):
    source = (
        "def twice(x: int) -> int:\n    return x + 1\n\n"
        "def twice(x: int) -> int:\n    return x + 2\n"
    )
    module = _import(tmp_path, "ambiguous_app", source)
    with pytest.raises(logos.LogosContractError, match="2 times at module level"):
        @logos.theorem(about=module.twice)
        def twice_contract(x, *, result):
            return logos.contract(ensures=(result - x == 1))


def test_function_without_a_module_file_is_refused():
    namespace = {}
    exec("def made(x: int) -> int:\n    return x + 1\n", namespace)
    with pytest.raises(logos.LogosContractError, match="source is not available"):
        @logos.theorem(about=namespace["made"])
        def made_contract(x, *, result):
            return logos.contract(ensures=(result - x == 1))


def test_unsupported_contract_shapes_are_refused():
    with pytest.raises(logos.LogosContractError, match="result appears on exactly one side"):
        @logos.theorem(about=advance)
        def both_sides(mid, *, result):
            return logos.contract(ensures=(result - mid == result))

    with pytest.raises(logos.LogosContractError, match="requires must not mention the result"):
        @logos.theorem(about=advance)
        def uses_result_in_requires(mid, *, result):
            return logos.contract(requires=(result == 0), ensures=(result - mid == 1))

    with pytest.raises(logos.LogosContractError, match="one equality"):
        @logos.theorem(about=advance)
        def not_an_equality(mid, *, result):
            return logos.contract(ensures=((result - mid == 1) & (mid == mid)))


def _plain_statement(theorem):
    result = subprocess.run(
        ["logos", "inspect", "--json", "--strict", "-"],
        input=theorem.receipt.artifact, capture_output=True,
    )
    assert result.returncode == 0, result.stderr
    import json
    return json.loads(result.stdout)["statement_text"]


def _import(tmp_path, name, source):
    path = tmp_path / f"{name}.py"
    path.write_text(source)
    return _load(name, path)


def _rewrite(module, source):
    path = Path(module.__file__)
    path.write_text(source)
    sys.modules.pop(module.__name__, None)


def _load(name, path):
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
