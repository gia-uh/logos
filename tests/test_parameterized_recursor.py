"""Check that sequence parameters survive portable recursor instantiation."""
import shutil
import subprocess

import pytest

import logos
from logos import Int, Seq
from logos.expr import Lit


fixed_offset_sum = logos.recursor(
    "fixed_offset_sum",
    lambda xs, offset: logos.length(xs) + offset,
    lambda n, previous, xs, offset: previous + logos.nth(xs, n + offset),
    parameters={"xs": Seq, "offset": int},
)


@logos.theorem
def first_equations(xs: Seq, offset: Int):
    return (fixed_offset_sum(0, xs, offset) == logos.length(xs) + offset) & (
        fixed_offset_sum(Lit(0) + 1, xs, offset)
        == fixed_offset_sum(0, xs, offset) + logos.nth(xs, 0 + offset)
    )


@first_equations.proof
def prove_first_equations(p, xs, offset):
    base = p.recursor_base(fixed_offset_sum, xs, offset)
    nonnegative = p.order("lt_irrefl", 0)
    step = p.recursor_step(fixed_offset_sum, 0, nonnegative, xs, offset)
    return p.and_intro(base, step)


@pytest.mark.skipif(shutil.which("logos") is None, reason="install the Rust checker")
def test_parameters_are_checked_with_zero_custom_axioms(tmp_path):
    path = tmp_path / "fixed_offset_sum.logos"
    first_equations.check()
    logos.export_proof(first_equations, path)
    checked = subprocess.run(["logos", "check", "--strict", path], check=True, capture_output=True, text=True)
    assert "Verified with 0 custom axioms" in checked.stdout
