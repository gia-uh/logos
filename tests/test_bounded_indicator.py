"""A strict comparison indicator based on checked floor-division intervals."""
import shutil
import subprocess

import pytest

import logos
from logos import Int
from logos.expr import Lit


@logos.theorem
def positive_indicator(difference: Int, width: Int):
    return logos.chain(0 < width, 0 < difference, difference <= width,
                       (difference + width - 1) // width == 1)


@positive_indicator.proof
def prove_positive_indicator(p, difference, width):
    positive_width = p.assume(0 < width)
    positive_difference = p.assume(0 < difference)
    maximum = p.assume(difference <= width)
    numerator = difference + width - 1
    at_least_one = p.order("lt_succ_le", 0, difference, using=[positive_difference])
    lower = p.linear(Lit(1) * width <= numerator, using=[at_least_one])
    upper = p.linear(numerator < 2 * width, using=[maximum])
    upper = p.subst(upper, p.ring(2 * width == (Lit(1) + 1) * width))
    return p.order("div_floor_interval", numerator, width, 1,
                   using=[positive_width, lower, upper])


@logos.theorem
def zero_indicator(difference: Int, width: Int):
    return logos.chain(0 < width, 1 - width <= difference, difference <= 0,
                       (difference + width - 1) // width == 0)


@zero_indicator.proof
def prove_zero_indicator(p, difference, width):
    positive_width = p.assume(0 < width)
    minimum = p.assume(1 - width <= difference)
    nonpositive_difference = p.assume(difference <= 0)
    numerator = difference + width - 1
    lower = p.linear(Lit(0) * width <= numerator, using=[minimum])
    upper = p.linear(numerator < Lit(1) * width, using=[nonpositive_difference])
    upper = p.subst(upper, p.ring(Lit(1) * width == (Lit(0) + 1) * width))
    return p.order("div_floor_interval", numerator, width, 0,
                   using=[positive_width, lower, upper])


@pytest.mark.skipif(shutil.which("logos") is None, reason="install the Rust checker")
@pytest.mark.parametrize("theorem", [positive_indicator, zero_indicator])
def test_indicator_replays_strictly(theorem, tmp_path):
    path = tmp_path / "indicator.logos"
    theorem.check()
    logos.export_proof(theorem, path)
    checked = subprocess.run(["logos", "check", "--strict", path], check=True, capture_output=True, text=True)
    assert "Verified with 0 custom axioms" in checked.stdout
