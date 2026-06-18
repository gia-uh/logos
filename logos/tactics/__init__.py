from logos.tactics.structural import (
    intro, assumption, exact, apply, split, left, right, witness, contradiction,
)
from logos.tactics.rewrite import (
    unfold, refl, rewrite, rewrite_rev, eval_, norm_num,
)
from logos.tactics.arithmetic import ring, linarith, decide
from logos.tactics.combinators import then, first, try_, repeat, all_goals
from logos.tactics.auto import auto
