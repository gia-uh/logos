"""Search finite domains described by pairs of exclusive proposition atoms."""
from dataclasses import dataclass
from time import monotonic

from logos import chain
from logos.expr import And, Expr, Implies, Lit, Not, Or, Var
from logos.kernel import (
    AndElimL, AndElimR, AndIntro, CaseAnalysis, ExFalso, HypRef, ImpliesElim, ImpliesIntro,
    NotElim, NotIntro, OrIntroL, OrIntroR, ProofTerm,
)
from logos.tactics import exact
from logos.theorem import Theorem


@dataclass(frozen=True)
class BinaryChoice:
    left: Var
    right: Var

    def premises(self) -> tuple[Expr, Expr, Expr]:
        return self.left | self.right, self.left >> ~self.right, self.right >> ~self.left


def validate(expr: Expr, atoms: set[Var]) -> None:
    match expr:
        case Var() if expr in atoms:
            return
        case Var():
            raise ValueError(f"statement atom {expr.name!r} must belong to this puzzle")
        case Lit(value) if value is False:
            return
        case Not(operand):
            validate(operand, atoms)
        case And(left, right) | Or(left, right) | Implies(left, right):
            validate(left, atoms)
            validate(right, atoms)
        case _:
            raise ValueError(
                f"unsupported statement {type(expr).__name__}; use role propositions "
                "joined by &, |, ~ or >>, or logos.lit(False)"
            )


def _truth(expr: Expr, values: dict[Var, bool]) -> bool | None:
    """Evaluate what is forced by the assigned atoms, leaving open cases unknown."""
    match expr:
        case Var():
            return values.get(expr)
        case Lit():
            return False
        case Not(operand):
            value = _truth(operand, values)
            return None if value is None else not value
        case And(left, right):
            a, b = _truth(left, values), _truth(right, values)
            if a is False or b is False:
                return False
            return True if a is True and b is True else None
        case Or(left, right):
            a, b = _truth(left, values), _truth(right, values)
            if a is True or b is True:
                return True
            return False if a is False and b is False else None
        case Implies(left, right):
            a, b = _truth(left, values), _truth(right, values)
            if a is False or b is True:
                return True
            return False if a is True and b is False else None
    raise AssertionError("expected a validated proposition")


def _derive(expr: Expr, values: dict[Var, bool], facts: dict[Var, ProofTerm]) -> ProofTerm:
    """Prove a known true proposition, or prove its negation if known false."""
    hyp = HypRef("formula")

    def negate(body: ProofTerm) -> ProofTerm:
        return NotIntro(ImpliesIntro(expr, hyp.name, body))

    def derive(child: Expr) -> ProofTerm:
        return _derive(child, values, facts)

    match expr:
        case Var():
            return facts[expr]
        case Lit():
            return negate(hyp)
        case Not(operand):
            proof = derive(operand)
            return negate(NotElim(hyp, proof)) if _truth(operand, values) else proof
        case And(left, right):
            if _truth(left, values) is False:
                return negate(NotElim(derive(left), AndElimL(hyp)))
            if _truth(right, values) is False:
                return negate(NotElim(derive(right), AndElimR(hyp)))
            return AndIntro(derive(left), derive(right))
        case Or(left, right):
            if _truth(left, values) is True:
                return OrIntroL(derive(left), right)
            if _truth(right, values) is True:
                return OrIntroR(left, derive(right))
            case = HypRef("disjunct")
            return negate(CaseAnalysis(
                hyp, case.name, NotElim(derive(left), case), NotElim(derive(right), case),
            ))
        case Implies(left, right):
            assumption = HypRef("antecedent")
            if _truth(left, values) is False:
                body = ExFalso(NotElim(derive(left), assumption), right)
            elif _truth(right, values) is True:
                body = derive(right)
            else:
                return negate(NotElim(derive(right), ImpliesElim(hyp, derive(left))))
            return ImpliesIntro(left, assumption.name, body)
    raise AssertionError("expected a validated proposition")


def solve(
    choices: list[BinaryChoice], constraints: list[Expr], *, name: str, timeout: float | None,
) -> tuple[list[tuple[Var, ...]], Theorem | None]:
    """Return all models and prepare evidence only for a unique result.

    Each case assumes one disjunct and derives the negation of the other
    from its exclusivity premise. A violated constraint closes that case.
    """
    deadline = None if timeout is None else monotonic() + timeout
    values: dict[Var, bool] = {}
    facts: dict[Var, ProofTerm] = {}
    models: list[tuple[Var, ...]] = []
    assignment: list[Var] = []

    def check_budget() -> None:
        if deadline is not None and monotonic() >= deadline:
            raise TimeoutError("finite-domain search budget exhausted")

    def violated_constraint() -> int | None:
        check_budget()
        for index, constraint in enumerate(constraints):
            if _truth(constraint, values) is False:
                return index
        return None

    def set_choice(selected: Var, excluded: Var) -> None:
        values[selected], values[excluded] = True, False

    def search(index: int) -> None:
        if violated_constraint() is not None:
            return
        if index == len(choices):
            models.append(tuple(assignment))
            return
        left, right = choices[index].left, choices[index].right
        for selected, excluded in ((left, right), (right, left)):
            set_choice(selected, excluded)
            assignment.append(selected)
            search(index + 1)
            assignment.pop()
        del values[left], values[right]

    search(0)
    check_budget()
    if len(models) != 1:
        return models, None

    model = models[0]
    if model:
        conclusion = model[0]
        for atom in model[1:]:
            conclusion = conclusion & atom
    else:
        conclusion = ~Lit(False)

    premises = [premise for choice in choices for premise in choice.premises()] + constraints
    names = [f"premise_{index + 1}" for index in range(len(premises))]

    def certify(index: int) -> ProofTerm:
        violation = violated_constraint()
        if violation is not None:
            negation = _derive(constraints[violation], values, facts)
            premise = HypRef(names[3 * len(choices) + violation])
            return ExFalso(NotElim(negation, premise), conclusion)
        if index == len(choices):
            return _derive(conclusion, values, facts)
        left, right = choices[index].left, choices[index].right
        role = HypRef(f"choice_{index + 1}")
        cases = []
        for selected, excluded, offset in ((left, right, 1), (right, left, 2)):
            set_choice(selected, excluded)
            facts[selected] = role
            facts[excluded] = ImpliesElim(HypRef(names[3 * index + offset]), role)
            cases.append(certify(index + 1))
        del values[left], values[right], facts[left], facts[right]
        return CaseAnalysis(HypRef(names[3 * index]), role.name, *cases)

    proof = certify(0)
    for premise, binder in zip(reversed(premises), reversed(names)):
        proof = ImpliesIntro(premise, binder, proof)
    theorem = Theorem(chain(*premises, conclusion), name=name)
    theorem.proof(exact(proof))
    check_budget()
    return models, theorem
