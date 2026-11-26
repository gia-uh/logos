"""Search finite domains described by pairs of exclusive proposition atoms."""
from collections.abc import Callable
from dataclasses import dataclass
from time import monotonic

from logos import chain
from logos.expr import And, Expr, Implies, Lit, Not, Or, Var
from logos.goal import Goal
from logos.helpers import structural_eq
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


def _derive(
    expr: Expr, values: dict[Var, bool], facts: dict[Var, ProofTerm], prefix: str,
) -> ProofTerm:
    """Prove a known true proposition, or prove its negation if known false."""
    hyp = HypRef(prefix + "formula")

    def negate(body: ProofTerm) -> ProofTerm:
        return NotIntro(ImpliesIntro(expr, hyp.name, body))

    def derive(child: Expr) -> ProofTerm:
        return _derive(child, values, facts, prefix)

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
            case = HypRef(prefix + "disjunct")
            return negate(CaseAnalysis(
                hyp, case.name, NotElim(derive(left), case), NotElim(derive(right), case),
            ))
        case Implies(left, right):
            assumption = HypRef(prefix + "antecedent")
            if _truth(left, values) is False:
                body = ExFalso(NotElim(derive(left), assumption), right)
            elif _truth(right, values) is True:
                body = derive(right)
            else:
                return negate(NotElim(derive(right), ImpliesElim(hyp, derive(left))))
            return ImpliesIntro(left, assumption.name, body)
    raise AssertionError("expected a validated proposition")


def bind(premises: list[Expr]) -> dict[str, Expr]:
    return {f"premise_{index}": premise for index, premise in enumerate(premises, 1)}


def theorem(goal: Goal, proof: ProofTerm, *, name: str) -> Theorem:
    for binder, premise in reversed(goal.context.items()):
        proof = ImpliesIntro(premise, binder, proof)
    statement = chain(*goal.context.values(), goal.statement)
    return Theorem(statement, name=name).proof(exact(proof))


def budget(timeout: float | None) -> Callable[[], None]:
    deadline = None if timeout is None else monotonic() + timeout

    def check() -> None:
        if deadline is not None and monotonic() >= deadline:
            raise TimeoutError("finite-domain search budget exhausted")

    return check


def _violation(constraints: list[Expr], values: dict[Var, bool]) -> int | None:
    return next((i for i, expr in enumerate(constraints) if _truth(expr, values) is False), None)


class Counterexample(Exception):
    def __init__(self, assignment: tuple[Var, ...]):
        self.assignment = assignment


class MissingRolePremise(Exception):
    pass


def certify(goal: Goal, choices: list[BinaryChoice], check_budget: Callable[[], None]) -> ProofTerm:
    """Split into role cases, close impossible branches, and prove the goal in the rest."""
    check_budget()
    context = goal.context
    names = list(context)
    constraints = list(context.values())
    conclusion = goal.statement
    values: dict[Var, bool] = {}
    facts: dict[Var, ProofTerm] = {}
    prefix = "finite_"
    while any(name.startswith(prefix) for name in names):
        prefix = "_" + prefix

    def lookup(statement: Expr) -> str | None:
        return next((name for name, hyp in context.items() if structural_eq(hyp, statement)), None)

    roles = [
        (choice, lookup(choice.left), lookup(choice.right),
         tuple(lookup(premise) for premise in choice.premises()))
        for choice in choices
    ]

    def branch(index: int) -> ProofTerm:
        check_budget()
        violation = _violation(constraints, values)
        if violation is not None:
            negation = _derive(constraints[violation], values, facts, prefix)
            return ExFalso(NotElim(negation, HypRef(names[violation])), conclusion)
        if _truth(conclusion, values) is True:
            return _derive(conclusion, values, facts, prefix)
        if index == len(roles):
            raise Counterexample(tuple(atom for atom, value in values.items() if value))

        choice, known_left, known_right, (exhaustive, exclude_right, exclude_left) = roles[index]
        left, right = choice.left, choice.right

        def assume(selected: Var, excluded: Var, hypothesis: str, exclusive: str | None) -> ProofTerm:
            if exclusive is None:
                raise MissingRolePremise
            role = HypRef(hypothesis)
            values[selected], values[excluded] = True, False
            facts[selected] = role
            facts[excluded] = ImpliesElim(HypRef(exclusive), role)
            proof = branch(index + 1)
            del values[selected], values[excluded], facts[selected], facts[excluded]
            return proof

        if known_left is not None:
            return assume(left, right, known_left, exclude_right)
        if known_right is not None:
            return assume(right, left, known_right, exclude_left)
        if exhaustive is None:
            raise MissingRolePremise
        binder = f"{prefix}choice_{index + 1}"
        return CaseAnalysis(
            HypRef(exhaustive), binder,
            assume(left, right, binder, exclude_right),
            assume(right, left, binder, exclude_left),
        )

    proof = branch(0)
    check_budget()
    return proof


def solve(
    choices: list[BinaryChoice], constraints: list[Expr], *, name: str, timeout: float | None,
) -> tuple[list[tuple[Var, ...]], Theorem | None]:
    """Return all models and prepare evidence only for a unique result."""
    check_budget = budget(timeout)
    values: dict[Var, bool] = {}
    models: list[tuple[Var, ...]] = []
    assignment: list[Var] = []

    def search(index: int) -> None:
        check_budget()
        if _violation(constraints, values) is not None:
            return
        if index == len(choices):
            models.append(tuple(assignment))
            return
        left, right = choices[index].left, choices[index].right
        for selected, excluded in ((left, right), (right, left)):
            values[selected], values[excluded] = True, False
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
    goal = Goal(bind(premises), conclusion)
    proof = theorem(goal, certify(goal, choices, check_budget), name=name)
    check_budget()
    return models, proof
