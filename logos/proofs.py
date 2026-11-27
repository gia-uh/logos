"""Generate and prove the verification conditions of a loop program.

This module is untrusted: it proposes verification conditions and proof terms.
The Rust checker recomputes the same conditions from the program and checks
every proof term with the core rules. The Python code never decides truth.
"""
from __future__ import annotations

from fractions import Fraction

from logos.core_laws import law_statement
from logos.expr import (
    Add, And, Div, Eq, Expr, ExistsNode, ForallNode, Implies, Le, Len, Lit, Lt,
    Mul, Neg, Not, Nth, Or, Pow, Sorted, Sub, Var,
)
from logos.helpers import structural_eq, substitute_symbols
from logos.kernel import (
    AndElimL, AndElimR, AndIntro, CaseAnalysis, CoreLaw, EqSubst, ExFalso, ForallElim,
    ForallIntro, Have, HypRef, ImpliesElim, ImpliesIntro, Linear, NotElim,
    NotIntro, OrIntroL, OrIntroR, Refl, Symm,
)
from logos.programs import Assign, If, Program, Return, While
from logos.sequence import length, nth


class ProofSearchError(Exception):
    pass


def _show(expr: Expr) -> str:
    """Render a condition the way the book writes it, not as a dataclass repr."""
    from logos.authoring import format_expr
    return format_expr(expr)


# ── Verification conditions ─────────────────────────────────────────────────


def _subst(expr: Expr, mapping: dict[int, Expr]) -> Expr:
    return substitute_symbols(expr, mapping)


def _bound(program: Program, index: Expr) -> Expr:
    return (Lit(0) <= index) & (index < length(program.params[0].var))


def _close(program: Program, goal: Expr) -> Expr:
    for item in reversed(program.variables):
        goal = ForallNode(item.var, goal)
    return goal


class _Generator:
    def __init__(self, program: Program):
        self.program = program
        self.obligations: dict[str, Expr] = {}
        self.loops = 0
        self.reads = 0
        self.returned = False

    def wp(self, statements, q):
        for statement in reversed(statements):
            if isinstance(statement, Assign):
                variable = self._variable(statement.name)
                q = _subst(q, {id(variable): statement.value})
            elif isinstance(statement, Return):
                q = _subst(q, {id(self.program.result.var): statement.value})
                self.returned = True
            elif isinstance(statement, If):
                q = And(
                    Implies(statement.condition, self.wp(statement.then_body, q)),
                    Implies(Not(statement.condition), self.wp(statement.else_body, q)),
                )
            elif isinstance(statement, While):
                index = self.loops
                self.loops += 1
                invariant = statement.invariant
                variant = statement.variant
                preserve = Implies(
                    And(invariant, statement.condition),
                    self.wp(statement.body, invariant),
                )
                exit_ = Implies(And(invariant, Not(statement.condition)), q)
                nonnegative = Implies(invariant, Le(Lit(0), variant))
                old = self.program.ghosts[0].var
                decreases = Implies(
                    Eq(old, variant),
                    Implies(
                        And(invariant, statement.condition),
                        self.wp(statement.body, Or(Not(statement.condition), Lt(variant, old))),
                    ),
                )
                prefix = f"loop{index}"
                self.obligations[f"{prefix}.preserve"] = preserve
                self.obligations[f"{prefix}.exit"] = exit_
                self.obligations[f"{prefix}.variant_nonnegative"] = nonnegative
                self.obligations[f"{prefix}.variant_decreases"] = decreases
                q = invariant
            else:
                raise ProofSearchError(f"unsupported statement {type(statement).__name__}")
        return q

    def _variable(self, name: str) -> Var:
        for item in (*self.program.params, *self.program.locals):
            if item.name == name:
                return item.var
        raise ProofSearchError(f"unknown program variable {name!r}")

    def reads_in(self, statements, path, state):
        for statement in statements:
            if isinstance(statement, Assign):
                value = _subst(statement.value, state)
                self._read_obligations(value, path)
                variable = self._variable(statement.name)
                state = dict(state)
                state[id(variable)] = value
            elif isinstance(statement, If):
                condition = _subst(statement.condition, state)
                self._read_obligations(condition, path)
                self.reads_in(statement.then_body, And(path, condition), dict(state))
                self.reads_in(statement.else_body, And(path, Not(condition)), dict(state))
            elif isinstance(statement, While):
                condition = statement.condition
                self._read_obligations(condition, And(path, statement.invariant))
                self.reads_in(
                    statement.body,
                    And(statement.invariant, condition),
                    {},
                )
                state = {}
            elif isinstance(statement, Return):
                self._read_obligations(_subst(statement.value, state), path)

    def _read_obligations(self, expression, path):
        for read in _nth_reads(expression):
            self.obligations[f"read{self.reads}"] = Implies(
                path, (Lit(0) <= read.index) & (read.index < length(read.seq))
            )
            self.reads += 1


def _nth_reads(expr: Expr):
    if isinstance(expr, Nth):
        yield expr
        yield from _nth_reads(expr.seq)
        yield from _nth_reads(expr.index)
        return
    for field in getattr(expr, "__dataclass_fields__", ()):
        value = getattr(expr, field)
        if isinstance(value, Expr):
            yield from _nth_reads(value)
        elif isinstance(value, (list, tuple)):
            for item in value:
                if isinstance(item, Expr):
                    yield from _nth_reads(item)
        elif isinstance(value, tuple):
            for item in value:
                if isinstance(item, Expr):
                    yield from _nth_reads(item)


def verification_conditions(program: Program) -> dict[str, Expr]:
    generator = _Generator(program)
    main = Implies(program.requires, generator.wp(program.body, program.ensures))
    if not generator.returned:
        raise ProofSearchError("program has no return statement")
    generator.reads_in(program.body, program.requires, {})
    generator.obligations["main"] = main
    return {name: _close(program, goal) for name, goal in generator.obligations.items()}


# ── Linear arithmetic certificates ──────────────────────────────────────────


def _key(expr: Expr):
    if isinstance(expr, Var):
        return ("var", expr.name)
    if isinstance(expr, Lit):
        return ("lit", expr.value)
    if isinstance(expr, Add):
        return ("add", _key(expr.left), _key(expr.right))
    if isinstance(expr, Sub):
        return ("sub", _key(expr.left), _key(expr.right))
    if isinstance(expr, Mul):
        return ("mul", _key(expr.left), _key(expr.right))
    if isinstance(expr, Div):
        return ("div", _key(expr.left), _key(expr.right))
    if isinstance(expr, Neg):
        return ("neg", _key(expr.operand))
    if isinstance(expr, Len):
        return ("len", _key(expr.seq))
    if isinstance(expr, Nth):
        return ("nth", _key(expr.seq), _key(expr.index))
    if isinstance(expr, Sorted):
        return ("sorted", _key(expr.seq))
    return ("other", repr(expr))


def _linear(expr: Expr) -> tuple[dict, Fraction] | None:
    if isinstance(expr, Lit) and type(expr.value) is int:
        return {}, Fraction(expr.value)
    if isinstance(expr, Var):
        return {_key(expr): Fraction(1)}, Fraction(0)
    if isinstance(expr, Add):
        left, right = _linear(expr.left), _linear(expr.right)
        if left is None or right is None:
            return None
        return _merge(left[0], right[0], 1), left[1] + right[1]
    if isinstance(expr, Sub):
        left, right = _linear(expr.left), _linear(expr.right)
        if left is None or right is None:
            return None
        return _merge(left[0], right[0], -1), left[1] - right[1]
    if isinstance(expr, Neg):
        inner = _linear(expr.operand)
        if inner is None:
            return None
        return {key: -value for key, value in inner[0].items()}, -inner[1]
    if isinstance(expr, Mul):
        left_lit = expr.left.value if isinstance(expr.left, Lit) and type(expr.left.value) is int else None
        right_lit = expr.right.value if isinstance(expr.right, Lit) and type(expr.right.value) is int else None
        if left_lit is not None:
            inner = _linear(expr.right)
            if inner is None:
                return None
            return {key: value * left_lit for key, value in inner[0].items()}, inner[1] * left_lit
        if right_lit is not None:
            inner = _linear(expr.left)
            if inner is None:
                return None
            return {key: value * right_lit for key, value in inner[0].items()}, inner[1] * right_lit
        # A non-linear product is still an atomic term for linear reasoning.
        return {_key(expr): Fraction(1)}, Fraction(0)
    # Atomic terms: sequence reads, lengths, division nodes and opaque calls.
    return {_key(expr): Fraction(1)}, Fraction(0)


def _merge(left: dict, right: dict, sign: int) -> dict:
    result = dict(left)
    for key, value in right.items():
        result[key] = result.get(key, Fraction(0)) + sign * value
        if result[key] == 0:
            del result[key]
    return result


class _Constraint:
    __slots__ = ("coeffs", "constant", "strict", "labels")

    def __init__(self, coeffs, constant, strict, labels):
        self.coeffs = coeffs
        self.constant = constant
        self.strict = strict
        self.labels = labels

    def scaled(self, factor, label=None):
        labels = {key: value * factor for key, value in self.labels.items()}
        if label is not None:
            labels[label] = labels.get(label, Fraction(0)) + factor
        return _Constraint(
            {key: value * factor for key, value in self.coeffs.items()},
            self.constant * factor,
            self.strict,
            {key: value for key, value in labels.items() if value != 0},
        )

    def plus(self, other):
        coeffs = dict(self.coeffs)
        for key, value in other.coeffs.items():
            coeffs[key] = coeffs.get(key, Fraction(0)) + value
            if coeffs[key] == 0:
                del coeffs[key]
        labels = dict(self.labels)
        for key, value in other.labels.items():
            labels[key] = labels.get(key, Fraction(0)) + value
            if labels[key] == 0:
                del labels[key]
        return _Constraint(coeffs, self.constant + other.constant, self.strict or other.strict, labels)


def _constraint(expr: Expr) -> _Constraint | None:
    if isinstance(expr, Le):
        left, right = _linear(expr.left), _linear(expr.right)
        if left is None or right is None:
            return None
        return _Constraint(_merge(left[0], right[0], -1), left[1] - right[1], False, {})
    if isinstance(expr, Lt):
        left, right = _linear(expr.left), _linear(expr.right)
        if left is None or right is None:
            return None
        return _Constraint(_merge(left[0], right[0], -1), left[1] - right[1], True, {})
    if isinstance(expr, Eq):
        left, right = _linear(expr.left), _linear(expr.right)
        if left is None or right is None:
            return None
        return _Constraint(_merge(left[0], right[0], -1), left[1] - right[1], False, {})
    return None


def farkas(goal: Expr, facts: list[tuple[str, Expr]]) -> dict[str, Fraction] | None:
    constraints = []
    for name, expression in facts:
        base = _constraint(expression)
        if base is None:
            continue
        if isinstance(expression, Eq):
            # An equality may be used with either sign.
            constraints.append(base.scaled(Fraction(1), name))
            constraints.append(base.scaled(Fraction(-1), name))
        else:
            constraints.append(base.scaled(Fraction(1), name))
    if isinstance(goal, (Le, Lt)):
        negated = Lt(goal.right, goal.left) if isinstance(goal, Le) else Le(goal.right, goal.left)
        base = _constraint(negated)
        if base is None:
            return None
        constraints.append(base)
    elif not isinstance(goal, Lit) or goal.value is not False:
        return None
    atoms = sorted({key for constraint in constraints for key in constraint.coeffs})
    system = constraints
    for atom in atoms:
        positive = [item for item in system if item.coeffs.get(atom, 0) > 0]
        negative = [item for item in system if item.coeffs.get(atom, 0) < 0]
        zero = [item for item in system if item.coeffs.get(atom, 0) == 0]
        if not positive or not negative:
            system = zero + positive + negative
            continue
        combined = list(zero)
        for first in positive:
            alpha = first.coeffs[atom]
            for second in negative:
                beta = second.coeffs[atom]
                # (-beta) * first + alpha * second eliminates the atom.
                combined.append(first.scaled(-beta).plus(second.scaled(alpha)))
        if len(combined) > 4000:
            return None
        system = combined
    for constraint in system:
        if constraint.coeffs:
            continue
        if constraint.strict:
            contradiction = constraint.constant >= 0
        else:
            contradiction = constraint.constant > 0
        if contradiction:
            labels = {name: value for name, value in constraint.labels.items() if value != 0}
            if _certificate_valid(goal, facts, labels):
                return labels
            return None
    return None


def _certificate_valid(goal, facts, labels):
    by_name = {name: expression for name, expression in facts}
    total = _Constraint({}, Fraction(0), False, {})
    for name, coefficient in labels.items():
        expression = by_name.get(name)
        if expression is None:
            return False
        base = _constraint(expression)
        if base is None:
            return False
        if not isinstance(expression, Eq) and coefficient < 0:
            return False
        total = total.plus(base.scaled(coefficient))
    if isinstance(goal, (Le, Lt)):
        negated = Lt(goal.right, goal.left) if isinstance(goal, Le) else Le(goal.right, goal.left)
        base = _constraint(negated)
        if base is None:
            return False
        total = total.plus(base)
    elif not (isinstance(goal, Lit) and goal.value is False):
        return False
    if total.coeffs:
        return False
    if total.strict:
        return total.constant >= 0
    return total.constant > 0


# ── Proof search ────────────────────────────────────────────────────────────


class _Fact:
    __slots__ = ("name", "expr", "proof", "expanded")

    def __init__(self, name, expr, proof, expanded=False):
        self.name = name
        self.expr = expr
        self.proof = proof
        self.expanded = expanded


def _split_implications(expr):
    premises = []
    while isinstance(expr, Implies):
        premises.append(expr.antecedent)
        expr = expr.consequent
    return premises, expr


def _half_terms(expr):
    result = []
    def visit(node):
        if isinstance(node, Div) and isinstance(node.right, Lit) and node.right.value == 2:
            result.append(node)
        for field in getattr(node, "__dataclass_fields__", ()):
            value = getattr(node, field)
            if isinstance(value, Expr):
                visit(value)
            elif isinstance(value, (list, tuple)):
                for item in value:
                    if isinstance(item, Expr):
                        visit(item)
    visit(expr)
    return result


def _clone(facts):
    return [_Fact(fact.name, fact.expr, fact.proof, fact.expanded) for fact in facts]


def _has_fact(facts, expression):
    return any(structural_eq(fact.expr, expression) for fact in facts)


class _Search:
    def __init__(self):
        self.counter = 0
        self.budget = 4000

    def fresh(self, prefix="h"):
        self.counter += 1
        return f"{prefix}{self.counter}"

    def prove(self, goal: Expr, facts: list[_Fact], depth=0):
        if depth > 120:
            raise ProofSearchError(
                f"proof search depth exceeded at {goal!r} with {len(facts)} facts"
            )
        self.budget -= 1
        if self.budget < 0:
            raise ProofSearchError("proof search budget exceeded")

        for fact in reversed(facts):
            if structural_eq(fact.expr, goal):
                return fact.proof

        # Expose conjunctive assumptions once, before any goal-specific rule.
        for fact in facts:
            if isinstance(fact.expr, And) and not fact.expanded:
                fact.expanded = True
                additions = []
                if not _has_fact(facts, fact.expr.left):
                    name = self.fresh("a")
                    additions.append((name, fact.expr.left, AndElimL(fact.proof)))
                if not _has_fact(facts, fact.expr.right):
                    name = self.fresh("a")
                    additions.append((name, fact.expr.right, AndElimR(fact.proof)))
                new_facts = list(facts)
                for name, expression, _derivation in additions:
                    new_facts.append(_Fact(name, expression, HypRef(name)))
                inner = self.prove(goal, new_facts, depth + 1)
                for name, expression, derivation in reversed(additions):
                    inner = Have(name, expression, derivation, inner)
                return inner

        nonneg = self._derive_nonneg_fact(goal, facts, depth)
        if nonneg is not None:
            return nonneg
        half = self._derive_half_fact(goal, facts, depth)
        if half is not None:
            return half
        order = self._derive_negated_order(goal, facts, depth)
        if order is not None:
            return order

        if isinstance(goal, ForallNode):
            if isinstance(goal.body, Implies):
                absence = self._sorted_gap(goal, facts, depth)
                if absence is not None:
                    return absence
            var = Var(goal.var.name, goal.var.type)
            body = substitute_symbols(goal.body, {id(goal.var): var})
            proof = self.prove(body, facts, depth + 1)
            return ForallIntro(var, proof)

        if isinstance(goal, Implies):
            name = self.fresh("p")
            fact = _Fact(name, goal.antecedent, HypRef(name))
            proof = self.prove(goal.consequent, facts + [fact], depth + 1)
            return ImpliesIntro(goal.antecedent, name, proof)

        if isinstance(goal, And):
            left_proof = self.prove(goal.left, facts, depth + 1)
            name = self.fresh("and")
            fact = _Fact(name, goal.left, HypRef(name))
            right_proof = self.prove(goal.right, facts + [fact], depth + 1)
            return Have(name, goal.left, left_proof, AndIntro(HypRef(name), right_proof))

        if isinstance(goal, Or):
            try:
                return OrIntroL(self.prove(goal.left, _clone(facts), depth + 1), goal.right)
            except ProofSearchError:
                pass
            try:
                return OrIntroR(goal.left, self.prove(goal.right, _clone(facts), depth + 1))
            except ProofSearchError:
                pass
            split = self._split_or_hypothesis(goal, facts, depth)
            if split is not None:
                return split
            raise ProofSearchError(f"cannot prove disjunction {_show(goal)}")

        if isinstance(goal, Not):
            law = self._law(goal, facts, depth)
            if law is not None:
                return law
            name = self.fresh("n")
            assumption = _Fact(name, goal.operand, HypRef(name))
            contradiction = self.prove(Lit(False), facts + [assumption], depth + 1)
            return NotIntro(ImpliesIntro(goal.operand, name, contradiction))

        if isinstance(goal, Lit) and goal.value is False:
            result = self._contradiction(facts)
            if result is not None:
                return result
            raise ProofSearchError("cannot derive falsehood")

        if isinstance(goal, Eq):
            if structural_eq(goal.left, goal.right):
                return Refl(goal.left)
            for fact in facts:
                if isinstance(fact.expr, Eq):
                    if structural_eq(fact.expr.left, goal.right) and structural_eq(fact.expr.right, goal.left):
                        return Symm(fact.proof)
                    if structural_eq(fact.expr.left, goal.left) and structural_eq(fact.expr.right, goal.right):
                        return fact.proof
            for fact in facts:
                if isinstance(fact.expr, Lt) and structural_eq(fact.expr.left, goal.left) and structural_eq(fact.expr.right, goal.right):
                    # a < b -> a <= b, then antisymmetry with b <= a if available.
                    pass
            if self._antisymmetry(goal, facts, depth) is not None:
                return self._antisymmetry(goal, facts, depth)
            raise ProofSearchError(f"cannot prove equality {_show(goal)}")

        if isinstance(goal, (Le, Lt)):
            law = self._law(goal, facts, depth)
            if law is not None:
                return law
            terms = farkas(goal, [(fact.name, fact.expr) for fact in facts])
            if terms is not None:
                return Linear(goal, tuple((name, _fraction_text(value)) for name, value in terms.items()))
            falsehood = self._contradiction(facts)
            if falsehood is not None:
                return ExFalso(falsehood, goal)
            raise ProofSearchError(
                f"cannot prove order atom {_show(goal)}; facts="
                + "; ".join(f"{fact.name}: {_show(fact.expr)}" for fact in facts[-12:])
            )

        # Consume a disjunctive fact by cases.
        split = self._split_or_hypothesis(goal, facts, depth)
        if split is not None:
            return split
        # Use an implication whose antecedent is provable.
        for fact in facts:
            if isinstance(fact.expr, Implies):
                try:
                    premise = self.prove(fact.expr.antecedent, facts, depth + 1)
                except ProofSearchError:
                    continue
                name = self.fresh("i")
                derived = ImpliesElim(fact.proof, premise)
                inner = self.prove(goal, facts + [_Fact(name, fact.expr.consequent, HypRef(name))], depth + 1)
                return Have(name, fact.expr.consequent, derived, inner)
        # Instantiate a universal fact with a candidate term.
        for fact in facts:
            if isinstance(fact.expr, ForallNode):
                for candidate in self._candidates(goal, facts):
                    instantiated = substitute_symbols(fact.expr.body, {id(fact.expr.var): candidate})
                    if isinstance(instantiated, Implies):
                        continue
                    name = self.fresh("u")
                    derived = ForallElim(fact.proof, candidate)
                    try:
                        inner = self.prove(goal, facts + [_Fact(name, instantiated, HypRef(name))], depth + 1)
                    except ProofSearchError:
                        continue
                    return Have(name, instantiated, derived, inner)
        raise ProofSearchError(f"no proof found for {_show(goal)}")

    def _derive_nonneg_fact(self, goal, facts, depth):
        """Add 0 <= t for division and product subterms that the goal mentions."""
        if not isinstance(goal, (Le, Lt)):
            return None
        terms = []
        def visit(expr):
            if not isinstance(expr, Expr):
                return
            if isinstance(expr, (Div, Mul)) and not any(structural_eq(expr, item) for item in terms):
                terms.append(expr)
            for field in getattr(expr, "__dataclass_fields__", ()):
                value = getattr(expr, field)
                if isinstance(value, Expr):
                    visit(value)
                elif isinstance(value, list):
                    for item in value:
                        if isinstance(item, tuple):
                            for part in item:
                                visit(part)
                        else:
                            visit(item)
        visit(goal)
        for term in terms:
            statement = Le(Lit(0), term)
            if _has_fact(facts, statement):
                continue
            try:
                proof = self._law(statement, facts, depth + 1)
            except ProofSearchError:
                proof = None
            if proof is None:
                continue
            name = self.fresh("nonneg")
            inner = self.prove(goal, facts + [_Fact(name, statement, HypRef(name))], depth + 1)
            return Have(name, statement, proof, inner)
        return None

    def _derive_half_fact(self, goal, facts, depth):
        for term in _half_terms(goal):
            if not isinstance(term.left, Add):
                continue
            a, b = term.left.left, term.left.right
            lower = Le(Lit(0), term)
            middle = Le(a, term)
            upper = Lt(term, b)
            additions = []
            if not _has_fact(facts, middle):
                try:
                    first = self.prove(Le(Lit(0), a), facts, depth + 1)
                    second = self.prove(Lt(a, b), facts, depth + 1)
                except ProofSearchError:
                    continue
                middle_proof = _apply_law(
                    "half_lower", (a, b), [Le(Lit(0), a), Lt(a, b)], [first, second], middle
                )
                name = self.fresh("half")
                additions.append((name, middle, middle_proof))
            if not _has_fact(facts, lower):
                try:
                    first = self.prove(Le(Lit(0), a), facts, depth + 1)
                    second = self.prove(Lt(a, b), facts, depth + 1)
                except ProofSearchError:
                    continue
                lower_proof = _apply_law(
                    "le_trans",
                    (Lit(0), a, term),
                    [Le(Lit(0), a), middle],
                    [first, middle_proof],
                    lower,
                )
                name = self.fresh("half")
                additions.append((name, lower, lower_proof))
            if not _has_fact(facts, upper):
                try:
                    first = self.prove(Le(Lit(0), a), facts, depth + 1)
                    second = self.prove(Lt(a, b), facts, depth + 1)
                except ProofSearchError:
                    continue
                upper_proof = _apply_law(
                    "half_upper", (a, b), [Le(Lit(0), a), Lt(a, b)], [first, second], upper
                )
                name = self.fresh("half")
                additions.append((name, upper, upper_proof))
            if not additions:
                continue
            new_facts = list(facts)
            for name, expression, _derivation in additions:
                new_facts.append(_Fact(name, expression, HypRef(name)))
            inner = self.prove(goal, new_facts, depth + 1)
            for name, expression, derivation in reversed(additions):
                inner = Have(name, expression, derivation, inner)
            return inner
        return None

    def _derive_negated_order(self, goal, facts, depth):
        if not (isinstance(goal, Lt) and isinstance(goal.right, Nth)):
            return None
        target, xs, index = goal.left, goal.right.seq, goal.right.index
        for fact in facts:
            if not (isinstance(fact.expr, Not) and isinstance(fact.expr.operand, Lt)):
                continue
            operand = fact.expr.operand
            if not (
                isinstance(operand.left, Nth)
                and structural_eq(operand.left.seq, xs)
                and structural_eq(operand.right, target)
            ):
                continue
            mid = operand.left.index
            derived = Lt(target, Nth(xs, mid))
            if _has_fact(facts, derived):
                continue
            has_equality = any(
                isinstance(item.expr, Not)
                and isinstance(item.expr.operand, Eq)
                and (
                    (structural_eq(item.expr.operand.left, Nth(xs, mid)) and structural_eq(item.expr.operand.right, target))
                    or (structural_eq(item.expr.operand.left, target) and structural_eq(item.expr.operand.right, Nth(xs, mid)))
                )
                for item in facts
            )
            if not has_equality:
                continue
            proof = self._trichotomy(derived, facts, depth + 1)
            if proof is None:
                continue
            name = self.fresh("order")
            inner = self.prove(goal, facts + [_Fact(name, derived, HypRef(name))], depth + 1)
            return Have(name, derived, proof, inner)
        return None

    def _contradiction(self, facts):
        for first in facts:
            if isinstance(first.expr, Not):
                for second in facts:
                    if structural_eq(first.expr.operand, second.expr):
                        return NotElim(first.proof, second.proof)
            if isinstance(first.expr, Lit) and first.expr.value is False:
                return first.proof
        terms = farkas(Lit(False), [(fact.name, fact.expr) for fact in facts])
        if terms is not None:
            return Linear(Lit(False), tuple((name, _fraction_text(value)) for name, value in terms.items()))
        return None

    def _split_or_hypothesis(self, goal, facts, depth):
        for fact in facts:
            if isinstance(fact.expr, Or) and not fact.expanded:
                name = self.fresh("c")
                left_fact = _Fact(name, fact.expr.left, HypRef(name))
                right_fact = _Fact(name, fact.expr.right, HypRef(name))
                left_facts = _clone(facts)
                for item in left_facts:
                    if item.name == fact.name:
                        item.expanded = True
                right_facts = _clone(facts)
                for item in right_facts:
                    if item.name == fact.name:
                        item.expanded = True
                left = self.prove(goal, left_facts + [left_fact], depth + 1)
                right = self.prove(goal, right_facts + [right_fact], depth + 1)
                return CaseAnalysis(fact.proof, name, left, right)
        return None

    def _antisymmetry(self, goal, facts, depth):
        if not isinstance(goal, Eq):
            return None
        lower = Le(goal.left, goal.right)
        upper = Le(goal.right, goal.left)
        try:
            forward = self.prove(lower, facts, depth + 1)
            backward = self.prove(upper, facts, depth + 1)
        except ProofSearchError:
            return None
        return _apply_law("le_antisymm", (goal.left, goal.right), [lower, upper], [forward, backward], goal)

    def _candidates(self, goal, facts):
        seen = []
        def visit(expr):
            if isinstance(expr, Expr):
                if not any(structural_eq(expr, item) for item in seen):
                    seen.append(expr)
                for field in getattr(expr, "__dataclass_fields__", ()):
                    value = getattr(expr, field)
                    if isinstance(value, Expr):
                        visit(value)
        visit(goal)
        for fact in facts:
            visit(fact.expr)
        return [item for item in seen if _sort_of(item) is int][:24]

    def _law(self, goal, facts, depth):
        # Direct reflection laws.
        if isinstance(goal, Le) and structural_eq(goal.left, goal.right):
            return CoreLaw("le_refl", (goal.left,))
        if isinstance(goal, Le) and isinstance(goal.left, Lit) and goal.left.value == 0 and isinstance(goal.right, Len):
            return _apply_law("length_nonneg", (goal.right.seq,), [], [], goal)
        if (
            isinstance(goal, Le)
            and isinstance(goal.left, Lit)
            and goal.left.value == 0
            and isinstance(goal.right, Div)
            and isinstance(goal.right.right, Lit)
            and goal.right.right.value == 2
            and isinstance(goal.right.left, Add)
        ):
            a, b = goal.right.left.left, goal.right.left.right
            premises = [Le(Lit(0), a), Lt(a, b)]
            try:
                proofs = [self.prove(item, facts, depth + 1) for item in premises]
            except ProofSearchError:
                proofs = None
            if proofs is not None:
                middle = Le(a, goal.right)
                middle_proof = _apply_law("half_lower", (a, b), premises, proofs, middle)
                return _apply_law(
                    "le_trans",
                    (Lit(0), a, goal.right),
                    [Le(Lit(0), a), middle],
                    [proofs[0], middle_proof],
                    goal,
                )
        if (
            isinstance(goal, Lt)
            and isinstance(goal.left, Div)
            and isinstance(goal.left.right, Lit)
            and goal.left.right.value == 2
            and isinstance(goal.left.left, Add)
        ):
            a, b = goal.left.left.left, goal.left.left.right
            for fact in facts:
                if (
                    isinstance(fact.expr, Le)
                    and structural_eq(fact.expr.left, b)
                    and structural_eq(fact.expr.right, goal.right)
                ):
                    premises = [Le(Lit(0), a), Lt(a, b)]
                    try:
                        proofs = [self.prove(item, facts, depth + 1) for item in premises]
                    except ProofSearchError:
                        continue
                    upper = Lt(goal.left, b)
                    upper_proof = _apply_law("half_upper", (a, b), premises, proofs, upper)
                    return _apply_law(
                        "lt_le_trans",
                        (goal.left, b, goal.right),
                        [upper, fact.expr],
                        [upper_proof, fact.proof],
                        goal,
                    )
        if isinstance(goal, Le) and isinstance(goal.right, Div) and isinstance(goal.right.right, Lit) and goal.right.right.value == 2:
            total = goal.right.left
            if isinstance(total, Add):
                a, b = total.left, total.right
                if structural_eq(a, goal.left):
                    premises = [Le(Lit(0), a), Lt(a, b)]
                    try:
                        proofs = [self.prove(item, facts, depth + 1) for item in premises]
                    except ProofSearchError:
                        proofs = None
                    if proofs is not None:
                        return _apply_law("half_lower", (a, b), premises, proofs, goal)
        if isinstance(goal, Lt) and isinstance(goal.left, Div) and isinstance(goal.left.right, Lit) and goal.left.right.value == 2:
            total = goal.left.left
            if isinstance(total, Add):
                a, b = total.left, total.right
                if structural_eq(b, goal.right):
                    premises = [Le(Lit(0), a), Lt(a, b)]
                    try:
                        proofs = [self.prove(item, facts, depth + 1) for item in premises]
                    except ProofSearchError:
                        proofs = None
                    if proofs is not None:
                        return _apply_law("half_upper", (a, b), premises, proofs, goal)
        if (
            isinstance(goal, Le)
            and isinstance(goal.left, Lit)
            and goal.left.value == 0
            and isinstance(goal.right, Mul)
        ):
            a, b = goal.right.left, goal.right.right
            premises = [Le(Lit(0), a), Le(Lit(0), b)]
            try:
                proofs = [self.prove(item, facts, depth + 1) for item in premises]
            except ProofSearchError:
                proofs = None
            if proofs is not None:
                return _apply_law("mul_nonneg", (a, b), premises, proofs, goal)
        if (
            isinstance(goal, Le)
            and isinstance(goal.left, Lit)
            and goal.left.value == 0
            and isinstance(goal.right, Div)
        ):
            a, b = goal.right.left, goal.right.right
            premises = [Le(Lit(0), a), Lt(Lit(0), b)]
            try:
                proofs = [self.prove(item, facts, depth + 1) for item in premises]
            except ProofSearchError:
                proofs = None
            if proofs is not None:
                return _apply_law("div_nonneg", (a, b), premises, proofs, goal)
        if (
            isinstance(goal, Lt)
            and isinstance(goal.left, Div)
        ):
            a, b = goal.left.left, goal.left.right
            premises = [Lt(Lit(0), a), Lt(Lit(1), b)]
            try:
                proofs = [self.prove(item, facts, depth + 1) for item in premises]
            except ProofSearchError:
                proofs = None
            if proofs is not None:
                base = Lt(Div(a, b), a)
                base_proof = _apply_law("div_lt", (a, b), premises, proofs, base)
                if structural_eq(goal.right, a):
                    return base_proof
                for fact in facts:
                    if not isinstance(fact.expr, Eq):
                        continue
                    equality = None
                    if structural_eq(fact.expr.left, goal.right) and structural_eq(fact.expr.right, a):
                        equality = Symm(fact.proof)
                    elif structural_eq(fact.expr.left, a) and structural_eq(fact.expr.right, goal.right):
                        equality = fact.proof
                    if equality is None:
                        continue
                    target = Var("__div_target", int)
                    template = Lt(Div(a, b), target)
                    return EqSubst(equality, target, template, base_proof)
        if isinstance(goal, Lt) and isinstance(goal.left, Nth):
            xs, i, t = goal.left.seq, goal.left.index, goal.right
            for fact in facts:
                if (
                    isinstance(fact.expr, Lt)
                    and isinstance(fact.expr.left, Nth)
                    and structural_eq(fact.expr.left.seq, xs)
                    and structural_eq(fact.expr.right, t)
                ):
                    mid = fact.expr.left.index
                    premises = [Sorted(xs), Le(Lit(0), i), Le(i, mid), Lt(mid, Len(xs)), fact.expr]
                    try:
                        proofs = [self.prove(item, facts, depth + 1) for item in premises]
                    except ProofSearchError:
                        continue
                    return _apply_law("sorted_lower", (xs, i, mid, t), premises, proofs, goal)
        if isinstance(goal, Lt) and isinstance(goal.right, Nth):
            t, xs, i = goal.left, goal.right.seq, goal.right.index
            for fact in facts:
                if (
                    isinstance(fact.expr, Lt)
                    and isinstance(fact.expr.right, Nth)
                    and structural_eq(fact.expr.right.seq, xs)
                    and structural_eq(fact.expr.left, t)
                ):
                    mid = fact.expr.right.index
                    premises = [Sorted(xs), Le(Lit(0), mid), Le(mid, i), Lt(i, Len(xs)), fact.expr]
                    try:
                        proofs = [self.prove(item, facts, depth + 1) for item in premises]
                    except ProofSearchError:
                        continue
                    return _apply_law("sorted_upper", (xs, mid, i, t), premises, proofs, goal)
        if isinstance(goal, ForallNode) and isinstance(goal.body, Implies):
            # sorted_gap concludes an absence quantifier.
            maybe = self._sorted_gap(goal, facts, depth)
            if maybe is not None:
                return maybe
        if isinstance(goal, Le):
            for fact in facts:
                if (
                    isinstance(fact.expr, Lt)
                    and structural_eq(fact.expr.left, goal.left)
                    and isinstance(fact.expr.right, Add)
                    and isinstance(fact.expr.right.right, Lit)
                    and fact.expr.right.right.value == 1
                    and structural_eq(fact.expr.right.left, goal.right)
                ):
                    return _apply_law(
                        "lt_add_one_le",
                        (goal.left, goal.right),
                        [fact.expr],
                        [fact.proof],
                        goal,
                    )
        if (
            isinstance(goal, Le)
            and isinstance(goal.left, Add)
            and isinstance(goal.left.right, Lit)
            and goal.left.right.value == 1
        ):
            for fact in facts:
                if isinstance(fact.expr, Lt) and structural_eq(fact.expr.left, goal.left.left) and structural_eq(fact.expr.right, goal.right):
                    return _apply_law(
                        "lt_succ_le",
                        (goal.left.left, goal.right),
                        [fact.expr],
                        [fact.proof],
                        goal,
                    )
        if isinstance(goal, Lt):
            tri = self._trichotomy(goal, facts, depth)
            if tri is not None:
                return tri
        # Search a shared middle term for the transitive order laws.
        for fact in facts:
            if not isinstance(fact.expr, (Le, Lt)):
                continue
            for other in facts:
                if not isinstance(other.expr, (Le, Lt)):
                    continue
                if not structural_eq(fact.expr.right, other.expr.left):
                    continue
                a, b, c = fact.expr.left, fact.expr.right, other.expr.right
                candidates = []
                if isinstance(fact.expr, Le) and isinstance(other.expr, Le) and isinstance(goal, Le):
                    candidates.append(("le_trans", (a, b, c), [fact.expr, other.expr]))
                if isinstance(fact.expr, Le) and isinstance(other.expr, Lt) and isinstance(goal, Lt):
                    candidates.append(("le_lt_trans", (a, b, c), [fact.expr, other.expr]))
                if isinstance(fact.expr, Lt) and isinstance(other.expr, Le) and isinstance(goal, Lt):
                    candidates.append(("lt_le_trans", (a, b, c), [fact.expr, other.expr]))
                if isinstance(fact.expr, Lt) and isinstance(other.expr, Lt) and isinstance(goal, Lt):
                    candidates.append(("lt_trans", (a, b, c), [fact.expr, other.expr]))
                for law, args, premises in candidates:
                    if structural_eq(law_statement(law, args), goal):
                        return _apply_law(law, args, premises, [fact.proof, other.proof], goal)
        if isinstance(goal, Le):
            for fact in facts:
                if isinstance(fact.expr, Lt) and structural_eq(fact.expr.left, goal.left) and structural_eq(fact.expr.right, goal.right):
                    return _apply_law("lt_to_le", (goal.left, goal.right), [fact.expr], [fact.proof], goal)
                if (
                    isinstance(fact.expr, Not)
                    and isinstance(fact.expr.operand, Lt)
                    and structural_eq(fact.expr.operand.left, goal.right)
                    and structural_eq(fact.expr.operand.right, goal.left)
                ):
                    return _apply_law("not_lt_le", (goal.right, goal.left), [fact.expr], [fact.proof], goal)
        if isinstance(goal, Not) and isinstance(goal.operand, Lt):
            a, b = goal.operand.left, goal.operand.right
            if structural_eq(a, b):
                return CoreLaw("lt_irrefl", (a,))
            for fact in facts:
                if isinstance(fact.expr, Lt) and structural_eq(fact.expr.left, a) and structural_eq(fact.expr.right, b):
                    name = self.fresh("neq")
                    inner = _apply_law("lt_neq", (a, b), [fact.expr], [fact.proof], Not(Eq(a, b)))
                    # The law gives ~(a=b); equality symmetry transports it.
                    inner = _transport_neq(a, b, inner)
                    proof = self.prove(goal, facts + [_Fact(name, Not(Eq(b, a)), inner)], depth + 1)
                    return Have(name, Not(Eq(b, a)), inner, proof)
        if isinstance(goal, Not) and isinstance(goal.operand, Eq):
            a, b = goal.operand.left, goal.operand.right
            for law, first, second in (("lt_neq", a, b), ("lt_neq", b, a)):
                for fact in facts:
                    if isinstance(fact.expr, Lt) and structural_eq(fact.expr.left, first) and structural_eq(fact.expr.right, second):
                        inner = _apply_law(law, (first, second), [fact.expr], [fact.proof], Not(Eq(first, second)))
                        if structural_eq(Not(Eq(first, second)), goal):
                            return inner
                        if first == b and second == a:
                            return _transport_neq(b, a, inner)
        return None

    def _sorted_gap(self, goal, facts, depth):
        # Recognize the absence shape and recover low/high from the two cut facts.
        body = goal.body
        if not isinstance(body, Implies):
            return None
        # Unwrap 0 <= i -> i < len(xs) -> ~(nth(xs,i) = t)
        condition = body.antecedent
        inner = body.consequent
        if not isinstance(inner, Implies):
            return None
        length_condition = inner.antecedent
        conclusion = inner.consequent
        if not isinstance(length_condition, Lt) or not isinstance(conclusion, Not) or not isinstance(conclusion.operand, Eq):
            return None
        read = conclusion.operand.left
        target = conclusion.operand.right
        if not isinstance(read, Nth):
            return None
        xs = read.seq
        lower = None
        upper = None
        for fact in facts:
            if not isinstance(fact.expr, ForallNode):
                continue
            premises, conclusion = _split_implications(fact.expr.body)
            if not isinstance(conclusion, Lt):
                continue
            if (
                isinstance(conclusion.left, Nth)
                and structural_eq(conclusion.left.seq, xs)
                and structural_eq(conclusion.right, target)
            ):
                for premise in premises:
                    if isinstance(premise, Lt):
                        lower = (fact, premise.right)
            if (
                isinstance(conclusion.right, Nth)
                and structural_eq(conclusion.right.seq, xs)
                and structural_eq(conclusion.left, target)
            ):
                for premise in premises:
                    if isinstance(premise, Le):
                        upper = (fact, premise.left)
        if lower is None or upper is None:
            return None
        low = lower[1]
        high = upper[1]
        premises = [
            Sorted(xs),
            Le(Lit(0), low),
            Le(low, high),
            Le(high, Len(xs)),
            lower[0].expr,
            upper[0].expr,
            Le(high, low),
        ]
        try:
            proofs = [self.prove(item, facts, depth + 1) for item in premises]
        except ProofSearchError:
            return None
        return _apply_law("sorted_gap", (xs, low, high, target), premises, proofs, goal)

    def _trichotomy(self, goal, facts, depth):
        if not isinstance(goal, Lt):
            return None
        a, b = goal.left, goal.right
        not_lt = None
        not_eq = None
        for fact in facts:
            if not isinstance(fact.expr, Not):
                continue
            operand = fact.expr.operand
            if isinstance(operand, Lt) and structural_eq(operand.left, b) and structural_eq(operand.right, a):
                not_lt = fact
            if isinstance(operand, Eq):
                if structural_eq(operand.left, a) and structural_eq(operand.right, b):
                    not_eq = fact
                elif structural_eq(operand.left, b) and structural_eq(operand.right, a):
                    not_eq = _Fact("_eq_sym", Not(Eq(a, b)), _transport_neq(b, a, fact.proof))
        if not_lt is None or not_eq is None:
            return None
        outer = CoreLaw("lt_trichotomy", (a, b))
        outer_name = self.fresh("tri")
        inner_name = self.fresh("tri")
        middle = ExFalso(NotElim(not_eq.proof, HypRef(inner_name)), goal)
        third = ExFalso(NotElim(not_lt.proof, HypRef(inner_name)), goal)
        inner = CaseAnalysis(HypRef(outer_name), inner_name, middle, third)
        return CaseAnalysis(outer, outer_name, HypRef(outer_name), inner)



def _apply_law(law, args, premises, proofs, goal):
    statement = law_statement(law, args)
    expected_goal = goal
    proof = CoreLaw(law, args)
    for premise, premise_proof in zip(premises, proofs):
        proof = ImpliesElim(proof, premise_proof)
    # Some law conclusions are not the goal itself (for example after
    # implication chains); compare structurally and reject a bad application.
    if not structural_eq(law_statement(law, args), statement):
        raise ProofSearchError("internal law mismatch")
    if not _concludes(statement, goal, len(premises)):
        raise ProofSearchError(f"law {law} does not conclude {goal!r}")
    return proof


def _alpha_eq(left, right):
    if type(left) is not type(right):
        return False
    if isinstance(left, (ForallNode, ExistsNode)):
        body = substitute_symbols(left.body, {id(left.var): right.var})
        return _alpha_eq(body, right.body)
    if isinstance(left, Implies):
        return _alpha_eq(left.antecedent, right.antecedent) and _alpha_eq(left.consequent, right.consequent)
    if isinstance(left, Expr) and hasattr(left, "__dataclass_fields__"):
        for field in left.__dataclass_fields__:
            lvalue, rvalue = getattr(left, field), getattr(right, field)
            if isinstance(lvalue, Expr):
                if not _alpha_eq(lvalue, rvalue):
                    return False
            elif lvalue != rvalue:
                return False
        return True
    return structural_eq(left, right)


def _concludes(statement, goal, premises):
    current = statement
    for _ in range(premises):
        if not isinstance(current, Implies):
            return False
        current = current.consequent
    return _alpha_eq(current, goal)


def _transport_neq(a, b, proof):
    # proof: ~(a = b); derive ~(b = a) by assuming b = a and symmetry.
    name = "neq_sym"
    assumed = HypRef(name)
    symmetric = CoreLaw("eq_symm", (b, a))
    equality = ImpliesElim(symmetric, assumed)  # a = b
    falsehood = NotElim(proof, equality)
    return NotIntro(ImpliesIntro(Eq(b, a), name, falsehood))


def _sort_of(expr):
    if isinstance(expr, Var):
        return expr.type
    if isinstance(expr, Lit):
        return type(expr.value)
    if isinstance(expr, (Add, Sub, Mul, Div, Neg, Len, Nth)):
        return int
    if isinstance(expr, (Eq, Le, Lt, And, Or, Not, Implies, Sorted, ForallNode, ExistsNode)):
        return bool
    return None


def _fraction_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def prove_condition(goal: Expr):
    search = _Search()
    return search.prove(goal, [])


def build_program_obligations(program: Program) -> dict:
    conditions = verification_conditions(program)
    result = {}
    for name, goal in conditions.items():
        try:
            result[name] = prove_condition(goal)
        except ProofSearchError as error:
            raise ProofSearchError(f"{name}: {error}") from error
    return result
