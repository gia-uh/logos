"""Proof-producing normalization of integer polynomials."""
from dataclasses import dataclass

from logos.expr import Add, Eq, Expr, Lit, Mul, Neg, Pow, Sub, Var
from logos.kernel import Block, Congr, CoreLaw, ProofTerm, Refl, StepRef, Symm, Trans
from logos.runner import TacticFailed


@dataclass(frozen=True)
class Equation:
    left: Expr
    right: Expr
    # A missing step means the two endpoints are definitionally convertible.
    step: StepRef | None = None


class Ring:
    def __init__(self):
        self.steps: list[ProofTerm] = []
        self.variables: dict[int, int] = {}
        self.normalized: dict[tuple, Equation] = {}
        self.hole = Var("hole", int)

    def emit(self, left, right, evidence):
        if len(self.steps) >= 4_000:
            raise TacticFailed("ring: derivation exceeds the proof size limit")
        step = StepRef(len(self.steps))
        self.steps.append(evidence)
        return Equation(left, right, step)

    def key(self, term):
        match term:
            case Lit(value) if type(value) is int:
                return ("int", value)
            case Var(_, type_) if type_ is int:
                return ("var", self.variables.setdefault(id(term), len(self.variables)))
            case Add(left, right) | Mul(left, right) | Sub(left, right) | Pow(left, right):
                return (type(term).__name__, self.key(left), self.key(right))
            case Neg(operand):
                return ("neg", self.key(operand))
            case _:
                raise TacticFailed(f"ring: unsupported integer term {term!r}")

    def law(self, name, a, b=None, c=None):
        match name:
            case "add_assoc":
                left, right, args = (a + b) + c, a + (b + c), (a, b, c)
            case "add_comm":
                left, right, args = a + b, b + a, (a, b)
            case "add_zero":
                left, right, args = a + 0, a, (a,)
            case "add_inverse":
                left, right, args = a + -a, Lit(0), (a,)
            case "mul_assoc":
                left, right, args = (a * b) * c, a * (b * c), (a, b, c)
            case "mul_comm":
                left, right, args = a * b, b * a, (a, b)
            case "mul_one":
                left, right, args = a * 1, a, (a,)
            case "distrib":
                left, right, args = a * (b + c), a * b + a * c, (a, b, c)
            case _:
                raise ValueError(f"unknown ring law {name!r}")
        return self.emit(left, right, CoreLaw(name, args))

    def reverse(self, eq):
        if eq.step is None:
            return Equation(eq.right, eq.left)
        return self.emit(eq.right, eq.left, Symm(eq.step))

    def chain(self, first, *rest):
        result = first
        for eq in rest:
            if result.step is not None and eq.step is not None:
                result = self.emit(result.left, eq.right, Trans(result.step, eq.step))
            else:
                result = Equation(result.left, eq.right, result.step or eq.step)
        return result

    def lift(self, context, eq):
        left, right = context(eq.left), context(eq.right)
        if eq.step is None:
            return Equation(left, right)
        return self.emit(left, right, Congr(self.hole, context(self.hole), eq.step))

    def left_zero(self, a):
        return self.chain(self.law("add_comm", Lit(0), a), self.law("add_zero", a))

    def cancel_left(self, a, b):
        """Derive −a + (a + b) = b."""
        return self.chain(
            self.reverse(self.law("add_assoc", -a, a, b)),
            self.lift(lambda t: t + b, self.chain(
                self.law("add_comm", -a, a), self.law("add_inverse", a),
            )),
            self.left_zero(b),
        )

    def times_zero(self, a):
        """Distribution gives q + q = q for q = a*0. Cancel q."""
        zero = Lit(0)
        q = a * zero
        repeated = self.reverse(self.law("distrib", a, zero, zero))
        equal_sums = self.chain(repeated, self.reverse(self.law("add_zero", q)))
        return self.chain(
            self.reverse(self.cancel_left(q, q)),
            self.lift(lambda t: -q + t, equal_sums),
            self.cancel_left(q, zero),
        )

    def as_product(self, a):
        """Derive a = 1*a."""
        return self.reverse(self.chain(
            self.law("mul_comm", Lit(1), a), self.law("mul_one", a),
        ))

    def factor(self, a, b, monomial):
        """Derive a*m + b*m = (a+b)*m using the pinned left distributive law."""
        return self.chain(
            self.lift(lambda t: t + b * monomial, self.law("mul_comm", a, monomial)),
            self.lift(lambda t: monomial * a + t, self.law("mul_comm", b, monomial)),
            self.reverse(self.law("distrib", monomial, a, b)),
            self.law("mul_comm", monomial, a + b),
        )

    def neg_as_product(self, a):
        """Both (−1)*a and −a add to zero against a. Cancel a."""
        minus_one = Lit(-1)
        zero = Lit(0)
        negative = minus_one * a
        equal_sums = self.chain(
            self.lift(lambda t: t + negative, self.as_product(a)),
            self.factor(Lit(1), minus_one, a),
            self.law("mul_comm", zero, a),
            self.times_zero(a),
            self.reverse(self.law("add_inverse", a)),
        )
        return self.reverse(self.chain(
            self.reverse(self.cancel_left(a, negative)),
            self.lift(lambda t: -a + t, equal_sums),
            self.cancel_left(a, -a),
        ))

    def coefficients(self, term):
        if isinstance(term, Lit):
            return term.value, None
        if isinstance(term, Mul) and isinstance(term.left, Lit):
            return term.left.value, term.right
        return 1, term

    def monomial_key(self, term):
        _, factors = self.coefficients(term)
        return self.key(factors) if factors is not None else ()

    def factor_key(self, factor):
        # Integer factors form one coefficient regardless of their values.
        return () if isinstance(factor, Lit) else self.key(factor)

    def add_coefficients(self, left, right):
        a, factors = self.coefficients(left)
        b, _ = self.coefficients(right)
        value = Lit(a + b)
        if factors is None:
            return Equation(left + right, value)
        left_factor = self.as_product(left) if left is factors else Equation(left, left)
        _, right_factors = self.coefficients(right)
        right_factor = self.as_product(right) if right is right_factors else Equation(right, right)
        return self.chain(
            self.lift(lambda t: t + right, left_factor),
            self.lift(lambda t: left_factor.right + t, right_factor),
            self.factor(Lit(a), Lit(b), factors),
            self.join(Mul, value, factors),
        )

    def join(self, op, left, right):
        """Join ordered operands, removing the operator's unit and zero factors."""
        if isinstance(left, Lit) and isinstance(right, Lit):
            value = left.value + right.value if op is Add else left.value * right.value
            return Equation(op(left, right), Lit(value))
        if op is Add:
            if isinstance(left, Lit) and left.value == 0:
                return self.left_zero(right)
            if isinstance(right, Lit) and right.value == 0:
                return self.law("add_zero", left)
        else:
            if isinstance(left, Lit) and left.value == 0:
                return self.chain(self.law("mul_comm", left, right), self.times_zero(right))
            if isinstance(right, Lit) and right.value == 0:
                return self.times_zero(left)
            if isinstance(left, Lit) and left.value == 1:
                return self.chain(self.law("mul_comm", left, right), self.law("mul_one", right))
            if isinstance(right, Lit) and right.value == 1:
                return self.law("mul_one", left)
        return Equation(op(left, right), op(left, right))

    def insert(self, op, item, tail):
        """Insert into a sorted, right-associated sum or product."""
        name = "add" if op is Add else "mul"
        key = self.monomial_key if op is Add else self.factor_key
        first = tail.left if isinstance(tail, op) else tail
        rest = tail.right if isinstance(tail, op) else None
        if key(item) > key(first):
            if rest is None:
                return self.chain(self.law(f"{name}_comm", item, first), self.join(op, first, item))
            swap = self.chain(
                self.reverse(self.law(f"{name}_assoc", item, first, rest)),
                self.lift(lambda t: op(t, rest), self.law(f"{name}_comm", item, first)),
                self.law(f"{name}_assoc", first, item, rest),
            )
            inserted = self.insert(op, item, rest)
            return self.chain(
                swap, self.lift(lambda t: op(first, t), inserted),
                self.insert(op, first, inserted.right),
            )
        joined = (
            self.add_coefficients(item, first)
            if op is Add and key(item) == key(first) else self.join(op, item, first)
        )
        if rest is None:
            return joined
        if joined.step is None and self.key(joined.right) == self.key(op(item, first)):
            return Equation(op(item, tail), op(item, tail))
        return self.chain(
            self.reverse(self.law(f"{name}_assoc", item, first, rest)),
            self.lift(lambda t: op(t, rest), joined), self.join(op, joined.right, rest),
        )

    def merge(self, op, left, right):
        """Merge sorted, right-associated operands of an associative operator."""
        if not isinstance(left, op):
            return self.insert(op, left, right)
        a, b = left.left, left.right
        merged = self.merge(op, b, right)
        name = "add" if op is Add else "mul"
        return self.chain(
            self.law(f"{name}_assoc", a, b, right),
            self.lift(lambda t: op(a, t), merged),
            self.insert(op, a, merged.right),
        )

    def multiply(self, left, right):
        if isinstance(right, Add):
            a, b = right.left, right.right
            first = self.multiply(left, a)
            second = self.multiply(left, b)
            return self.chain(
                self.law("distrib", left, a, b),
                self.lift(lambda t: t + left * b, first),
                self.lift(lambda t: first.right + t, second),
                self.merge(Add, first.right, second.right),
            )
        if isinstance(left, Add):
            return self.chain(self.law("mul_comm", left, right), self.multiply(right, left))
        return self.merge(Mul, left, right)

    def normalize(self, expr):
        key = self.key(expr)
        if key not in self.normalized:
            self.normalized[key] = self.normalize_uncached(expr)
        return self.normalized[key]

    def normalize_uncached(self, expr):
        match expr:
            case Add(a, Neg(b)) if self.key(a) == self.key(b):
                return self.law("add_inverse", a)
            case Add(left, right) | Mul(left, right):
                op = type(expr)
                a, b = self.normalize(left), self.normalize(right)
                reduced = self.merge(Add, a.right, b.right) if op is Add else self.multiply(a.right, b.right)
                return self.chain(
                    self.lift(lambda t: op(t, right), a),
                    self.lift(lambda t: op(a.right, t), b),
                    reduced,
                )
            case Neg(Lit(value)):
                return Equation(expr, Lit(-value))
            case Neg(operand):
                return self.chain(self.neg_as_product(operand), self.normalize(Lit(-1) * operand))
            case Sub(left, right):
                return self.chain(Equation(expr, left + -right), self.normalize(left + -right))
            case Pow(base, Lit(n)) if type(n) is int and 0 <= n <= 128:
                expanded = Lit(1)
                for _ in range(n):
                    expanded = expanded * base
                return self.chain(Equation(expr, expanded), self.normalize(expanded))
            case Var() | Lit():
                return Equation(expr, expr)
            case _:
                raise TacticFailed(f"ring: unsupported integer term {expr!r}")

    def prove(self, goal):
        if not isinstance(goal, Eq):
            raise TacticFailed(f"ring: goal is not an equation, got {goal!r}")
        # Visit the two originals first so ordering follows first occurrence,
        # including distinct variables that share the same display name.
        self.key(goal.left)
        self.key(goal.right)
        lhs, rhs = self.normalize(goal.left), self.normalize(goal.right)
        if self.key(lhs.right) != self.key(rhs.right):
            raise TacticFailed("ring: the two sides have different polynomial normal forms")
        result = self.chain(lhs, self.reverse(rhs))
        if result.step is None:
            return Refl(goal.left)
        if isinstance(self.steps[result.step.index], CoreLaw):
            return self.steps[result.step.index]
        return Block(tuple(self.steps), result.step.index)
