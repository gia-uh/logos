//! Checked linear integer arithmetic certificates.
//!
//! A certificate is a non-negative rational combination of local inequality
//! hypotheses together with the negation of the claimed inequality. If the
//! combination cancels every atom and leaves a false constant relation, the
//! claim follows over the rationals and therefore over the integers. Equality
//! hypotheses may carry either sign because a multiple of an equality is
//! still zero.

use num_bigint::BigInt;
use std::collections::BTreeMap;

use crate::Proposition;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Rational {
    numerator: BigInt,
    denominator: BigInt,
}

impl Rational {
    fn new(numerator: BigInt, denominator: BigInt) -> Result<Self, String> {
        if denominator == BigInt::from(0) {
            return Err("linear: zero denominator".into());
        }
        let mut numerator = numerator;
        let mut denominator = denominator;
        if denominator < BigInt::from(0) {
            numerator = -numerator;
            denominator = -denominator;
        }
        let divisor = gcd(numerator.clone(), denominator.clone());
        if divisor != BigInt::from(1) && divisor != BigInt::from(0) {
            numerator /= &divisor;
            denominator /= &divisor;
        }
        Ok(Self {
            numerator,
            denominator,
        })
    }

    pub fn parse(value: &str) -> Result<Self, String> {
        if value.len() > 2000 {
            return Err("linear: coefficient exceeds resource limit".into());
        }
        let (numerator, denominator) = match value.split_once('/') {
            Some((left, right)) => (left, right),
            None => (value, "1"),
        };
        let numerator = numerator
            .parse::<BigInt>()
            .map_err(|_| format!("linear: invalid numerator {numerator:?}"))?;
        let denominator = denominator
            .parse::<BigInt>()
            .map_err(|_| format!("linear: invalid denominator {denominator:?}"))?;
        Self::new(numerator, denominator)
    }

    fn zero() -> Self {
        Self::new(BigInt::from(0), BigInt::from(1)).expect("zero is valid")
    }

    fn one() -> Self {
        Self::new(BigInt::from(1), BigInt::from(1)).expect("one is valid")
    }

    fn from_integer(value: BigInt) -> Self {
        Self::new(value, BigInt::from(1)).expect("integer is valid")
    }

    fn add(&self, other: &Self) -> Self {
        Self::new(
            &self.numerator * &other.denominator + &other.numerator * &self.denominator,
            &self.denominator * &other.denominator,
        )
        .expect("common denominator is nonzero")
    }

    fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    fn mul(&self, other: &Self) -> Self {
        Self::new(
            &self.numerator * &other.numerator,
            &self.denominator * &other.denominator,
        )
        .expect("product denominator is nonzero")
    }

    fn neg(&self) -> Self {
        Self {
            numerator: -self.numerator.clone(),
            denominator: self.denominator.clone(),
        }
    }

    fn is_zero(&self) -> bool {
        self.numerator == BigInt::from(0)
    }

    fn is_negative(&self) -> bool {
        self.numerator < BigInt::from(0)
    }

    fn sign(&self) -> i8 {
        if self.numerator < BigInt::from(0) {
            -1
        } else if self.numerator > BigInt::from(0) {
            1
        } else {
            0
        }
    }
}

fn gcd(mut left: BigInt, mut right: BigInt) -> BigInt {
    if left < BigInt::from(0) {
        left = -left;
    }
    if right < BigInt::from(0) {
        right = -right;
    }
    while right != BigInt::from(0) {
        let remainder = &left % &right;
        left = right;
        right = remainder;
    }
    if left == BigInt::from(0) {
        BigInt::from(1)
    } else {
        left
    }
}

#[derive(Clone, Debug)]
pub struct Constraint {
    coeffs: BTreeMap<Proposition, Rational>,
    constant: Rational,
    strict: bool,
    size: usize,
}

impl Constraint {
    fn zero() -> Self {
        Self {
            coeffs: BTreeMap::new(),
            constant: Rational::zero(),
            strict: false,
            size: 0,
        }
    }

    fn add_term(&mut self, atom: Proposition, coefficient: Rational) {
        if coefficient.is_zero() {
            return;
        }
        let next = match self.coeffs.get(&atom) {
            Some(current) => current.add(&coefficient),
            None => coefficient,
        };
        if next.is_zero() {
            self.coeffs.remove(&atom);
        } else {
            self.coeffs.insert(atom, next);
        }
        self.recompute_size();
    }

    fn add_constant(&mut self, value: Rational) {
        self.constant = self.constant.add(&value);
    }

    fn recompute_size(&mut self) {
        self.size = self.coeffs.len() + 1;
    }

    fn scale(&self, factor: &Rational) -> Self {
        let mut result = Constraint::zero();
        result.strict = self.strict;
        result.constant = self.constant.mul(factor);
        for (atom, coefficient) in &self.coeffs {
            let value = coefficient.mul(factor);
            if !value.is_zero() {
                result.coeffs.insert(atom.clone(), value);
            }
        }
        result.recompute_size();
        result
    }

    fn combine(&self, other: &Self, factor: &Rational) -> Self {
        let mut result = self.scale(&Rational::one());
        let other = other.scale(factor);
        result.strict |= other.strict;
        result.add_constant(other.constant.clone());
        for (atom, coefficient) in other.coeffs {
            result.add_term(atom, coefficient);
        }
        result
    }

    fn falsehood(&self) -> bool {
        if !self.coeffs.is_empty() {
            return false;
        }
        if self.strict {
            self.constant.sign() >= 0
        } else {
            self.constant.sign() > 0
        }
    }
}

fn atom(term: &Proposition) -> Result<Proposition, String> {
    match term {
        Proposition::Int { .. }
        | Proposition::Add { .. }
        | Proposition::Sub { .. }
        | Proposition::Mul { .. }
        | Proposition::Neg { .. } => Err("linear: expected an atomic term".into()),
        _ => Ok(term.clone()),
    }
}

/// Turn an integer expression into `coeffs + constant`.
pub fn linearize(
    term: &Proposition,
) -> Result<(BTreeMap<Proposition, Rational>, Rational), String> {
    match term {
        Proposition::Int { value } => {
            let value = value
                .parse::<BigInt>()
                .map_err(|_| "linear: invalid integer literal".to_string())?;
            Ok((BTreeMap::new(), Rational::from_integer(value)))
        }
        Proposition::Add { left, right } => {
            let (mut lc, lv) = linearize(left)?;
            let (rc, rv) = linearize(right)?;
            for (atom, coefficient) in rc {
                let value = lc
                    .get(&atom)
                    .cloned()
                    .unwrap_or_else(Rational::zero)
                    .add(&coefficient);
                if value.is_zero() {
                    lc.remove(&atom);
                } else {
                    lc.insert(atom, value);
                }
            }
            Ok((lc, lv.add(&rv)))
        }
        Proposition::Sub { left, right } => {
            let (mut lc, lv) = linearize(left)?;
            let (rc, rv) = linearize(right)?;
            for (atom, coefficient) in rc {
                let value = lc
                    .get(&atom)
                    .cloned()
                    .unwrap_or_else(Rational::zero)
                    .sub(&coefficient);
                if value.is_zero() {
                    lc.remove(&atom);
                } else {
                    lc.insert(atom, value);
                }
            }
            Ok((lc, lv.sub(&rv)))
        }
        Proposition::Neg { operand } => {
            let (coeffs, constant) = linearize(operand)?;
            Ok((
                coeffs
                    .into_iter()
                    .map(|(atom, coefficient)| (atom, coefficient.neg()))
                    .collect(),
                constant.neg(),
            ))
        }
        Proposition::Mul { left, right } => match (literal(left)?, literal(right)?) {
            (Some(value), None) => {
                let (coeffs, constant) = linearize(right)?;
                let factor = Rational::from_integer(value);
                Ok((
                    coeffs
                        .into_iter()
                        .map(|(atom, coefficient)| (atom, coefficient.mul(&factor)))
                        .collect(),
                    constant.mul(&factor),
                ))
            }
            (None, Some(value)) => {
                let (coeffs, constant) = linearize(left)?;
                let factor = Rational::from_integer(value);
                Ok((
                    coeffs
                        .into_iter()
                        .map(|(atom, coefficient)| (atom, coefficient.mul(&factor)))
                        .collect(),
                    constant.mul(&factor),
                ))
            }
            _ => {
                let mut coeffs = BTreeMap::new();
                coeffs.insert(atom(term)?, Rational::one());
                Ok((coeffs, Rational::zero()))
            }
        },
        _ => {
            let mut coeffs = BTreeMap::new();
            coeffs.insert(atom(term)?, Rational::one());
            Ok((coeffs, Rational::zero()))
        }
    }
}

fn literal(term: &Proposition) -> Result<Option<BigInt>, String> {
    match term {
        Proposition::Int { value } => {
            Ok(Some(value.parse::<BigInt>().map_err(|_| {
                "linear: invalid integer literal".to_string()
            })?))
        }
        _ => Ok(None),
    }
}

/// Parse a top-level order atom. `direction` is `-1` for `Not`, never used here.
pub fn constraint(term: &Proposition) -> Result<Constraint, String> {
    let (left, right, strict, equality) = match term {
        Proposition::Le { left, right } => (left, right, false, false),
        Proposition::Lt { left, right } => (left, right, true, false),
        Proposition::Eq { left, right } => (left, right, false, true),
        _ => return Err("linear: premise is not an arithmetic order or equality".into()),
    };
    let (mut coeffs, lv) = linearize(left)?;
    let (rc, rv) = linearize(right)?;
    for (atom, coefficient) in rc {
        let value = coeffs
            .get(&atom)
            .cloned()
            .unwrap_or_else(Rational::zero)
            .sub(&coefficient);
        if value.is_zero() {
            coeffs.remove(&atom);
        } else {
            coeffs.insert(atom, value);
        }
    }
    let constant = lv.sub(&rv);
    let mut result = Constraint::zero();
    result.coeffs = coeffs;
    result.constant = constant;
    result.strict = strict;
    result.size = result.coeffs.len() + 1;
    if equality {
        // Represent an equality as a non-strict constraint with a marker handled by
        // the caller: an equality may be scaled by either sign.
    }
    Ok(result)
}

pub fn is_equality(term: &Proposition) -> bool {
    matches!(term, Proposition::Eq { .. })
}

/// Check that `terms` plus the negation of `conclusion` is contradictory.
pub fn verify(
    conclusion: &Proposition,
    terms: &[(String, Rational)],
    hypotheses: &[(String, Proposition)],
) -> Result<(), String> {
    let mut total = Constraint::zero();
    for (binder, coefficient) in terms {
        let (_, hypothesis) = hypotheses
            .iter()
            .rev()
            .find(|(name, _)| name == binder)
            .ok_or_else(|| format!("linear: unknown hypothesis {binder:?}"))?;
        let equality = is_equality(hypothesis);
        if !equality && coefficient.is_negative() {
            return Err(format!(
                "linear: a non-negative coefficient is required for inequality {binder:?}"
            ));
        }
        let constraint = constraint(hypothesis)?;
        total = total.combine(&constraint, coefficient);
        total.strict |= constraint.strict && !coefficient.is_zero();
        total.recompute_size();
    }
    match conclusion {
        Proposition::False => {}
        Proposition::Le { .. } | Proposition::Lt { .. } => {
            let negated = match conclusion {
                Proposition::Le { left, right } => Proposition::Lt {
                    left: right.clone(),
                    right: left.clone(),
                },
                Proposition::Lt { left, right } => Proposition::Le {
                    left: right.clone(),
                    right: left.clone(),
                },
                _ => unreachable!(),
            };
            let constraint = constraint(&negated)?;
            total = total.combine(&constraint, &Rational::one());
            total.strict |= constraint.strict;
            total.recompute_size();
        }
        _ => return Err("linear: conclusion must be an order atom or falsehood".into()),
    }
    if total.falsehood() {
        Ok(())
    } else {
        Err(format!(
            "linear: the certified combination is not contradictory for {conclusion:?}: constant={:?} strict={} atoms={}",
            total.constant,
            total.strict,
            total.coeffs.len()
        ))
    }
}
