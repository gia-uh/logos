use num_bigint::BigInt;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Sort {
    Prop,
    Int,
}

impl Sort {
    pub fn name(self) -> &'static str {
        match self {
            Self::Prop => "prop",
            Self::Int => "int",
        }
    }
}

// Bound occurrences are de Bruijn indices. Names on binders are display labels.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "tag", rename_all = "snake_case", deny_unknown_fields)]
pub enum Proposition {
    Symbol {
        id: String,
    },
    Bound {
        index: usize,
    },
    Int {
        value: String,
    },
    Add {
        left: Box<Self>,
        right: Box<Self>,
    },
    Sub {
        left: Box<Self>,
        right: Box<Self>,
    },
    Mul {
        left: Box<Self>,
        right: Box<Self>,
    },
    Neg {
        operand: Box<Self>,
    },
    Pow {
        base: Box<Self>,
        exponent: u32,
    },
    Eq {
        left: Box<Self>,
        right: Box<Self>,
    },
    Lt {
        left: Box<Self>,
        right: Box<Self>,
    },
    And {
        left: Box<Self>,
        right: Box<Self>,
    },
    Or {
        left: Box<Self>,
        right: Box<Self>,
    },
    Not {
        operand: Box<Self>,
    },
    False,
    Implies {
        left: Box<Self>,
        right: Box<Self>,
    },
    Forall {
        name: String,
        sort: Sort,
        body: Box<Self>,
    },
    Exists {
        name: String,
        sort: Sort,
        body: Box<Self>,
    },
    App {
        id: String,
        args: Vec<Self>,
    },
}

use Proposition::*;

macro_rules! binary {
    ($op:ident, $left:expr, $right:expr) => {
        $op {
            left: Box::new($left),
            right: Box::new($right),
        }
    };
}

#[derive(Clone, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Function {
    pub id: String,
    pub name: String,
    pub params: Vec<Sort>,
    pub result: Sort,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub body: Option<Proposition>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub recursor: Option<Recursor>,
}

/// A primitive-recursive definition on the natural numbers.
///
/// `base` is a closed integer term. `step` is an integer term with two
/// integer binders: the argument (outer) and its previous value (inner).
/// A step may call the recursive function only at the argument itself.
#[derive(Clone, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Recursor {
    pub base: Proposition,
    pub step: Proposition,
}

pub type Functions<'a> = HashMap<&'a str, &'a Function>;

// Rewrite bound variables while tracking how many binders enclose the occurrence.
impl Proposition {
    fn map_bound(&self, depth: usize, f: &impl Fn(usize, usize) -> Self) -> Self {
        let recurse = |term: &Self| term.map_bound(depth, f);
        match self {
            Bound { index } => f(*index, depth),
            Add { left, right } => binary!(Add, recurse(left), recurse(right)),
            Sub { left, right } => binary!(Sub, recurse(left), recurse(right)),
            Mul { left, right } => binary!(Mul, recurse(left), recurse(right)),
            Eq { left, right } => binary!(Eq, recurse(left), recurse(right)),
            Lt { left, right } => binary!(Lt, recurse(left), recurse(right)),
            And { left, right } => binary!(And, recurse(left), recurse(right)),
            Or { left, right } => binary!(Or, recurse(left), recurse(right)),
            Not { operand } => Not {
                operand: Box::new(recurse(operand)),
            },
            Implies { left, right } => binary!(Implies, recurse(left), recurse(right)),
            Neg { operand } => Neg {
                operand: Box::new(recurse(operand)),
            },
            Pow { base, exponent } => Pow {
                base: Box::new(recurse(base)),
                exponent: *exponent,
            },
            Forall { name, sort, body } => Forall {
                name: name.clone(),
                sort: *sort,
                body: Box::new(body.map_bound(depth + 1, f)),
            },
            Exists { name, sort, body } => Exists {
                name: name.clone(),
                sort: *sort,
                body: Box::new(body.map_bound(depth + 1, f)),
            },
            App { id, args } => App {
                id: id.clone(),
                args: args.iter().map(recurse).collect(),
            },
            Symbol { .. } | Int { .. } | False => self.clone(),
        }
    }

    pub fn shift(&self, by: usize) -> Self {
        self.map_bound(0, &|index, depth| Bound {
            index: if index >= depth { index + by } else { index },
        })
    }

    /// Close the innermost binder, failing when the term still mentions it.
    pub fn lower_outer(&self) -> Result<Self, String> {
        let escaped = std::cell::Cell::new(false);
        let result = self.map_bound(0, &|index, depth| {
            if index == depth {
                escaped.set(true);
                Bound { index }
            } else if index > depth {
                Bound { index: index - 1 }
            } else {
                Bound { index }
            }
        });
        if escaped.get() {
            Err("eigenvariable escapes the conclusion".into())
        } else {
            Ok(result)
        }
    }

    fn instantiate(&self, args: &[Self]) -> Self {
        self.map_bound(0, &|index, depth| {
            if index < depth {
                Bound { index }
            } else if let Some(arg) = args.get(index - depth) {
                arg.shift(depth)
            } else {
                Bound {
                    index: index - args.len(),
                }
            }
        })
    }
}

/// Instantiate a one-binder predicate template at a target scope.
///
/// `new_binders` counts the binders between the template's outer scope and
/// the target, including the binder that replaces the template's own binder.
/// For ordinary universal elimination the template binder is removed, so
/// `new_binders` is zero. For an induction or least-element conclusion the
/// replacement binder stays in scope, so it is one or more.
pub fn instantiate_predicate(
    body: &Proposition,
    new_binders: usize,
    term: &Proposition,
) -> Proposition {
    body.map_bound(0, &|index, depth| {
        if index == depth {
            term.shift(depth)
        } else if index > depth {
            Bound {
                index: index - 1 + new_binders,
            }
        } else {
            Bound { index }
        }
    })
}

impl Proposition {
    fn children(&self) -> &[Self] {
        match self {
            App { args, .. } => args,
            _ => &[],
        }
    }

    pub fn weight(&self) -> Result<usize, String> {
        fn visit(term: &Proposition, depth: usize, weight: &mut usize) -> Result<(), String> {
            if depth > MAX_DEPTH || *weight > CONVERSION_LIMIT * 4 {
                return Err("inferred expression exceeds resource limit".into());
            }
            *weight += 64
                + match term {
                    Symbol { id } | App { id, .. } => id.len(),
                    Int { value } => value.len(),
                    Forall { name, .. } | Exists { name, .. } => name.len(),
                    _ => 0,
                };
            match term {
                Neg { operand }
                | Not { operand }
                | Pow { base: operand, .. }
                | Forall { body: operand, .. }
                | Exists { body: operand, .. } => visit(operand, depth + 1, weight)?,
                Add { left, right }
                | Sub { left, right }
                | Mul { left, right }
                | Eq { left, right }
                | Lt { left, right }
                | And { left, right }
                | Or { left, right }
                | Implies { left, right } => {
                    visit(left, depth + 1, weight)?;
                    visit(right, depth + 1, weight)?;
                }
                _ => {
                    for child in term.children() {
                        visit(child, depth + 1, weight)?;
                    }
                }
            }
            Ok(())
        }
        let mut weight = 0;
        visit(self, 0, &mut weight)?;
        Ok(weight)
    }
}

const MAX_INT_BITS: u64 = 65_536;
const MAX_DEPTH: usize = 160;
const CONVERSION_LIMIT: usize = 200_000;

pub fn integer(value: &str) -> Result<BigInt, String> {
    if value.len() > 20_000 {
        return Err("integer literal exceeds resource limit".into());
    }
    let digits = value.strip_prefix('-').unwrap_or(value);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return Err("invalid signed decimal integer literal".into());
    }
    value
        .parse()
        .map_err(|_| "invalid signed decimal integer literal".into())
}

fn literal(value: BigInt) -> Result<Proposition, String> {
    if value.bits() > MAX_INT_BITS {
        return Err("integer conversion exceeds resource limit".into());
    }
    Ok(Int {
        value: value.to_string(),
    })
}

impl Sort {
    pub fn expect(self, expected: Self) -> Result<(), String> {
        if self == expected {
            Ok(())
        } else {
            Err(format!(
                "has sort {}, expected {}",
                self.name(),
                expected.name()
            ))
        }
    }
}

pub fn convert(expr: &Proposition, functions: &Functions<'_>) -> Result<Proposition, String> {
    let mut fuel = CONVERSION_LIMIT;
    let normal = normalize(expr, functions, 0, &mut fuel)?;
    normal.weight()?;
    Ok(normal)
}

fn normalize(
    expr: &Proposition,
    functions: &Functions<'_>,
    depth: usize,
    fuel: &mut usize,
) -> Result<Proposition, String> {
    let spend = |fuel: &mut usize| -> Result<(), String> {
        if depth > MAX_DEPTH || *fuel == 0 {
            return Err("conversion exceeds resource limit".into());
        }
        *fuel -= 1;
        Ok(())
    };
    spend(fuel)?;
    let child = |term, fuel: &mut usize| normalize(term, functions, depth + 1, fuel);
    let combine = |left, right, multiply| match (&left, &right) {
        (Int { value: a }, Int { value: b }) => {
            let (a, b) = (integer(a)?, integer(b)?);
            literal(if multiply { a * b } else { a + b })
        }
        _ if multiply => Ok(binary!(Mul, left, right)),
        _ => Ok(binary!(Add, left, right)),
    };
    match expr {
        Symbol { .. } | Bound { .. } | False => Ok(expr.clone()),
        Int { value } => literal(integer(value)?),
        Add { left, right } | Mul { left, right } => combine(
            child(left, fuel)?,
            child(right, fuel)?,
            matches!(expr, Mul { .. }),
        ),
        Sub { left, right } => {
            let left = child(left, fuel)?;
            let right = child(right, fuel)?;
            combine(left, negate(right)?, false)
        }
        Neg { operand } => negate(child(operand, fuel)?),
        Pow { base, exponent } => {
            if *exponent == 0 {
                return literal(1.into());
            }
            let once = child(base, fuel)?;
            if let Int { value } = &once {
                return exact_power(integer(value)?, *exponent);
            }
            if *exponent > MAX_DEPTH.saturating_sub(depth) as u32 {
                return Err("power conversion exceeds resource limit".into());
            }
            // The specified expansion starts from 1, even for a symbolic base.
            let mut result = Int { value: "1".into() };
            for nesting in (1..=*exponent as usize).rev() {
                spend(fuel)?;
                result = combine(
                    result,
                    normalize(base, functions, depth + nesting, fuel)?,
                    true,
                )?;
            }
            Ok(result)
        }
        Eq { left, right } => Ok(binary!(Eq, child(left, fuel)?, child(right, fuel)?)),
        Lt { left, right } => Ok(binary!(Lt, child(left, fuel)?, child(right, fuel)?)),
        And { left, right } => Ok(binary!(And, child(left, fuel)?, child(right, fuel)?)),
        Or { left, right } => Ok(binary!(Or, child(left, fuel)?, child(right, fuel)?)),
        Not { operand } => Ok(Not {
            operand: Box::new(child(operand, fuel)?),
        }),
        Implies { left, right } => Ok(binary!(Implies, child(left, fuel)?, child(right, fuel)?)),
        Forall { sort, body, .. } => Ok(Forall {
            name: String::new(),
            sort: *sort,
            body: Box::new(child(body, fuel)?),
        }),
        Exists { sort, body, .. } => Ok(Exists {
            name: String::new(),
            sort: *sort,
            body: Box::new(child(body, fuel)?),
        }),
        App { id, args } => {
            let mut args = args
                .iter()
                .map(|arg| child(arg, fuel))
                .collect::<Result<Vec<_>, _>>()?;
            if let Some(body) = &functions[id.as_str()].body {
                args.reverse();
                // Charge each copy before materializing a definition expansion.
                let instantiated = instantiate_with_fuel(body, &args, fuel)?;
                child(&instantiated, fuel)
            } else {
                Ok(App {
                    id: id.clone(),
                    args,
                })
            }
        }
    }
}

fn exact_power(mut base: BigInt, mut exponent: u32) -> Result<Proposition, String> {
    let mut value = BigInt::from(1);
    while exponent != 0 {
        if exponent % 2 == 1 {
            value *= &base;
            if value.bits() > MAX_INT_BITS {
                return Err("integer conversion exceeds resource limit".into());
            }
        }
        exponent /= 2;
        if exponent != 0 {
            base = &base * &base;
            if base.bits() > MAX_INT_BITS {
                return Err("integer conversion exceeds resource limit".into());
            }
        }
    }
    literal(value)
}

fn negate(term: Proposition) -> Result<Proposition, String> {
    match term {
        Int { value } => literal(-integer(&value)?),
        _ => Ok(Neg {
            operand: Box::new(term),
        }),
    }
}

pub fn instantiate_bounded(
    body: &Proposition,
    args: &[Proposition],
) -> Result<Proposition, String> {
    let mut fuel = CONVERSION_LIMIT;
    instantiate_with_fuel(body, args, &mut fuel)
}

fn instantiate_with_fuel(
    body: &Proposition,
    args: &[Proposition],
    fuel: &mut usize,
) -> Result<Proposition, String> {
    // Count occurrences and argument sizes without allocating expanded syntax.
    fn visit(
        term: &Proposition,
        depth: usize,
        remaining: usize,
        bound: &mut impl FnMut(usize, usize) -> usize,
    ) -> usize {
        if remaining == 0 {
            return 0;
        }
        let rest = remaining.saturating_sub(
            64 + match term {
                Symbol { id } | App { id, .. } => id.len(),
                Int { value } => value.len(),
                Forall { name, .. } | Exists { name, .. } => name.len(),
                _ => 0,
            },
        );
        match term {
            Bound { index } => rest.saturating_sub(bound(*index, depth)),
            Neg { operand } | Not { operand } | Pow { base: operand, .. } => {
                visit(operand, depth, rest, bound)
            }
            Forall { body, .. } | Exists { body, .. } => visit(body, depth + 1, rest, bound),
            Add { left, right }
            | Sub { left, right }
            | Mul { left, right }
            | Eq { left, right }
            | Lt { left, right }
            | And { left, right }
            | Or { left, right }
            | Implies { left, right } => {
                let rest = visit(left, depth, rest, bound);
                visit(right, depth, rest, bound)
            }
            App { args, .. } => args
                .iter()
                .fold(rest, |rest, arg| visit(arg, depth, rest, bound)),
            _ => rest,
        }
    }
    let sizes = args
        .iter()
        .map(Proposition::weight)
        .collect::<Result<Vec<_>, _>>()?;
    *fuel = visit(body, 0, *fuel, &mut |index, depth| {
        index
            .checked_sub(depth)
            .and_then(|i| sizes.get(i))
            .copied()
            .unwrap_or(0)
    });
    if *fuel == 0 {
        return Err("definition conversion exceeds resource limit".into());
    }
    let result = body.instantiate(args);
    result.weight()?;
    Ok(result)
}

macro_rules! integer_laws {
    ($int:ident, $add:ident, $mul:ident, $neg:ident, $lt:ident, $eq:ident, $not:ident, $or:ident, $implies:ident;
     $($law:literal ($($var:ident),*) => $left:expr, $right:expr;)*
     [$($order:literal ($($ovar:ident),*) => $body:expr;)*]) => {
        pub fn law_formals(id: &str) -> Option<&'static [&'static str]> {
            match id {
                $($law => Some(&[$(stringify!($var)),*]),)*
                $($order => Some(&[$(stringify!($ovar)),*]),)*
                _ => None,
            }
        }

        pub fn instantiate_law(id: &str, args: &[Proposition]) -> Option<Proposition> {
            let $int = |value: &str| Int { value: value.into() };
            let $add = |a, b| binary!(Add, a, b);
            let $mul = |a, b| binary!(Mul, a, b);
            let $neg = |operand| Neg { operand: Box::new(operand) };
            let $lt = |a, b| binary!(Lt, a, b);
            let $eq = |a, b| binary!(Eq, a, b);
            let $not = |operand| Not { operand: Box::new(operand) };
            let $or = |left, right| binary!(Or, left, right);
            let $implies = |left, right| binary!(Implies, left, right);
            match (id, args) {
                $(($law, [$($var),*]) => Some(binary!(Eq, $left, $right)),)*
                $(($order, [$($ovar),*]) => Some($body),)*
                _ => None,
            }
        }
    };
}

integer_laws! {
    int, add, mul, neg, lt, eq, not, or, implies;
    "add_assoc"(a, b, c) => add(add(a.clone(), b.clone()), c.clone()), add(a.clone(), add(b.clone(), c.clone()));
    "add_comm"(a, b) => add(a.clone(), b.clone()), add(b.clone(), a.clone());
    "add_zero"(a) => add(a.clone(), int("0")), a.clone();
    "add_inverse"(a) => add(a.clone(), neg(a.clone())), int("0");
    "mul_assoc"(a, b, c) => mul(mul(a.clone(), b.clone()), c.clone()), mul(a.clone(), mul(b.clone(), c.clone()));
    "mul_comm"(a, b) => mul(a.clone(), b.clone()), mul(b.clone(), a.clone());
    "mul_one"(a) => mul(a.clone(), int("1")), a.clone();
    "distrib"(a, b, c) => mul(a.clone(), add(b.clone(), c.clone())), add(mul(a.clone(), b.clone()), mul(a.clone(), c.clone()));
    [
        "lt_irrefl"(a) => not(lt(a.clone(), a.clone()));
        "lt_trans"(a, b, c) => implies(lt(a.clone(), b.clone()), implies(lt(b.clone(), c.clone()), lt(a.clone(), c.clone())));
        "lt_add"(a, b, c) => implies(lt(a.clone(), b.clone()), lt(add(a.clone(), c.clone()), add(b.clone(), c.clone())));
        "lt_neq"(a, b) => implies(lt(a.clone(), b.clone()), not(eq(a.clone(), b.clone())));
        "mul_pos"(a, b) => implies(lt(int("0"), a.clone()), implies(lt(int("0"), b.clone()), lt(int("0"), mul(a.clone(), b.clone()))));
        "mul_eq_one"(a, b) => implies(eq(mul(a.clone(), b.clone()), int("1")), or(eq(a.clone(), int("1")), eq(a.clone(), int("-1"))));
        "lt_succ_fwd"(a, b) => implies(lt(a.clone(), add(b.clone(), int("1"))), not(lt(b.clone(), a.clone())));
        "lt_succ_rev"(a, b) => implies(not(lt(b.clone(), a.clone())), lt(a.clone(), add(b.clone(), int("1"))));
        "eq_of_not_lt_not_lt"(a, b) => implies(not(lt(a.clone(), b.clone())), implies(not(lt(b.clone(), a.clone())), eq(a.clone(), b.clone())));
        "lt_decidable"(a, b) => or(lt(a.clone(), b.clone()), not(lt(a.clone(), b.clone())));
    ]
}
