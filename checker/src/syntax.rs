use num_bigint::BigInt;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Sort {
    Prop,
    Int,
    Seq,
}

impl Sort {
    pub fn name(self) -> &'static str {
        match self {
            Self::Prop => "prop",
            Self::Int => "int",
            Self::Seq => "seq",
        }
    }
}

// Bound occurrences are de Bruijn indices. Names on binders are display labels.
#[derive(Clone, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
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
    Len {
        seq: Box<Self>,
    },
    Nth {
        seq: Box<Self>,
        index: Box<Self>,
    },
    Sorted {
        seq: Box<Self>,
    },
    Div {
        left: Box<Self>,
        right: Box<Self>,
    },
    Eq {
        left: Box<Self>,
        right: Box<Self>,
    },
    Le {
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
            Le { left, right } => binary!(Le, recurse(left), recurse(right)),
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
            Len { seq } => Len {
                seq: Box::new(recurse(seq)),
            },
            Nth { seq, index } => Nth {
                seq: Box::new(recurse(seq)),
                index: Box::new(recurse(index)),
            },
            Sorted { seq } => Sorted {
                seq: Box::new(recurse(seq)),
            },
            Div { left, right } => binary!(Div, recurse(left), recurse(right)),
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
                | Le { left, right }
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
        Div { left, right } => {
            let left = child(left, fuel)?;
            let right = child(right, fuel)?;
            match (&left, &right) {
                (Int { value: a }, Int { value: b }) => {
                    let (a, b) = (integer(a)?, integer(b)?);
                    if b == 0.into() {
                        return Err("integer division by zero".into());
                    }
                    literal(a / b)
                }
                _ => Ok(binary!(Div, left, right)),
            }
        }
        Len { seq } => Ok(Len {
            seq: Box::new(child(seq, fuel)?),
        }),
        Nth { seq, index } => Ok(Nth {
            seq: Box::new(child(seq, fuel)?),
            index: Box::new(child(index, fuel)?),
        }),
        Sorted { seq } => Ok(Sorted {
            seq: Box::new(child(seq, fuel)?),
        }),
        Eq { left, right } => Ok(binary!(Eq, child(left, fuel)?, child(right, fuel)?)),
        Le { left, right } => Ok(binary!(Le, child(left, fuel)?, child(right, fuel)?)),
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
            Neg { operand }
            | Not { operand }
            | Pow { base: operand, .. }
            | Len { seq: operand }
            | Sorted { seq: operand } => visit(operand, depth, rest, bound),
            Forall { body, .. } | Exists { body, .. } => visit(body, depth + 1, rest, bound),
            Add { left, right }
            | Sub { left, right }
            | Mul { left, right }
            | Eq { left, right }
            | Le { left, right }
            | Lt { left, right }
            | And { left, right }
            | Or { left, right }
            | Implies { left, right } => {
                let rest = visit(left, depth, rest, bound);
                visit(right, depth, rest, bound)
            }
            Div { left, right } => {
                let rest = visit(left, depth, rest, bound);
                visit(right, depth, rest, bound)
            }
            Nth { seq, index } => {
                let rest = visit(seq, depth, rest, bound);
                visit(index, depth, rest, bound)
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

fn int(value: &str) -> Proposition {
    Int {
        value: value.into(),
    }
}
fn add(a: Proposition, b: Proposition) -> Proposition {
    binary!(Add, a, b)
}
fn mul(a: Proposition, b: Proposition) -> Proposition {
    binary!(Mul, a, b)
}
fn neg(operand: Proposition) -> Proposition {
    Neg {
        operand: Box::new(operand),
    }
}
fn lt(a: Proposition, b: Proposition) -> Proposition {
    binary!(Lt, a, b)
}
fn le(a: Proposition, b: Proposition) -> Proposition {
    binary!(Le, a, b)
}
fn eq(a: Proposition, b: Proposition) -> Proposition {
    binary!(Eq, a, b)
}
fn not(operand: Proposition) -> Proposition {
    Not {
        operand: Box::new(operand),
    }
}
fn implies(left: Proposition, right: Proposition) -> Proposition {
    binary!(Implies, left, right)
}
fn or(left: Proposition, right: Proposition) -> Proposition {
    binary!(Or, left, right)
}
fn len(seq: Proposition) -> Proposition {
    Len { seq: Box::new(seq) }
}
fn nth(seq: Proposition, index: Proposition) -> Proposition {
    Nth {
        seq: Box::new(seq),
        index: Box::new(index),
    }
}
fn sorted(seq: Proposition) -> Proposition {
    Sorted { seq: Box::new(seq) }
}
fn div(left: Proposition, right: Proposition) -> Proposition {
    binary!(Div, left, right)
}
fn half(a: Proposition, b: Proposition) -> Proposition {
    div(add(a.clone(), b), Int { value: "2".into() })
}
fn forall_int(body: Proposition) -> Proposition {
    Forall {
        name: "i".into(),
        sort: Sort::Int,
        body: Box::new(body),
    }
}

pub fn law_formals(id: &str) -> Option<&'static [&'static str]> {
    Some(match id {
        "add_assoc" | "mul_assoc" | "distrib" => &["a", "b", "c"],
        "add_comm" | "mul_comm" | "lt_neq" | "le_antisymm" | "le_total" | "lt_trichotomy"
        | "lt_to_le" | "not_lt_le" | "eq_symm" => &["a", "b"],
        "add_zero" | "lt_irrefl" | "le_refl" => &["a"],
        "add_inverse" | "mul_one" => &["a"],
        "lt_trans" | "lt_add" | "le_trans" | "le_lt_trans" | "lt_le_trans" | "le_add" => {
            &["a", "b", "c"]
        }
        "lt_succ_le" | "lt_add_one_le" => &["a", "b"],
        "half_lower" | "half_upper" => &["a", "b"],
        "length_nonneg" => &["xs"],
        "sorted_elim" => &["xs", "i", "j"],
        "sorted_lower" | "sorted_upper" | "sorted_gap" => &["xs", "a", "b", "t"],
        _ => return None,
    })
}

pub fn law_sorts(id: &str) -> Option<&'static [Sort]> {
    Some(match id {
        "sorted_elim" => &[Sort::Seq, Sort::Int, Sort::Int],
        "length_nonneg" => &[Sort::Seq],
        "sorted_lower" | "sorted_upper" | "sorted_gap" => {
            &[Sort::Seq, Sort::Int, Sort::Int, Sort::Int]
        }
        _ => &[],
    })
}

pub fn law_arg_sorts(id: &str) -> Vec<Sort> {
    let arity = law_formals(id).map(|names| names.len()).unwrap_or(0);
    let sequence = law_sorts(id).unwrap_or(&[]);
    (0..arity)
        .map(|index| sequence.get(index).copied().unwrap_or(Sort::Int))
        .collect()
}

pub fn instantiate_law(id: &str, args: &[Proposition]) -> Option<Proposition> {
    let a = args.first().cloned();
    let b = args.get(1).cloned();
    let c = args.get(2).cloned();
    let body = match id {
        "add_assoc" => eq(
            add(add(a.clone()?, b.clone()?), c.clone()?),
            add(a?, add(b?, c?)),
        ),
        "add_comm" => eq(add(a.clone()?, b.clone()?), add(b?, a?)),
        "add_zero" => eq(add(a.clone()?, int("0")), a?),
        "add_inverse" => eq(add(a.clone()?, neg(a?)), int("0")),
        "mul_assoc" => eq(
            mul(mul(a.clone()?, b.clone()?), c.clone()?),
            mul(a?, mul(b?, c?)),
        ),
        "mul_comm" => eq(mul(a.clone()?, b.clone()?), mul(b?, a?)),
        "mul_one" => eq(mul(a.clone()?, int("1")), a?),
        "distrib" => eq(
            mul(a.clone()?, add(b.clone()?, c.clone()?)),
            add(mul(a.clone()?, b?), mul(a?, c?)),
        ),
        "lt_irrefl" => not(lt(a.clone()?, a?)),
        "lt_trans" => implies(
            lt(a.clone()?, b.clone()?),
            implies(lt(b?, c.clone()?), lt(a?, c?)),
        ),
        "lt_add" => implies(
            lt(a.clone()?, b.clone()?),
            lt(add(a?, c.clone()?), add(b?, c?)),
        ),
        "lt_neq" => implies(lt(a.clone()?, b.clone()?), not(eq(a?, b?))),
        "le_refl" => le(a.clone()?, a?),
        "le_trans" => implies(
            le(a.clone()?, b.clone()?),
            implies(le(b?, c.clone()?), le(a?, c?)),
        ),
        "le_antisymm" => implies(
            le(a.clone()?, b.clone()?),
            implies(le(b.clone()?, a.clone()?), eq(a?, b?)),
        ),
        "le_lt_trans" => implies(
            le(a.clone()?, b.clone()?),
            implies(lt(b?, c.clone()?), lt(a?, c?)),
        ),
        "lt_le_trans" => implies(
            lt(a.clone()?, b.clone()?),
            implies(le(b?, c.clone()?), lt(a?, c?)),
        ),
        "le_total" => or(le(a.clone()?, b.clone()?), le(b?, a?)),
        "lt_trichotomy" => or(
            lt(a.clone()?, b.clone()?),
            or(eq(a.clone()?, b.clone()?), lt(b?, a?)),
        ),
        "lt_to_le" => implies(lt(a.clone()?, b.clone()?), le(a?, b?)),
        "lt_succ_le" => implies(
            lt(a.clone()?, b.clone()?),
            le(add(a.clone()?, int("1")), b?),
        ),
        "lt_add_one_le" => implies(lt(a.clone()?, add(b.clone()?, int("1"))), le(a?, b?)),
        "le_add" => implies(
            le(a.clone()?, b.clone()?),
            le(add(a?, c.clone()?), add(b?, c?)),
        ),
        "not_lt_le" => implies(not(lt(a.clone()?, b.clone()?)), le(b?, a?)),
        "eq_symm" => implies(eq(a.clone()?, b.clone()?), eq(b?, a?)),
        "half_lower" => implies(
            le(int("0"), a.clone()?),
            implies(lt(a.clone()?, b.clone()?), le(a.clone()?, half(a?, b?))),
        ),
        "half_upper" => implies(
            le(int("0"), a.clone()?),
            implies(lt(a.clone()?, b.clone()?), lt(half(a?, b.clone()?), b?)),
        ),
        "length_nonneg" => le(int("0"), len(a?)),
        "sorted_elim" => {
            let xs = a?;
            let i = b?;
            let j = c?;
            implies(
                sorted(xs.clone()),
                implies(
                    le(int("0"), i.clone()),
                    implies(
                        le(i.clone(), j.clone()),
                        implies(
                            lt(j.clone(), len(xs.clone())),
                            le(nth(xs.clone(), i), nth(xs, j)),
                        ),
                    ),
                ),
            )
        }
        "sorted_lower" => {
            let xs = a?;
            let i = b?;
            let mid = c?;
            let t = args.get(3).cloned()?;
            implies(
                sorted(xs.clone()),
                implies(
                    le(int("0"), i.clone()),
                    implies(
                        le(i.clone(), mid.clone()),
                        implies(
                            lt(mid.clone(), len(xs.clone())),
                            implies(lt(nth(xs.clone(), mid), t.clone()), lt(nth(xs, i), t)),
                        ),
                    ),
                ),
            )
        }
        "sorted_upper" => {
            let xs = a?;
            let mid = b?;
            let i = c?;
            let t = args.get(3).cloned()?;
            implies(
                sorted(xs.clone()),
                implies(
                    le(int("0"), mid.clone()),
                    implies(
                        le(mid.clone(), i.clone()),
                        implies(
                            lt(i.clone(), len(xs.clone())),
                            implies(lt(t.clone(), nth(xs.clone(), mid)), lt(t, nth(xs, i))),
                        ),
                    ),
                ),
            )
        }
        "sorted_gap" => {
            let xs = a?;
            let low = b?;
            let high = c?;
            let t = args.get(3).cloned()?;
            // The quantified cuts use a fresh index and shift the outer terms.
            let at = |term: &Proposition| term.shift(1);
            let xs1 = at(&xs);
            let low1 = at(&low);
            let high1 = at(&high);
            let t1 = at(&t);
            let index = prop_bound(0);
            let lower_cut = forall_int(implies(
                le(int("0"), index.clone()),
                implies(
                    lt(index.clone(), low1.clone()),
                    lt(nth(xs1.clone(), index.clone()), t1.clone()),
                ),
            ));
            let upper_cut = forall_int(implies(
                le(high1.clone(), index.clone()),
                implies(
                    lt(index.clone(), len(xs1.clone())),
                    lt(t1.clone(), nth(xs1.clone(), index.clone())),
                ),
            ));
            let absent = forall_int(implies(
                le(int("0"), index.clone()),
                implies(
                    lt(index.clone(), len(xs1.clone())),
                    not(eq(nth(xs1.clone(), index.clone()), t1.clone())),
                ),
            ));
            implies(
                sorted(xs.clone()),
                implies(
                    le(int("0"), low.clone()),
                    implies(
                        le(low.clone(), high.clone()),
                        implies(
                            le(high.clone(), len(xs.clone())),
                            implies(
                                lower_cut,
                                implies(upper_cut, implies(le(high, low), absent)),
                            ),
                        ),
                    ),
                ),
            )
        }
        _ => return None,
    };
    Some(body)
}

fn prop_bound(index: usize) -> Proposition {
    Bound { index }
}
