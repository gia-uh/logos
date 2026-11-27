//! Executable loop programs and their verification conditions.
//!
//! Expressions in a program use declaration IDs for program variables. The
//! conditions below are closed over those variables before they are checked.

use serde::Deserialize;
use std::collections::{BTreeMap, HashSet};

use crate::Proposition;

#[derive(Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Program {
    pub id: String,
    pub function: String,
    pub params: Vec<String>,
    pub locals: Vec<String>,
    #[serde(default)]
    pub ghosts: Vec<String>,
    pub result: String,
    pub requires: Proposition,
    pub ensures: Proposition,
    pub body: Vec<Statement>,
    #[serde(default)]
    pub obligations: Vec<Obligation>,
}

#[derive(Clone, Deserialize)]
#[serde(tag = "tag", rename_all = "snake_case", deny_unknown_fields)]
pub enum Statement {
    Assign {
        name: String,
        value: Proposition,
    },
    If {
        condition: Proposition,
        then_body: Vec<Statement>,
        else_body: Vec<Statement>,
    },
    While {
        condition: Proposition,
        body: Vec<Statement>,
        invariant: Proposition,
        variant: Proposition,
    },
    Return {
        value: Proposition,
    },
}

#[derive(Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Obligation {
    pub id: String,
    pub proof: crate::Evidence,
}

impl Program {
    /// Variables in the order in which conditions are closed over them.
    pub fn variables(&self) -> Vec<&str> {
        self.params
            .iter()
            .chain(self.locals.iter())
            .chain(self.ghosts.iter())
            .chain(std::iter::once(&self.result))
            .map(String::as_str)
            .collect()
    }
}

fn subst(expr: &Proposition, mapping: &BTreeMap<String, Proposition>) -> Proposition {
    use Proposition::*;
    match expr {
        Symbol { id } => mapping.get(id).cloned().unwrap_or_else(|| expr.clone()),
        Bound { .. } | Int { .. } | False => expr.clone(),
        Add { left, right } => Add {
            left: Box::new(subst(left, mapping)),
            right: Box::new(subst(right, mapping)),
        },
        Sub { left, right } => Sub {
            left: Box::new(subst(left, mapping)),
            right: Box::new(subst(right, mapping)),
        },
        Mul { left, right } => Mul {
            left: Box::new(subst(left, mapping)),
            right: Box::new(subst(right, mapping)),
        },
        Div { left, right } => Div {
            left: Box::new(subst(left, mapping)),
            right: Box::new(subst(right, mapping)),
        },
        Neg { operand } => Neg {
            operand: Box::new(subst(operand, mapping)),
        },
        Pow { base, exponent } => Pow {
            base: Box::new(subst(base, mapping)),
            exponent: *exponent,
        },
        Len { seq } => Len {
            seq: Box::new(subst(seq, mapping)),
        },
        Nth { seq, index } => Nth {
            seq: Box::new(subst(seq, mapping)),
            index: Box::new(subst(index, mapping)),
        },
        Sorted { seq } => Sorted {
            seq: Box::new(subst(seq, mapping)),
        },
        Eq { left, right } => Eq {
            left: Box::new(subst(left, mapping)),
            right: Box::new(subst(right, mapping)),
        },
        Le { left, right } => Le {
            left: Box::new(subst(left, mapping)),
            right: Box::new(subst(right, mapping)),
        },
        Lt { left, right } => Lt {
            left: Box::new(subst(left, mapping)),
            right: Box::new(subst(right, mapping)),
        },
        And { left, right } => And {
            left: Box::new(subst(left, mapping)),
            right: Box::new(subst(right, mapping)),
        },
        Or { left, right } => Or {
            left: Box::new(subst(left, mapping)),
            right: Box::new(subst(right, mapping)),
        },
        Not { operand } => Not {
            operand: Box::new(subst(operand, mapping)),
        },
        Implies { left, right } => Implies {
            left: Box::new(subst(left, mapping)),
            right: Box::new(subst(right, mapping)),
        },
        Forall { name, sort, body } | Exists { name, sort, body } => {
            let body = subst(body, mapping);
            if matches!(expr, Forall { .. }) {
                Forall {
                    name: name.clone(),
                    sort: *sort,
                    body: Box::new(body),
                }
            } else {
                Exists {
                    name: name.clone(),
                    sort: *sort,
                    body: Box::new(body),
                }
            }
        }
        App { id, args } => App {
            id: id.clone(),
            args: args.iter().map(|arg| subst(arg, mapping)).collect(),
        },
    }
}

fn substitute_one(expr: &Proposition, name: &str, value: &Proposition) -> Proposition {
    let mut mapping = BTreeMap::new();
    mapping.insert(name.to_owned(), value.clone());
    subst(expr, &mapping)
}

fn and(left: Proposition, right: Proposition) -> Proposition {
    Proposition::And {
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn or(left: Proposition, right: Proposition) -> Proposition {
    Proposition::Or {
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn not(operand: Proposition) -> Proposition {
    Proposition::Not {
        operand: Box::new(operand),
    }
}

fn implies(left: Proposition, right: Proposition) -> Proposition {
    Proposition::Implies {
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn le(left: Proposition, right: Proposition) -> Proposition {
    Proposition::Le {
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn lt(left: Proposition, right: Proposition) -> Proposition {
    Proposition::Lt {
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn eq(left: Proposition, right: Proposition) -> Proposition {
    Proposition::Eq {
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn symbol(id: &str) -> Proposition {
    Proposition::Symbol { id: id.to_owned() }
}

fn int(value: i64) -> Proposition {
    Proposition::Int {
        value: value.to_string(),
    }
}

fn len(seq: Proposition) -> Proposition {
    Proposition::Len { seq: Box::new(seq) }
}

struct Generator<'a> {
    program: &'a Program,
    obligations: Vec<(String, Proposition)>,
    loops: usize,
    reads: usize,
}

impl<'a> Generator<'a> {
    fn wp(&mut self, statements: &[Statement], mut q: Proposition) -> Result<Proposition, String> {
        for statement in statements.iter().rev() {
            match statement {
                Statement::Assign { name, value } => {
                    q = substitute_one(&q, name, value);
                }
                Statement::Return { value } => {
                    q = substitute_one(&q, &self.program.result, value);
                }
                Statement::If {
                    condition,
                    then_body,
                    else_body,
                } => {
                    let then_q = self.wp(then_body, q.clone())?;
                    let else_q = self.wp(else_body, q)?;
                    q = and(
                        implies(condition.clone(), then_q),
                        implies(not(condition.clone()), else_q),
                    );
                }
                Statement::While {
                    condition,
                    body,
                    invariant,
                    variant,
                } => {
                    let index = self.loops;
                    self.loops += 1;
                    let preserve = implies(
                        and(invariant.clone(), condition.clone()),
                        self.wp(body, invariant.clone())?,
                    );
                    let exit = implies(and(invariant.clone(), not(condition.clone())), q);
                    let nonnegative = implies(invariant.clone(), le(int(0), variant.clone()));
                    let ghost = self
                        .program
                        .ghosts
                        .first()
                        .ok_or_else(|| "program: a loop needs one ghost variant".to_string())?;
                    let frozen = symbol(ghost);
                    let decreases_body =
                        or(not(condition.clone()), lt(variant.clone(), frozen.clone()));
                    let decreases = implies(
                        eq(frozen, variant.clone()),
                        implies(
                            and(invariant.clone(), condition.clone()),
                            self.wp(body, decreases_body)?,
                        ),
                    );
                    let prefix = format!("loop{index}");
                    self.obligations
                        .push((format!("{prefix}.preserve"), preserve));
                    self.obligations.push((format!("{prefix}.exit"), exit));
                    self.obligations
                        .push((format!("{prefix}.variant_nonnegative"), nonnegative));
                    self.obligations
                        .push((format!("{prefix}.variant_decreases"), decreases));
                    q = invariant.clone();
                }
            }
        }
        Ok(q)
    }

    fn reads_in<'b>(
        &mut self,
        statements: &'b [Statement],
        path: Proposition,
        mut state: BTreeMap<String, Proposition>,
    ) -> Result<(), String> {
        for statement in statements {
            match statement {
                Statement::Assign { name, value } => {
                    let value = subst(value, &state);
                    self.read_obligations(&value, &path)?;
                    state.insert(name.clone(), value);
                }
                Statement::If {
                    condition,
                    then_body,
                    else_body,
                } => {
                    let condition = subst(condition, &state);
                    self.read_obligations(&condition, &path)?;
                    let mut then_state = state.clone();
                    let mut else_state = state.clone();
                    self.reads_in(
                        then_body,
                        and(path.clone(), condition.clone()),
                        std::mem::take(&mut then_state),
                    )?;
                    self.reads_in(
                        else_body,
                        and(path.clone(), not(condition)),
                        std::mem::take(&mut else_state),
                    )?;
                }
                Statement::While {
                    condition,
                    body,
                    invariant,
                    ..
                } => {
                    self.read_obligations(condition, &and(path.clone(), invariant.clone()))?;
                    self.reads_in(
                        body,
                        and(invariant.clone(), condition.clone()),
                        BTreeMap::new(),
                    )?;
                    state.clear();
                }
                Statement::Return { value } => {
                    self.read_obligations(&subst(value, &state), &path)?;
                }
            }
        }
        Ok(())
    }

    fn read_obligations(
        &mut self,
        expression: &Proposition,
        path: &Proposition,
    ) -> Result<(), String> {
        let mut reads = Vec::new();
        collect_reads(expression, &mut reads);
        for read in reads {
            let (seq, index) = match read {
                Proposition::Nth { seq, index } => (seq.as_ref(), index.as_ref()),
                _ => unreachable!(),
            };
            let bounds = and(
                le(int(0), index.clone()),
                lt(index.clone(), len(seq.clone())),
            );
            let name = format!("read{}", self.reads);
            self.reads += 1;
            self.obligations.push((name, implies(path.clone(), bounds)));
        }
        Ok(())
    }
}

fn collect_reads<'a>(expr: &'a Proposition, result: &mut Vec<&'a Proposition>) {
    use Proposition::*;
    match expr {
        Nth { seq, index } => {
            result.push(expr);
            collect_reads(seq, result);
            collect_reads(index, result);
        }
        Add { left, right }
        | Sub { left, right }
        | Mul { left, right }
        | Div { left, right }
        | Eq { left, right }
        | Le { left, right }
        | Lt { left, right }
        | And { left, right }
        | Or { left, right }
        | Implies { left, right } => {
            collect_reads(left, result);
            collect_reads(right, result);
        }
        Neg { operand }
        | Not { operand }
        | Pow { base: operand, .. }
        | Len { seq: operand }
        | Sorted { seq: operand }
        | Forall { body: operand, .. }
        | Exists { body: operand, .. } => collect_reads(operand, result),
        App { args, .. } => {
            for arg in args {
                collect_reads(arg, result);
            }
        }
        _ => {}
    }
}

/// Build the conditions as expressions over program variable symbols.
pub fn conditions(program: &Program) -> Result<Vec<(String, Proposition)>, String> {
    let mut generator = Generator {
        program,
        obligations: Vec::new(),
        loops: 0,
        reads: 0,
    };
    let main = implies(
        program.requires.clone(),
        generator.wp(&program.body, program.ensures.clone())?,
    );
    generator.reads_in(&program.body, program.requires.clone(), BTreeMap::new())?;
    generator.obligations.push(("main".into(), main));
    Ok(generator.obligations)
}

fn abstract_symbols(
    expr: &Proposition,
    mapping: &BTreeMap<String, usize>,
    depth: usize,
) -> Proposition {
    use Proposition::*;
    match expr {
        Symbol { id } => match mapping.get(id) {
            Some(index) => Bound {
                index: index + depth,
            },
            None => expr.clone(),
        },
        Bound { .. } | Int { .. } | False => expr.clone(),
        Add { left, right } => Add {
            left: Box::new(abstract_symbols(left, mapping, depth)),
            right: Box::new(abstract_symbols(right, mapping, depth)),
        },
        Sub { left, right } => Sub {
            left: Box::new(abstract_symbols(left, mapping, depth)),
            right: Box::new(abstract_symbols(right, mapping, depth)),
        },
        Mul { left, right } => Mul {
            left: Box::new(abstract_symbols(left, mapping, depth)),
            right: Box::new(abstract_symbols(right, mapping, depth)),
        },
        Div { left, right } => Div {
            left: Box::new(abstract_symbols(left, mapping, depth)),
            right: Box::new(abstract_symbols(right, mapping, depth)),
        },
        Neg { operand } => Neg {
            operand: Box::new(abstract_symbols(operand, mapping, depth)),
        },
        Pow { base, exponent } => Pow {
            base: Box::new(abstract_symbols(base, mapping, depth)),
            exponent: *exponent,
        },
        Len { seq } => Len {
            seq: Box::new(abstract_symbols(seq, mapping, depth)),
        },
        Nth { seq, index } => Nth {
            seq: Box::new(abstract_symbols(seq, mapping, depth)),
            index: Box::new(abstract_symbols(index, mapping, depth)),
        },
        Sorted { seq } => Sorted {
            seq: Box::new(abstract_symbols(seq, mapping, depth)),
        },
        Eq { left, right } => Eq {
            left: Box::new(abstract_symbols(left, mapping, depth)),
            right: Box::new(abstract_symbols(right, mapping, depth)),
        },
        Le { left, right } => Le {
            left: Box::new(abstract_symbols(left, mapping, depth)),
            right: Box::new(abstract_symbols(right, mapping, depth)),
        },
        Lt { left, right } => Lt {
            left: Box::new(abstract_symbols(left, mapping, depth)),
            right: Box::new(abstract_symbols(right, mapping, depth)),
        },
        And { left, right } => And {
            left: Box::new(abstract_symbols(left, mapping, depth)),
            right: Box::new(abstract_symbols(right, mapping, depth)),
        },
        Or { left, right } => Or {
            left: Box::new(abstract_symbols(left, mapping, depth)),
            right: Box::new(abstract_symbols(right, mapping, depth)),
        },
        Not { operand } => Not {
            operand: Box::new(abstract_symbols(operand, mapping, depth)),
        },
        Implies { left, right } => Implies {
            left: Box::new(abstract_symbols(left, mapping, depth)),
            right: Box::new(abstract_symbols(right, mapping, depth)),
        },
        Forall { name, sort, body } => Forall {
            name: name.clone(),
            sort: *sort,
            body: Box::new(abstract_symbols(body, mapping, depth + 1)),
        },
        Exists { name, sort, body } => Exists {
            name: name.clone(),
            sort: *sort,
            body: Box::new(abstract_symbols(body, mapping, depth + 1)),
        },
        App { id, args } => App {
            id: id.clone(),
            args: args
                .iter()
                .map(|arg| abstract_symbols(arg, mapping, depth))
                .collect(),
        },
    }
}

pub fn close(
    goal: Proposition,
    variables: &[&str],
    sorts: &BTreeMap<String, crate::Sort>,
) -> Proposition {
    let count = variables.len();
    let mut mapping = BTreeMap::new();
    for (position, id) in variables.iter().enumerate() {
        mapping.insert((*id).to_owned(), count - 1 - position);
    }
    let mut goal = abstract_symbols(&goal, &mapping, 0);
    for id in variables.iter().rev() {
        let sort = sorts.get(*id).copied().unwrap_or(crate::Sort::Int);
        goal = Proposition::Forall {
            name: (*id).to_owned(),
            sort,
            body: Box::new(goal),
        };
    }
    goal
}

pub fn contract(
    program: &Program,
    function: &crate::Function,
    sorts: &BTreeMap<String, crate::Sort>,
) -> Result<Proposition, String> {
    if function.body.is_some() {
        return Err(format!(
            "program {}: function {} must be opaque so the program is its only definition",
            program.id, program.function
        ));
    }
    if function.params.len() != program.params.len() {
        return Err(format!(
            "program {}: parameter count does not match its function",
            program.id
        ));
    }
    let mut args = Vec::new();
    for id in &program.params {
        args.push(Proposition::Symbol { id: id.clone() });
    }
    let call = Proposition::App {
        id: program.function.clone(),
        args,
    };
    let result = Proposition::Symbol {
        id: program.result.clone(),
    };
    let mut statement = implies(eq(result, call), program.ensures.clone());
    statement = implies(program.requires.clone(), statement);
    let mut variables: Vec<&str> = program.params.iter().map(String::as_str).collect();
    variables.push(&program.result);
    Ok(close(statement, &variables, sorts))
}

pub fn check_definite_assignment(program: &Program) -> Result<(), String> {
    let params: HashSet<&str> = program.params.iter().map(String::as_str).collect();
    let locals: HashSet<&str> = program.locals.iter().map(String::as_str).collect();
    let mut initialized: HashSet<String> = params.iter().map(|id| (*id).to_owned()).collect();
    check_list(&program.body, &mut initialized, &params, &locals, false)
}

fn read_names(expr: &Proposition, result: &mut Vec<String>) {
    use Proposition::*;
    match expr {
        Symbol { id } => result.push(id.clone()),
        Add { left, right }
        | Sub { left, right }
        | Mul { left, right }
        | Div { left, right }
        | Eq { left, right }
        | Le { left, right }
        | Lt { left, right }
        | And { left, right }
        | Or { left, right }
        | Implies { left, right } => {
            read_names(left, result);
            read_names(right, result);
        }
        Neg { operand }
        | Not { operand }
        | Pow { base: operand, .. }
        | Len { seq: operand }
        | Sorted { seq: operand } => read_names(operand, result),
        Nth { seq, index } => {
            read_names(seq, result);
            read_names(index, result);
        }
        Forall { body, .. } | Exists { body, .. } => read_names(body, result),
        App { args, .. } => {
            for arg in args {
                read_names(arg, result);
            }
        }
        _ => {}
    }
}

fn check_list(
    statements: &[Statement],
    initialized: &mut HashSet<String>,
    params: &HashSet<&str>,
    locals: &HashSet<&str>,
    inside_loop: bool,
) -> Result<(), String> {
    for statement in statements {
        match statement {
            Statement::Assign { name, value } => {
                // Parameters are call-by-value initial variables. Rebinding one
                // is local, exactly as Python rebinding an int parameter is.
                if !params.contains(name.as_str()) && !locals.contains(name.as_str()) {
                    return Err(format!("program: assignment to unknown local {name:?}"));
                }
                let mut names = Vec::new();
                read_names(value, &mut names);
                for used in names {
                    if locals.contains(used.as_str()) && !initialized.contains(&used) {
                        return Err(format!("program: local {used:?} is read before assignment"));
                    }
                }
                initialized.insert(name.clone());
            }
            Statement::If {
                condition,
                then_body,
                else_body,
            } => {
                let mut names = Vec::new();
                read_names(condition, &mut names);
                for used in names {
                    if locals.contains(used.as_str()) && !initialized.contains(&used) {
                        return Err(format!("program: local {used:?} is read before assignment"));
                    }
                }
                let mut then_initialized = initialized.clone();
                let mut else_initialized = initialized.clone();
                check_list(
                    then_body,
                    &mut then_initialized,
                    params,
                    locals,
                    inside_loop,
                )?;
                check_list(
                    else_body,
                    &mut else_initialized,
                    params,
                    locals,
                    inside_loop,
                )?;
                if then_initialized != else_initialized {
                    return Err("program: the two if branches initialize different locals".into());
                }
                *initialized = then_initialized;
            }
            Statement::While {
                condition, body, ..
            } => {
                if inside_loop {
                    return Err("program: nested loops are not supported".into());
                }
                let mut names = Vec::new();
                read_names(condition, &mut names);
                for used in names {
                    if locals.contains(used.as_str()) && !initialized.contains(&used) {
                        return Err(format!("program: local {used:?} is read before assignment"));
                    }
                }
                let before = initialized.clone();
                let mut body_initialized = initialized.clone();
                check_list(body, &mut body_initialized, params, locals, true)?;
                *initialized = before;
            }
            Statement::Return { value } => {
                let mut names = Vec::new();
                read_names(value, &mut names);
                for used in names {
                    if locals.contains(used.as_str()) && !initialized.contains(&used) {
                        return Err(format!("program: local {used:?} is read before assignment"));
                    }
                }
            }
        }
    }
    Ok(())
}
