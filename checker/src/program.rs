//! Executable loop programs and their verification conditions.
//!
//! Expressions in a program use declaration IDs for program variables. The
//! conditions below are closed over those variables before they are checked.

use serde::Deserialize;
use std::collections::{BTreeMap, HashMap, HashSet};

use crate::Proposition;

#[derive(Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct NamedClause {
    pub name: String,
    pub proposition: Proposition,
}

#[derive(Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CallSite {
    pub id: String,
    pub callee: String,
    pub line: usize,
    pub requires: Proposition,
    #[serde(default)]
    pub requires_clauses: Vec<NamedClause>,
    pub ensures: Proposition,
    #[serde(default)]
    pub ensures_clauses: Vec<NamedClause>,
}

/// The contract of an already verified callee program.
#[derive(Clone)]
pub struct CalleeInfo {
    pub function: String,
    pub params: Vec<String>,
    pub result: String,
    pub requires: Proposition,
    pub ensures: Proposition,
    pub requires_clauses: Vec<NamedClause>,
    pub ensures_clauses: Vec<NamedClause>,
}

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
    #[serde(default)]
    pub requires_clauses: Vec<NamedClause>,
    #[serde(default)]
    pub ensures_clauses: Vec<NamedClause>,
    pub body: Vec<Statement>,
    #[serde(default)]
    pub calls: Vec<CallSite>,
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
        #[serde(default)]
        invariants: Vec<NamedClause>,
        #[serde(default)]
        decreases_name: Option<String>,
    },
    Return {
        value: Proposition,
    },
    Call {
        target: String,
        call: String,
        args: Vec<Proposition>,
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

    pub fn callee_info(&self) -> CalleeInfo {
        CalleeInfo {
            function: self.function.clone(),
            params: self.params.clone(),
            result: self.result.clone(),
            requires: self.requires.clone(),
            ensures: self.ensures.clone(),
            requires_clauses: self.requires_clauses.clone(),
            ensures_clauses: self.ensures_clauses.clone(),
        }
    }
}

fn conjoin(clauses: &[NamedClause]) -> Option<Proposition> {
    let mut clauses = clauses.iter().rev();
    let last = clauses.next()?.proposition.clone();
    Some(clauses.fold(last, |right, clause| and(clause.proposition.clone(), right)))
}

/// A program's named clauses must denote exactly the proposition they annotate.
pub fn check_clauses(program: &Program) -> Result<(), String> {
    if let Some(joined) = conjoin(&program.requires_clauses) {
        if joined != program.requires {
            return Err(format!(
                "program {}: requires clauses do not conjoin to its requires",
                program.id
            ));
        }
    }
    if let Some(joined) = conjoin(&program.ensures_clauses) {
        if joined != program.ensures {
            return Err(format!(
                "program {}: ensures clauses do not conjoin to its ensures",
                program.id
            ));
        }
    }
    check_statement_clauses(program, &program.body)
}

fn check_statement_clauses(program: &Program, statements: &[Statement]) -> Result<(), String> {
    for statement in statements {
        match statement {
            Statement::While {
                invariant,
                invariants,
                ..
            } => {
                if let Some(joined) = conjoin(invariants) {
                    if joined != *invariant {
                        return Err(format!(
                            "program {}: loop invariant clauses do not conjoin to the invariant",
                            program.id
                        ));
                    }
                }
                if let Statement::While { body, .. } = statement {
                    check_statement_clauses(program, body)?;
                }
            }
            Statement::If {
                then_body,
                else_body,
                ..
            } => {
                check_statement_clauses(program, then_body)?;
                check_statement_clauses(program, else_body)?;
            }
            _ => {}
        }
    }
    Ok(())
}

/// Check that each call statement has exactly one well-formed call site.
pub fn check_calls(program: &Program, callees: &HashMap<String, CalleeInfo>) -> Result<(), String> {
    let mut sites = HashMap::new();
    for site in &program.calls {
        if sites.insert(site.id.as_str(), site).is_some() {
            return Err(format!(
                "program {}: duplicate call site {:?}",
                program.id, site.id
            ));
        }
        let callee = callees.get(&site.callee).ok_or_else(|| {
            format!(
                "program {}: call {} names unknown or unverified callee program {:?}",
                program.id, site.id, site.callee
            )
        })?;
        if site.requires != callee.requires {
            return Err(format!(
                "program {}: call {} at line {} records a requires that differs from callee {}",
                program.id, site.id, site.line, callee.function
            ));
        }
        if site.ensures != callee.ensures {
            return Err(format!(
                "program {}: call {} at line {} records an ensures that differs from callee {}",
                program.id, site.id, site.line, callee.function
            ));
        }
        if site.requires_clauses != callee.requires_clauses
            || site.ensures_clauses != callee.ensures_clauses
        {
            return Err(format!(
                "program {}: call {} at line {} records clauses that differ from callee {}",
                program.id, site.id, site.line, callee.function
            ));
        }
    }
    let mut used = HashSet::new();
    let locals: HashSet<&str> = program
        .params
        .iter()
        .chain(program.locals.iter())
        .map(String::as_str)
        .collect();
    fn walk(
        program: &Program,
        sites: &HashMap<&str, &CallSite>,
        callees: &HashMap<String, CalleeInfo>,
        locals: &HashSet<&str>,
        used: &mut HashSet<String>,
        statements: &[Statement],
    ) -> Result<(), String> {
        for statement in statements {
            match statement {
                Statement::Call { call, args, target } => {
                    let site = sites.get(call.as_str()).ok_or_else(|| {
                        format!("program {}: call {:?} has no call site", program.id, call)
                    })?;
                    if !used.insert(call.clone()) {
                        return Err(format!(
                            "program {}: call site {:?} is used more than once",
                            program.id, call
                        ));
                    }
                    if !locals.contains(target.as_str()) {
                        return Err(format!(
                            "program {}: call {} targets unknown local {:?}",
                            program.id, call, target
                        ));
                    }
                    let callee = callees.get(&site.callee).ok_or_else(|| {
                        format!(
                            "program {}: call {} names unknown callee program {:?}",
                            program.id, call, site.callee
                        )
                    })?;
                    if site.callee == program.id && program.id == site.callee {
                        return Err(format!(
                            "program {}: recursive call to itself is not supported",
                            program.id
                        ));
                    }
                    if args.len() != callee.params.len() {
                        return Err(format!(
                            "program {}: call {} passes {} argument(s) to {}, which takes {}",
                            program.id,
                            call,
                            args.len(),
                            callee.function,
                            callee.params.len()
                        ));
                    }
                }
                Statement::If {
                    then_body,
                    else_body,
                    ..
                } => {
                    walk(program, sites, callees, locals, used, then_body)?;
                    walk(program, sites, callees, locals, used, else_body)?;
                }
                Statement::While { body, .. } => walk(program, sites, callees, locals, used, body)?,
                _ => {}
            }
        }
        Ok(())
    }
    walk(program, &sites, callees, &locals, &mut used, &program.body)?;
    if let Some(site) = program.calls.iter().find(|site| !used.contains(&site.id)) {
        return Err(format!(
            "program {}: call site {:?} has no call statement",
            program.id, site.id
        ));
    }
    Ok(())
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
    callees: &'a HashMap<String, CalleeInfo>,
    sites: HashMap<&'a str, &'a CallSite>,
    obligations: Vec<(String, Proposition)>,
    loops: usize,
    reads: usize,
}

impl<'a> Generator<'a> {
    fn call_parts(
        &self,
        call: &str,
        args: &[Proposition],
        target: &str,
    ) -> Result<(Proposition, Proposition, Proposition), String> {
        let site = self
            .sites
            .get(call)
            .ok_or_else(|| format!("program {}: unknown call site {call:?}", self.program.id))?;
        let callee = self.callees.get(&site.callee).ok_or_else(|| {
            format!(
                "program {}: call {call} names unknown callee {}",
                self.program.id, site.callee
            )
        })?;
        if args.len() != callee.params.len() {
            return Err(format!(
                "program {}: call {call} has the wrong number of arguments",
                self.program.id
            ));
        }
        let application = Proposition::App {
            id: callee.function.clone(),
            args: args.to_vec(),
        };
        let mut mapping = BTreeMap::new();
        for (formal, actual) in callee.params.iter().zip(args.iter()) {
            mapping.insert(formal.clone(), actual.clone());
        }
        mapping.insert(callee.result.clone(), application.clone());
        let requires = subst(&callee.requires, &mapping);
        let ensures = subst(&callee.ensures, &mapping);
        let _ = target;
        Ok((requires, ensures, application))
    }
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
                    invariants,
                    decreases_name,
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
                    let suffix = decreases_name
                        .as_ref()
                        .map(|name| format!(".{name}"))
                        .unwrap_or_default();
                    if invariants.is_empty() {
                        self.obligations
                            .push((format!("{prefix}.preserve"), preserve));
                    } else {
                        for clause in invariants {
                            let goal = implies(
                                and(invariant.clone(), condition.clone()),
                                self.wp(body, clause.proposition.clone())?,
                            );
                            self.obligations
                                .push((format!("{prefix}.preserve.{}", clause.name), goal));
                        }
                    }
                    self.obligations.push((format!("{prefix}.exit"), exit));
                    self.obligations
                        .push((format!("{prefix}.variant_nonnegative{suffix}"), nonnegative));
                    self.obligations
                        .push((format!("{prefix}.variant_decreases{suffix}"), decreases));
                    q = invariant.clone();
                }
                Statement::Call { target, call, args } => {
                    let (requires, ensures, application) = self.call_parts(call, args, target)?;
                    q = substitute_one(&q, target, &application);
                    q = and(requires, implies(ensures, q));
                }
            }
        }
        Ok(q)
    }

    fn reads_in<'b>(
        &mut self,
        statements: &'b [Statement],
        mut path: Proposition,
        mut state: BTreeMap<String, Proposition>,
    ) -> Result<(), String> {
        for (offset, statement) in statements.iter().enumerate() {
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
                    // Each branch reaches the continuation with its own local values.
                    let continuation = &statements[offset + 1..];
                    let mut then_path = then_body.clone();
                    then_path.extend_from_slice(continuation);
                    let mut else_path = else_body.clone();
                    else_path.extend_from_slice(continuation);
                    self.reads_in(
                        &then_path,
                        and(path.clone(), condition.clone()),
                        state.clone(),
                    )?;
                    return self.reads_in(&else_path, and(path, not(condition)), state);
                }
                Statement::While {
                    condition,
                    body,
                    invariant,
                    ..
                } => {
                    self.read_obligations(condition, invariant)?;
                    self.reads_in(
                        body,
                        and(invariant.clone(), condition.clone()),
                        BTreeMap::new(),
                    )?;
                    // Use facts about the exit state in place of facts about entry.
                    state.clear();
                    path = and(invariant.clone(), not(condition.clone()));
                }
                Statement::Return { value } => {
                    self.read_obligations(&subst(value, &state), &path)?;
                    return Ok(());
                }
                Statement::Call { target, call, args } => {
                    let actuals: Vec<Proposition> =
                        args.iter().map(|arg| subst(arg, &state)).collect();
                    for actual in &actuals {
                        self.read_obligations(actual, &path)?;
                    }
                    let (_, ensures, application) = self.call_parts(call, &actuals, target)?;
                    let site = self.sites.get(call.as_str()).ok_or_else(|| {
                        format!("program {}: unknown call site {call:?}", self.program.id)
                    })?;
                    let callee = self.callees.get(&site.callee).ok_or_else(|| {
                        format!(
                            "program {}: call {call} names unknown callee {}",
                            self.program.id, site.callee
                        )
                    })?;
                    let mut mapping = BTreeMap::new();
                    for (formal, actual) in callee.params.iter().zip(actuals.iter()) {
                        mapping.insert(formal.clone(), actual.clone());
                    }
                    mapping.insert(callee.result.clone(), application);
                    if callee.requires_clauses.is_empty() {
                        Self::call_requirement(
                            &mut self.obligations,
                            format!("{}.requires", site.id),
                            implies(path.clone(), subst(&callee.requires, &mapping)),
                        );
                    } else {
                        for clause in &callee.requires_clauses {
                            Self::call_requirement(
                                &mut self.obligations,
                                format!("{}.requires.{}", site.id, clause.name),
                                implies(path.clone(), subst(&clause.proposition, &mapping)),
                            );
                        }
                    }
                    state.insert(target.clone(), {
                        let value = Proposition::App {
                            id: callee.function.clone(),
                            args: actuals,
                        };
                        value
                    });
                    path = and(path, ensures);
                }
            }
        }
        Ok(())
    }

    fn call_requirement(
        obligations: &mut Vec<(String, Proposition)>,
        name: String,
        goal: Proposition,
    ) {
        if let Some((_, existing)) = obligations.iter_mut().find(|(key, _)| *key == name) {
            *existing = and(existing.clone(), goal);
        } else {
            obligations.push((name, goal));
        }
    }

    fn read_obligations(
        &mut self,
        expression: &Proposition,
        path: &Proposition,
    ) -> Result<(), String> {
        let mut guards = Vec::new();
        collect_guards(expression, &mut guards);
        for guard in guards {
            let name = format!("read{}", self.reads);
            self.reads += 1;
            self.obligations.push((name, implies(path.clone(), guard)));
        }
        Ok(())
    }
}

fn collect_guards(expr: &Proposition, result: &mut Vec<Proposition>) {
    use Proposition::*;
    match expr {
        Nth { seq, index } => {
            result.push(and(
                le(int(0), *index.clone()),
                lt(*index.clone(), len(*seq.clone())),
            ));
            collect_guards(seq, result);
            collect_guards(index, result);
        }
        Div { left, right } => {
            result.push(or(lt(*right.clone(), int(0)), lt(int(0), *right.clone())));
            collect_guards(left, result);
            collect_guards(right, result);
        }
        And { left, right } | Or { left, right } => {
            collect_guards(left, result);
            let evaluated = if matches!(expr, And { .. }) {
                *left.clone()
            } else {
                not(*left.clone())
            };
            let mut guards = Vec::new();
            collect_guards(right, &mut guards);
            result.extend(
                guards
                    .into_iter()
                    .map(|guard| implies(evaluated.clone(), guard)),
            );
        }
        Add { left, right }
        | Sub { left, right }
        | Mul { left, right }
        | Eq { left, right }
        | Le { left, right }
        | Lt { left, right }
        | Implies { left, right } => {
            collect_guards(left, result);
            collect_guards(right, result);
        }
        Neg { operand }
        | Not { operand }
        | Pow { base: operand, .. }
        | Len { seq: operand }
        | Sorted { seq: operand }
        | Forall { body: operand, .. }
        | Exists { body: operand, .. } => collect_guards(operand, result),
        App { args, .. } => {
            for arg in args {
                collect_guards(arg, result);
            }
        }
        _ => {}
    }
}

/// Build the conditions as expressions over program variable symbols.
pub fn conditions(
    program: &Program,
    callees: &HashMap<String, CalleeInfo>,
) -> Result<Vec<(String, Proposition)>, String> {
    let sites = program
        .calls
        .iter()
        .map(|site| (site.id.as_str(), site))
        .collect();
    let mut generator = Generator {
        program,
        callees,
        sites,
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
    let mut statement = if program.ensures == eq(int(0), int(0)) {
        eq(result, call)
    } else {
        implies(eq(result, call), program.ensures.clone())
    };
    if program.requires != eq(int(0), int(0)) {
        statement = implies(program.requires.clone(), statement);
    }
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

fn block_returns(statements: &[Statement]) -> bool {
    match statements.last() {
        Some(Statement::Return { .. }) => true,
        Some(Statement::If {
            then_body,
            else_body,
            ..
        }) => block_returns(then_body) && block_returns(else_body),
        _ => false,
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
                let before = initialized.clone();
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
                let then_returns = block_returns(then_body);
                let else_returns = block_returns(else_body);
                if then_returns != else_returns {
                    return Err(
                        "program: both branches of an if must return or neither may return".into(),
                    );
                }
                if then_returns {
                    *initialized = before;
                } else {
                    if then_initialized != else_initialized {
                        return Err(
                            "program: the two if branches initialize different locals".into()
                        );
                    }
                    *initialized = then_initialized;
                }
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
            Statement::Call { target, args, .. } => {
                if !params.contains(target.as_str()) && !locals.contains(target.as_str()) {
                    return Err(format!("program: call targets unknown local {target:?}"));
                }
                for argument in args {
                    let mut names = Vec::new();
                    read_names(argument, &mut names);
                    for used in names {
                        if locals.contains(used.as_str()) && !initialized.contains(&used) {
                            return Err(format!(
                                "program: local {used:?} is read before assignment"
                            ));
                        }
                    }
                }
                initialized.insert(target.clone());
            }
        }
    }
    Ok(())
}
