//! Verification for the first portable Logos proof fragment.
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet};

pub const FORMAT: &str = "logos-proof-v1";
pub const THEORY: &str = "logos-core-v1";
pub const PROTOCOL_VERSION: u32 = 1;

mod syntax;
mod trace;

pub use syntax::{Function, Proposition, Sort};
use syntax::{Functions, convert, instantiate_bounded, instantiate_law, integer, law_formals};
pub use trace::Context as TraceContext;
use trace::{
    Conversion, LawApplication, LocalHypothesis, Provenance, Substitution, Variable,
    rule_explanation,
};

#[derive(Deserialize)]
#[serde(tag = "tag", rename_all = "snake_case", deny_unknown_fields)]
enum Evidence {
    ImpliesIntro {
        binder: String,
        premise: Proposition,
        body: Box<Self>,
    },
    ImpliesElim {
        implication: Box<Self>,
        premise: Box<Self>,
    },
    OrIntroL {
        proof: Box<Self>,
        other: Proposition,
    },
    OrIntroR {
        proof: Box<Self>,
        other: Proposition,
    },
    OrElim {
        proof: Box<Self>,
        binder: String,
        left: Box<Self>,
        right: Box<Self>,
    },
    NotIntro {
        proof: Box<Self>,
    },
    NotElim {
        negation: Box<Self>,
        premise: Box<Self>,
    },
    ExFalso {
        proof: Box<Self>,
        conclusion: Proposition,
    },
    HypRef {
        binder: String,
    },
    AxiomRef {
        id: String,
    },
    TheoremRef {
        id: String,
    },
    AndIntro {
        left: Box<Self>,
        right: Box<Self>,
    },
    AndElimL {
        proof: Box<Self>,
    },
    AndElimR {
        proof: Box<Self>,
    },
    Refl {
        term: Proposition,
    },
    Symm {
        proof: Box<Self>,
    },
    Trans {
        left: Box<Self>,
        right: Box<Self>,
    },
    Congr {
        context: Proposition,
        proof: Box<Self>,
    },
    ForallIntro {
        name: String,
        sort: Sort,
        body: Box<Self>,
    },
    ForallElim {
        proof: Box<Self>,
        term: Proposition,
    },
    ExistsIntro {
        goal: Proposition,
        witness: Proposition,
        proof: Box<Self>,
    },
    CoreLaw {
        id: String,
        args: Vec<Proposition>,
    },
    Block {
        steps: Vec<Self>,
        result: usize,
    },
    StepRef {
        index: usize,
    },
}

impl Evidence {
    fn children(&self) -> [Option<&Self>; 3] {
        match self {
            Self::ImpliesIntro { body, .. } | Self::ForallIntro { body, .. } => {
                [Some(body), None, None]
            }
            Self::AndElimL { proof }
            | Self::AndElimR { proof }
            | Self::OrIntroL { proof, .. }
            | Self::OrIntroR { proof, .. }
            | Self::NotIntro { proof }
            | Self::ExFalso { proof, .. }
            | Self::Symm { proof }
            | Self::Congr { proof, .. }
            | Self::ForallElim { proof, .. }
            | Self::ExistsIntro { proof, .. } => [Some(proof), None, None],
            Self::AndIntro { left, right }
            | Self::Trans { left, right }
            | Self::ImpliesElim {
                implication: left,
                premise: right,
            }
            | Self::NotElim {
                negation: left,
                premise: right,
            } => [Some(left), Some(right), None],
            Self::OrElim {
                proof, left, right, ..
            } => [Some(proof), Some(left), Some(right)],
            _ => [None, None, None],
        }
    }

    fn lemma_dependencies<'a>(&'a self, dependencies: &mut Vec<&'a str>) -> Result<(), String> {
        match self {
            Self::TheoremRef { id } => dependencies.push(id),
            Self::Block { steps, result } => {
                for index in block_order(steps, *result)? {
                    steps[index].lemma_dependencies(dependencies)?;
                }
            }
            _ => {
                for child in self.children().into_iter().flatten() {
                    child.lemma_dependencies(dependencies)?;
                }
            }
        }
        Ok(())
    }

    fn step_dependencies(&self, deps: &mut Vec<usize>) {
        if let Self::StepRef { index } = self {
            deps.push(*index);
        }
        // Nested blocks have their own index space and no ordinary children.
        for child in self.children().into_iter().flatten() {
            child.step_dependencies(deps);
        }
    }
}

fn block_order(steps: &[Evidence], result: usize) -> Result<Vec<usize>, String> {
    if result >= steps.len() {
        return Err(format!("invalid block result {result}"));
    }
    let mut reachable = HashSet::new();
    let mut pending = vec![result];
    let mut dependencies = Vec::new();
    while let Some(index) = pending.pop() {
        if reachable.insert(index) {
            steps[index].step_dependencies(&mut dependencies);
            for previous in dependencies.drain(..) {
                if previous >= index {
                    return Err(format!(
                        "out-of-scope block step {previous} in step {index}"
                    ));
                }
                pending.push(previous);
            }
        }
    }
    let mut order: Vec<_> = reachable.into_iter().collect();
    order.sort_unstable();
    Ok(order)
}

#[derive(Clone, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Declaration {
    pub id: String,
    pub name: String,
    pub sort: Sort,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Bundle {
    format: String,
    theory: String,
    name: Option<String>,
    declarations: Vec<Declaration>,
    #[serde(default)]
    functions: Vec<Function>,
    custom_axioms: Vec<CustomAxiom>,
    lemmas: Vec<Lemma>,
    target: Proposition,
    proof: Evidence,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CustomAxiom {
    id: String,
    statement: Proposition,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Lemma {
    id: String,
    statement: Proposition,
    proof: Evidence,
}

#[derive(Serialize)]
pub struct UsedAxiom {
    pub id: String,
    pub statement: Proposition,
    pub statement_text: String,
    pub path: Vec<String>,
}

#[derive(Serialize)]
pub struct Judgment {
    pub protocol_version: u32,
    pub status: &'static str,
    pub artifact_sha256: String,
    pub format: &'static str,
    pub theory: &'static str,
    pub unverified_author_label: Option<String>,
    pub declarations: Vec<Declaration>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub functions: Vec<Function>,
    pub statement: Proposition,
    pub statement_text: String,
    pub custom_axioms: Vec<UsedAxiom>,
}

#[derive(Serialize)]
pub struct Step {
    pub id: String,
    pub rule: &'static str,
    pub explanation: &'static str,
    pub context_id: usize,
    pub conclusion_sort: Sort,
    pub premises: Vec<String>,
    pub conclusion: Proposition,
    pub conclusion_text: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub binder: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reference_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub discharged: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub discharged_cases: Option<[String; 2]>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub substitutions: Option<Vec<Proposition>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub context: Option<Proposition>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub binder_sort: Option<Sort>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub introduced_variable: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub introduced_hypothesis: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub provenance: Option<Provenance>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub law: Option<LawApplication>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub premise_conversion: Option<Conversion>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub conclusion_conversion: Option<Conversion>,
}

pub struct Verified {
    pub judgment: Judgment,
    pub steps: Vec<Step>,
    pub contexts: Vec<TraceContext>,
}

type Declarations<'a> = HashMap<&'a str, &'a Declaration>;
#[derive(Default)]
struct Scope<'a> {
    hyps: Vec<(&'a str, Proposition, String, usize)>,
    binders: Vec<Sort>,
    variables: Vec<Variable>,
    blocks: Vec<BlockScope>,
}

struct BlockScope {
    depth: usize,
    entries: HashMap<usize, (Proposition, String)>,
}

pub const MAX_ARTIFACT_BYTES: usize = 8 * 1024 * 1024;
const MAX_STEPS: usize = 25_000;
const MAX_TRACE_WEIGHT: usize = 32 * 1024 * 1024;

pub fn verify(bytes: &[u8]) -> Result<Verified, String> {
    if bytes.len() > MAX_ARTIFACT_BYTES {
        return Err("proof file exceeds resource limit".into());
    }
    let source = std::str::from_utf8(bytes).map_err(|error| format!("invalid UTF-8: {error}"))?;
    let bundle: Bundle =
        serde_json::from_str(source).map_err(|error| format!("malformed proof file: {error}"))?;
    if bundle.format != FORMAT {
        return Err(format!("unsupported proof format {:?}", bundle.format));
    }
    if bundle.theory != THEORY {
        return Err(format!("unsupported theory {:?}", bundle.theory));
    }
    let mut ids = HashSet::new();
    let mut register = |id: &'_ str, kind| {
        if id.is_empty() {
            return Err(format!("empty {kind} ID"));
        }
        if law_formals(id).is_some() {
            return Err(format!("{kind} ID {id:?} is reserved by logos-core-v1"));
        }
        if !ids.insert(id.to_owned()) {
            return Err(format!("duplicate {kind} ID {id:?}"));
        }
        Ok(())
    };
    let mut declarations = HashMap::new();
    for declaration in &bundle.declarations {
        register(&declaration.id, "declaration")?;
        declarations.insert(declaration.id.as_str(), declaration);
    }
    let mut checker = Checker::new(declarations);
    // Transparent bodies can mention earlier functions only. This makes
    // definition references acyclic before any conversion takes place.
    for function in &bundle.functions {
        register(&function.id, "function")?;
        if let Some(body) = &function.body {
            checker
                .sort(body, &function.params)?
                .expect(function.result)?;
        }
        checker.functions.insert(function.id.as_str(), function);
    }
    for axiom in &bundle.custom_axioms {
        register(&axiom.id, "axiom")?;
        checker.check_proposition(&axiom.statement)?;
        checker.axioms.insert(axiom.id.as_str(), axiom);
    }
    let mut lemmas = HashMap::new();
    for lemma in &bundle.lemmas {
        register(&lemma.id, "lemma")?;
        checker.check_proposition(&lemma.statement)?;
        lemmas.insert(lemma.id.as_str(), lemma);
    }
    checker.check_proposition(&bundle.target)?;
    // Check only the lemmas reachable from the target proof, in dependency
    // order and with an empty local scope. Bundle-level format, ID and
    // namespace checks above already covered every supplied declaration.
    let mut dependencies = Vec::new();
    bundle.proof.lemma_dependencies(&mut dependencies)?;
    for id in dependencies {
        let lemma = lemmas
            .get(id)
            .ok_or_else(|| format!("unknown theorem reference {id:?}"))?;
        checker.check_lemmas(lemma, &lemmas)?;
    }
    checker.check_conclusion(&bundle.proof, &bundle.target, "proof")?;
    let statement = bundle.target;
    let statement_text = checker.render(&statement, false, false);
    let (custom_axioms, steps, contexts) = checker.target_trace();
    Ok(Verified {
        judgment: Judgment {
            protocol_version: PROTOCOL_VERSION,
            status: "verified",
            artifact_sha256: Sha256::digest(bytes)
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect(),
            format: FORMAT,
            theory: THEORY,
            unverified_author_label: bundle.name,
            declarations: bundle.declarations,
            functions: bundle.functions,
            statement,
            statement_text,
            custom_axioms,
        },
        steps,
        contexts,
    })
}

struct Checker<'a> {
    declarations: Declarations<'a>,
    functions: Functions<'a>,
    ambiguous_names: HashSet<&'a str>,
    steps: Vec<Step>,
    contexts: Vec<TraceContext>,
    context_ids: HashMap<(Vec<String>, Vec<String>), usize>,
    trace_weight: usize,
    axioms: HashMap<&'a str, &'a CustomAxiom>,
    checked_lemmas: HashMap<&'a str, &'a Lemma>,
}

impl<'a> Checker<'a> {
    fn new(declarations: Declarations<'a>) -> Self {
        let mut names = HashSet::new();
        let ambiguous_names = declarations
            .values()
            .map(|declaration| declaration.name.as_str())
            .filter(|name| !names.insert(*name))
            .collect();
        Self {
            declarations,
            functions: HashMap::new(),
            ambiguous_names,
            steps: Vec::new(),
            contexts: Vec::new(),
            context_ids: HashMap::new(),
            trace_weight: 0,
            axioms: HashMap::new(),
            checked_lemmas: HashMap::new(),
        }
    }

    fn check_lemmas(
        &mut self,
        root: &'a Lemma,
        lemmas: &HashMap<&str, &'a Lemma>,
    ) -> Result<(), String> {
        // An explicit depth-first stack keeps lemma-chain length off the call stack.
        let mut visiting = HashSet::new();
        let mut pending = vec![(root, false)];
        let mut dependencies = Vec::new();
        while let Some((lemma, ready)) = pending.pop() {
            let id = lemma.id.as_str();
            if ready {
                self.check_conclusion(&lemma.proof, &lemma.statement, &lemma_path(id))?;
                self.checked_lemmas.insert(id, lemma);
                visiting.remove(id);
            } else if !self.checked_lemmas.contains_key(id) {
                if !visiting.insert(id) {
                    return Err(format!("cyclic theorem dependency at {id:?}"));
                }
                pending.push((lemma, true));
                lemma.proof.lemma_dependencies(&mut dependencies)?;
                for id in dependencies.drain(..).rev() {
                    let dependency = lemmas
                        .get(id)
                        .ok_or_else(|| format!("unknown theorem reference {id:?}"))?;
                    pending.push((dependency, false));
                }
            }
        }
        Ok(())
    }

    fn check_conclusion(
        &mut self,
        evidence: &'a Evidence,
        expected: &Proposition,
        path: &str,
    ) -> Result<Proposition, String> {
        let derived = self.infer(evidence, &mut Scope::default(), path)?;
        let conversion = self.compare(&derived, expected)?.ok_or_else(|| {
            let location = if path == "proof" {
                String::new()
            } else {
                format!("{path}: ")
            };
            format!(
                "{location}proof conclusion mismatch\nExpected: {}\nDerived:  {}",
                self.render(expected, false, false),
                self.render(&derived, false, false),
            )
        })?;
        if let Some(item) = &conversion {
            self.charge(&item.common_normal_form)?;
            self.charge(expected)?;
        }
        self.steps
            .last_mut()
            .expect("inference recorded a step")
            .conclusion_conversion = conversion;
        Ok(derived)
    }

    fn target_trace(self) -> (Vec<UsedAxiom>, Vec<Step>, Vec<TraceContext>) {
        let by_path: HashMap<_, _> = self
            .steps
            .iter()
            .map(|step| (step.id.as_str(), step))
            .collect();
        let mut parents: HashMap<&str, Option<&str>> = HashMap::from([("proof", None)]);
        let mut pending = vec!["proof"];
        let mut used_ids = HashSet::new();
        let mut used = Vec::new();
        while let Some(path) = pending.pop() {
            let step = by_path[path];
            if step.rule == "axiom_ref" {
                let id = step.reference_id.as_deref().expect("axiom ref has an ID");
                if used_ids.insert(id) {
                    let statement = &self.axioms[id].statement;
                    let mut chain = vec![path.to_owned()];
                    let mut current = path;
                    while let Some(parent) = parents[current] {
                        chain.push(parent.to_owned());
                        current = parent;
                    }
                    chain.reverse();
                    used.push(UsedAxiom {
                        id: id.to_owned(),
                        statement: statement.clone(),
                        statement_text: self.render(statement, false, true),
                        path: chain,
                    });
                }
            }
            for premise in step.premises.iter().rev() {
                let premise = premise.as_str();
                if let std::collections::hash_map::Entry::Vacant(entry) = parents.entry(premise) {
                    entry.insert(Some(path));
                    pending.push(premise);
                }
            }
        }
        // Keep premise-first ordering while omitting unreachable lemmas.
        let reachable: Vec<_> = self
            .steps
            .iter()
            .map(|step| parents.contains_key(step.id.as_str()))
            .collect();
        let steps = self
            .steps
            .into_iter()
            .zip(reachable)
            .filter_map(|(step, reached)| reached.then_some(step))
            .collect();
        (used, steps, self.contexts)
    }

    fn check_proposition(&self, proposition: &Proposition) -> Result<(), String> {
        proposition.weight()?;
        let sort = self.sort(proposition, &[])?;
        sort.expect(Sort::Prop).map_err(|error| match proposition {
            Proposition::Symbol { id } => format!("declaration {id:?} {error}"),
            _ => error,
        })
    }

    fn sort(&self, term: &Proposition, scope: &[Sort]) -> Result<Sort, String> {
        use Proposition::*;
        let child = |term| self.sort(term, scope);
        let require = |term, expected| {
            child(term)?.expect(expected).map_err(|error| match term {
                Symbol { id } => format!("declaration {id:?} {error}"),
                _ => error,
            })
        };
        match term {
            Symbol { id } => self
                .declarations
                .get(id.as_str())
                .map(|decl| decl.sort)
                .ok_or_else(|| format!("undeclared symbol {id:?}")),
            Bound { index } => scope
                .iter()
                .rev()
                .nth(*index)
                .copied()
                .ok_or_else(|| format!("out-of-scope bound variable {index}")),
            Int { value } => {
                integer(value)?;
                Ok(Sort::Int)
            }
            Add { left, right } | Sub { left, right } | Mul { left, right } => {
                require(left, Sort::Int)?;
                require(right, Sort::Int)?;
                Ok(Sort::Int)
            }
            Neg { operand } | Pow { base: operand, .. } => {
                require(operand, Sort::Int)?;
                Ok(Sort::Int)
            }
            Eq { left, right } => {
                require(right, child(left)?)?;
                Ok(Sort::Prop)
            }
            False => Ok(Sort::Prop),
            Not { operand } => {
                require(operand, Sort::Prop)?;
                Ok(Sort::Prop)
            }
            And { left, right } | Or { left, right } | Implies { left, right } => {
                require(left, Sort::Prop)?;
                require(right, Sort::Prop)?;
                Ok(Sort::Prop)
            }
            Forall { sort, body, .. } | Exists { sort, body, .. } => {
                let mut nested = scope.to_vec();
                nested.push(*sort);
                self.sort(body, &nested)?.expect(Sort::Prop)?;
                Ok(Sort::Prop)
            }
            App { id, args } => {
                let function = self
                    .functions
                    .get(id.as_str())
                    .ok_or_else(|| format!("undeclared function {id:?}"))?;
                if args.len() != function.params.len() {
                    return Err(format!("wrong number of arguments for function {id:?}"));
                }
                for (arg, sort) in args.iter().zip(&function.params) {
                    require(arg, *sort)?;
                }
                Ok(function.result)
            }
        }
    }

    // Outer None is a mismatch. Inner None denotes already identical syntax.
    fn compare(
        &self,
        left: &Proposition,
        right: &Proposition,
    ) -> Result<Option<Option<Conversion>>, String> {
        let common_normal_form = convert(left, &self.functions)?;
        if left != right && common_normal_form != convert(right, &self.functions)? {
            return Ok(None);
        }
        Ok(Some((left != right).then(|| Conversion {
            explanation: "The two expressions have the same normal form under the core conversion rules.",
            left: left.clone(),
            right: right.clone(),
            common_normal_form,
        })))
    }

    fn context_id(&mut self, scope: &Scope<'_>) -> usize {
        let variables = scope.variables.iter().map(|var| var.id.clone()).collect();
        let hypotheses = scope.hyps.iter().map(|(_, _, id, _)| id.clone()).collect();
        *self
            .context_ids
            .entry((variables, hypotheses))
            .or_insert_with(|| {
                let id = self.contexts.len();
                self.contexts.push(TraceContext {
                    id,
                    variables: scope.variables.clone(),
                    hypotheses: scope
                        .hyps
                        .iter()
                        .map(|(binder, _, id, depth)| LocalHypothesis {
                            id: id.clone(),
                            binder: (*binder).to_owned(),
                            binder_depth: *depth,
                        })
                        .collect(),
                });
                id
            })
    }

    fn equality(
        &self,
        p: Proposition,
        path: &str,
    ) -> Result<(Box<Proposition>, Box<Proposition>), String> {
        match p {
            Proposition::Eq { left, right } => Ok((left, right)),
            _ => match convert(&p, &self.functions)? {
                Proposition::Eq { left, right } => Ok((left, right)),
                _ => Err(format!("{path}: rule requires an equality premise")),
            },
        }
    }

    fn render(&self, proposition: &Proposition, nested: bool, typed: bool) -> String {
        self.render_scoped(proposition, nested, typed, &mut Vec::new())
    }

    fn render_scoped<'b>(
        &self,
        proposition: &'b Proposition,
        nested: bool,
        typed: bool,
        binders: &mut Vec<(&'b str, Sort)>,
    ) -> String {
        let (left, op, right) = match proposition {
            Proposition::Symbol { id } => {
                let name = self.declarations[id.as_str()].name.as_str();
                let label = if !name.is_empty()
                    && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
                {
                    name.to_owned()
                } else {
                    format!("{name:?}")
                };
                return if typed {
                    format!(
                        "{label}[{id:?}]:{}",
                        self.declarations[id.as_str()].sort.name()
                    )
                } else if self.ambiguous_names.contains(name) {
                    format!("{label}[{id:?}]")
                } else {
                    label
                };
            }
            Proposition::Bound { index } => {
                return match binders.iter().rev().nth(*index) {
                    Some((name, sort)) if typed => format!("{name:?}[#{index}]:{}", sort.name()),
                    Some((name, _)) => name.to_string(),
                    None => format!("#{index}"),
                };
            }
            Proposition::Int { value } => return value.clone(),
            Proposition::False => return "⊥".into(),
            Proposition::Not { operand } => {
                return format!("¬{}", self.render_scoped(operand, true, typed, binders));
            }
            Proposition::Neg { operand } => {
                return format!("(−{})", self.render_scoped(operand, true, typed, binders));
            }
            Proposition::Pow { base, exponent } => {
                return format!(
                    "({}^{exponent})",
                    self.render_scoped(base, true, typed, binders)
                );
            }
            Proposition::App { id, args } => {
                let name = &self.functions[id.as_str()].name;
                let label = format!("{name:?}[{id:?}]");
                let args = args
                    .iter()
                    .map(|arg| self.render_scoped(arg, false, typed, binders))
                    .collect::<Vec<_>>()
                    .join(", ");
                return format!("{label}({args})");
            }
            Proposition::Forall { name, sort, body } | Proposition::Exists { name, sort, body } => {
                let quantifier = if matches!(proposition, Proposition::Exists { .. }) {
                    "∃"
                } else {
                    "∀"
                };
                let label = if !name.is_empty()
                    && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
                {
                    name.clone()
                } else {
                    format!("{name:?}")
                };
                binders.push((name, *sort));
                let body = self.render_scoped(body, false, typed, binders);
                binders.pop();
                let text = format!("{quantifier}{label}:{}, {body}", sort.name());
                return if nested { format!("({text})") } else { text };
            }
            Proposition::Add { left, right } => (left, "+", right),
            Proposition::Sub { left, right } => (left, "−", right),
            Proposition::Mul { left, right } => (left, "·", right),
            Proposition::Eq { left, right } => (left, "=", right),
            Proposition::And { left, right } => (left, "∧", right),
            Proposition::Or { left, right } => (left, "∨", right),
            Proposition::Implies { left, right } => (left, "→", right),
        };
        let text = format!(
            "{} {op} {}",
            self.render_scoped(left, true, typed, binders),
            self.render_scoped(right, true, typed, binders)
        );
        if nested { format!("({text})") } else { text }
    }

    fn charge(&mut self, conclusion: &Proposition) -> Result<(), String> {
        self.trace_weight += conclusion.weight()?;
        if self.trace_weight > MAX_TRACE_WEIGHT {
            return Err("proof trace exceeds resource limit".into());
        }
        Ok(())
    }

    fn infer_under_hypothesis(
        &mut self,
        binder: &'a str,
        premise: &Proposition,
        body: &'a Evidence,
        scope: &mut Scope<'a>,
        (path, assumption, explanation): (&str, String, &'static str),
    ) -> Result<(String, Proposition), String> {
        self.charge(premise)?;
        if binder.is_empty() {
            return Err(format!("{path}: empty hypothesis binder"));
        }
        scope.hyps.push((
            binder,
            premise.clone(),
            assumption.clone(),
            scope.binders.len(),
        ));
        let context_id = self.context_id(scope);
        let mut variables = scope
            .variables
            .iter()
            .map(|var| (var.name.as_str(), var.sort))
            .collect();
        self.steps.push(Step {
            id: assumption.clone(),
            rule: "local_assumption",
            explanation,
            context_id,
            conclusion_sort: Sort::Prop,
            premises: Vec::new(),
            conclusion: premise.clone(),
            conclusion_text: self.render_scoped(premise, false, false, &mut variables),
            binder: Some(binder.to_owned()),
            discharged: None,
            discharged_cases: None,
            reference_id: None,
            substitutions: None,
            context: None,
            binder_sort: None,
            introduced_variable: None,
            introduced_hypothesis: Some(assumption.clone()),
            provenance: None,
            law: None,
            premise_conversion: None,
            conclusion_conversion: None,
        });
        let result = self.infer(body, scope, path);
        scope.hyps.pop();
        Ok((assumption, result?))
    }

    fn infer(
        &mut self,
        evidence: &'a Evidence,
        scope: &mut Scope<'a>,
        path: &str,
    ) -> Result<Proposition, String> {
        if self.steps.len() >= MAX_STEPS {
            return Err("proof steps exceed resource limit".into());
        }
        let mut reference_id = None;
        let mut substitutions = None;
        let mut context = None;
        let mut binder_sort = None;
        let mut introduced_variable = None;
        let mut introduced_hypothesis = None;
        let mut discharged_cases = None;
        let mut provenance = None;
        let mut law = None;
        let mut premise_conversion = None;
        let (rule, premises, conclusion, binder, discharged) = match evidence {
            Evidence::ImpliesIntro {
                binder,
                premise,
                body,
            } => {
                self.sort(premise, &scope.binders)?.expect(Sort::Prop)?;
                let body_path = format!("{path}.body");
                let (assumption, result) = self.infer_under_hypothesis(
                    binder,
                    premise,
                    body,
                    scope,
                    (
                        &body_path,
                        format!("{path}.assumption"),
                        rule_explanation("local_assumption", None),
                    ),
                )?;
                introduced_hypothesis = Some(assumption.clone());
                let conclusion = Proposition::Implies {
                    left: Box::new(premise.clone()),
                    right: Box::new(result),
                };
                (
                    "implies_intro",
                    vec![assumption.clone(), body_path],
                    conclusion,
                    Some(binder.clone()),
                    Some(assumption),
                )
            }
            Evidence::ImpliesElim {
                implication,
                premise,
            } => {
                let impl_path = format!("{path}.implication");
                let premise_path = format!("{path}.premise");
                let inferred = self.infer(implication, scope, &impl_path)?;
                let implication = if matches!(inferred, Proposition::Implies { .. }) {
                    inferred
                } else {
                    convert(&inferred, &self.functions)?
                };
                let Proposition::Implies { left, right } = implication else {
                    return Err(format!("{path}: implies_elim requires an implication"));
                };
                let premise = self.infer(premise, scope, &premise_path)?;
                premise_conversion = self.compare(&left, &premise)?.ok_or_else(|| {
                    format!("{path}: implication antecedent does not match premise")
                })?;
                (
                    "implies_elim",
                    vec![impl_path, premise_path],
                    *right,
                    None,
                    None,
                )
            }
            Evidence::OrIntroL { proof, other } | Evidence::OrIntroR { proof, other } => {
                self.sort(other, &scope.binders)?.expect(Sort::Prop)?;
                self.charge(other)?;
                let proof_path = format!("{path}.proof");
                let known = Box::new(self.infer(proof, scope, &proof_path)?);
                let other = Box::new(other.clone());
                let (rule, left, right) = if matches!(evidence, Evidence::OrIntroL { .. }) {
                    ("or_intro_l", known, other)
                } else {
                    ("or_intro_r", other, known)
                };
                (
                    rule,
                    vec![proof_path],
                    Proposition::Or { left, right },
                    None,
                    None,
                )
            }
            Evidence::OrElim {
                proof,
                binder,
                left,
                right,
            } => {
                let proof_path = format!("{path}.proof");
                let inferred = self.infer(proof, scope, &proof_path)?;
                let disjunction = if matches!(inferred, Proposition::Or { .. }) {
                    inferred
                } else {
                    convert(&inferred, &self.functions)?
                };
                let Proposition::Or { left: a, right: b } = disjunction else {
                    return Err(format!("{path}: or_elim requires a disjunction"));
                };
                let left_path = format!("{path}.left");
                let (left_assumption, left_result) = self.infer_under_hypothesis(
                    binder,
                    &a,
                    left,
                    scope,
                    (
                        &left_path,
                        format!("{left_path}.assumption"),
                        "Assume the left disjunct for the first case.",
                    ),
                )?;
                let right_path = format!("{path}.right");
                let (right_assumption, right_result) = self.infer_under_hypothesis(
                    binder,
                    &b,
                    right,
                    scope,
                    (
                        &right_path,
                        format!("{right_path}.assumption"),
                        "Assume the right disjunct for the second case.",
                    ),
                )?;
                premise_conversion = self
                    .compare(&left_result, &right_result)?
                    .ok_or_else(|| format!("{path}: case branches prove different conclusions"))?;
                discharged_cases = Some([left_assumption.clone(), right_assumption.clone()]);
                (
                    "or_elim",
                    vec![
                        proof_path,
                        left_assumption,
                        left_path,
                        right_assumption,
                        right_path,
                    ],
                    left_result,
                    Some(binder.clone()),
                    None,
                )
            }
            Evidence::NotIntro { proof } => {
                let proof_path = format!("{path}.proof");
                let inferred = self.infer(proof, scope, &proof_path)?;
                let implication = if matches!(inferred, Proposition::Implies { .. }) {
                    inferred
                } else {
                    convert(&inferred, &self.functions)?
                };
                let Proposition::Implies { left, right } = implication else {
                    return Err(format!(
                        "{path}: not_intro requires an implication to falsehood"
                    ));
                };
                premise_conversion =
                    self.compare(&right, &Proposition::False)?.ok_or_else(|| {
                        format!("{path}: not_intro requires an implication to falsehood")
                    })?;
                (
                    "not_intro",
                    vec![proof_path],
                    Proposition::Not { operand: left },
                    None,
                    None,
                )
            }
            Evidence::NotElim { negation, premise } => {
                let neg_path = format!("{path}.negation");
                let premise_path = format!("{path}.premise");
                let inferred = self.infer(negation, scope, &neg_path)?;
                let negation = if matches!(inferred, Proposition::Not { .. }) {
                    inferred
                } else {
                    convert(&inferred, &self.functions)?
                };
                let Proposition::Not { operand } = negation else {
                    return Err(format!("{path}: not_elim requires a negation"));
                };
                let premise = self.infer(premise, scope, &premise_path)?;
                premise_conversion = self
                    .compare(&operand, &premise)?
                    .ok_or_else(|| format!("{path}: negation operand does not match premise"))?;
                (
                    "not_elim",
                    vec![neg_path, premise_path],
                    Proposition::False,
                    None,
                    None,
                )
            }
            Evidence::ExFalso { proof, conclusion } => {
                self.sort(conclusion, &scope.binders)?.expect(Sort::Prop)?;
                self.charge(conclusion)?;
                let proof_path = format!("{path}.proof");
                let premise = self.infer(proof, scope, &proof_path)?;
                premise_conversion = self
                    .compare(&premise, &Proposition::False)?
                    .ok_or_else(|| format!("{path}: ex_falso requires a proof of falsehood"))?;
                ("ex_falso", vec![proof_path], conclusion.clone(), None, None)
            }
            Evidence::HypRef { binder } => {
                let (_, proposition, assumption, depth) = scope
                    .hyps
                    .iter()
                    .rev()
                    .find(|(name, _, _, _)| *name == binder)
                    .ok_or_else(|| format!("{path}: out-of-scope hypothesis {binder:?}"))?;
                provenance = Some(Provenance {
                    kind: "local_hypothesis",
                    id: assumption.clone(),
                    proof_step: Some(assumption.clone()),
                });
                (
                    "hyp_ref",
                    vec![assumption.clone()],
                    proposition.shift(scope.binders.len() - depth),
                    Some(binder.clone()),
                    None,
                )
            }
            Evidence::AxiomRef { id } => {
                let axiom = self
                    .axioms
                    .get(id.as_str())
                    .ok_or_else(|| format!("{path}: unknown axiom reference {id:?}"))?;
                reference_id = Some(id.clone());
                provenance = Some(Provenance {
                    kind: "custom_axiom",
                    id: id.clone(),
                    proof_step: None,
                });
                ("axiom_ref", Vec::new(), axiom.statement.clone(), None, None)
            }
            Evidence::TheoremRef { id } => {
                let lemma = self
                    .checked_lemmas
                    .get(id.as_str())
                    .ok_or_else(|| format!("{path}: unknown theorem reference {id:?}"))?;
                reference_id = Some(id.clone());
                provenance = Some(Provenance {
                    kind: "checked_lemma",
                    id: id.clone(),
                    proof_step: Some(lemma_path(id)),
                });
                (
                    "theorem_ref",
                    vec![lemma_path(id)],
                    lemma.statement.clone(),
                    None,
                    None,
                )
            }
            Evidence::ForallIntro { name, sort, body } => {
                // Extending the index scope introduces a fresh variable. Existing
                // hypotheses are lifted on lookup, so they cannot mention it.
                scope.binders.push(*sort);
                let binding = Variable {
                    id: format!("{path}.variable"),
                    name: name.clone(),
                    sort: *sort,
                };
                introduced_variable = Some(binding.id.clone());
                scope.variables.push(binding);
                let body_path = format!("{path}.body");
                let result = self.infer(body, scope, &body_path);
                scope.binders.pop();
                scope.variables.pop();
                binder_sort = Some(*sort);
                let conclusion = Proposition::Forall {
                    name: name.clone(),
                    sort: *sort,
                    body: Box::new(result?),
                };
                (
                    "forall_intro",
                    vec![body_path],
                    conclusion,
                    Some(name.clone()),
                    None,
                )
            }
            Evidence::ForallElim { proof, term } => {
                let proof_path = format!("{path}.proof");
                let inferred = self.infer(proof, scope, &proof_path)?;
                let universal = if matches!(inferred, Proposition::Forall { .. }) {
                    inferred
                } else {
                    convert(&inferred, &self.functions)?
                };
                let Proposition::Forall { sort, body, .. } = universal else {
                    return Err(format!("{path}: forall_elim requires a universal premise"));
                };
                self.sort(term, &scope.binders)?.expect(sort)?;
                substitutions = Some(vec![term.clone()]);
                let conclusion = instantiate_bounded(&body, std::slice::from_ref(term))?;
                ("forall_elim", vec![proof_path], conclusion, None, None)
            }
            Evidence::ExistsIntro {
                goal,
                witness,
                proof,
            } => {
                let Proposition::Exists { name, sort, body } = goal else {
                    return Err(format!("{path}: exists_intro requires an existential goal"));
                };
                self.sort(goal, &scope.binders)
                    .map_err(|error| format!("{path}: existential goal {error}"))?;
                self.sort(witness, &scope.binders)
                    .and_then(|actual| actual.expect(*sort))
                    .map_err(|error| format!("{path}: existential witness {error}"))?;

                // The existential binder scopes only over its predicate. Both the
                // witness and its evidence use the surrounding proof scope.
                let expected = instantiate_bounded(body, std::slice::from_ref(witness))?;
                let proof_path = format!("{path}.proof");
                let actual = self.infer(proof, scope, &proof_path)?;
                premise_conversion = self.compare(&expected, &actual)?.ok_or_else(|| {
                    format!(
                        "{path}: proof does not establish the instantiated existential predicate"
                    )
                })?;
                self.charge(witness)?;
                substitutions = Some(vec![witness.clone()]);
                binder_sort = Some(*sort);
                (
                    "exists_intro",
                    vec![proof_path],
                    goal.clone(),
                    Some(name.clone()),
                    None,
                )
            }
            Evidence::Refl { term } => {
                self.sort(term, &scope.binders)?;
                let conclusion = Proposition::Eq {
                    left: Box::new(term.clone()),
                    right: Box::new(term.clone()),
                };
                ("refl", Vec::new(), conclusion, None, None)
            }
            Evidence::Symm { proof } => {
                let proof_path = format!("{path}.proof");
                let inferred = self.infer(proof, scope, &proof_path)?;
                let (right, left) = self.equality(inferred, path)?;
                (
                    "symm",
                    vec![proof_path],
                    Proposition::Eq { left, right },
                    None,
                    None,
                )
            }
            Evidence::Trans { left, right } => {
                let left_path = format!("{path}.left");
                let right_path = format!("{path}.right");
                let lhs = self.infer(left, scope, &left_path)?;
                let rhs = self.infer(right, scope, &right_path)?;
                let (left, middle_left) = self.equality(lhs, path)?;
                let (middle_right, right) = self.equality(rhs, path)?;
                premise_conversion = self
                    .compare(&middle_left, &middle_right)?
                    .ok_or_else(|| format!("{path}: transitivity middle terms do not match"))?;
                (
                    "trans",
                    vec![left_path, right_path],
                    Proposition::Eq { left, right },
                    None,
                    None,
                )
            }
            Evidence::Congr {
                context: template,
                proof,
            } => {
                let proof_path = format!("{path}.proof");
                let inferred = self.infer(proof, scope, &proof_path)?;
                let (left, right) = self.equality(inferred, path)?;
                let sort = self.sort(&left, &scope.binders)?;
                scope.binders.push(sort);
                let result = self.sort(template, &scope.binders);
                scope.binders.pop();
                result?;
                context = Some(template.clone());
                binder_sort = Some(sort);
                let apply = |arg| instantiate_bounded(template, &[arg]).map(Box::new);
                let conclusion = Proposition::Eq {
                    left: apply(*left)?,
                    right: apply(*right)?,
                };
                ("congr", vec![proof_path], conclusion, None, None)
            }
            Evidence::CoreLaw { id, args } => {
                let formals =
                    law_formals(id).ok_or_else(|| format!("{path}: unknown core law {id:?}"))?;
                if args.len() != formals.len() {
                    return Err(format!(
                        "{path}: core law {id:?} requires {} substitutions",
                        formals.len()
                    ));
                }
                for arg in args {
                    self.sort(arg, &scope.binders)?.expect(Sort::Int)?;
                }
                reference_id = Some(id.clone());
                substitutions = Some(args.clone());
                provenance = Some(Provenance {
                    kind: "core_law",
                    id: id.clone(),
                    proof_step: None,
                });
                let formal_args: Vec<_> = formals
                    .iter()
                    .map(|name| Proposition::Symbol { id: (*name).into() })
                    .collect();
                law = Some(LawApplication {
                    id: id.clone(),
                    formal_statement: instantiate_law(id, &formal_args)
                        .expect("checked law and arity"),
                    substitution: formals
                        .iter()
                        .zip(args)
                        .map(|(formal, actual)| Substitution {
                            formal,
                            actual: actual.clone(),
                            sort: Sort::Int,
                        })
                        .collect(),
                });
                let conclusion = instantiate_law(id, args).expect("checked law and arity");
                ("core_law", Vec::new(), conclusion, None, None)
            }
            Evidence::Block { steps, result } => {
                scope.blocks.push(BlockScope {
                    depth: scope.binders.len(),
                    entries: HashMap::new(),
                });
                for index in block_order(steps, *result)? {
                    let step_path = format!("{path}.steps[{index}]");
                    let conclusion = self.infer(&steps[index], scope, &step_path)?;
                    scope
                        .blocks
                        .last_mut()
                        .unwrap()
                        .entries
                        .insert(index, (conclusion, step_path));
                }
                let mut block = scope.blocks.pop().unwrap();
                let (conclusion, result_path) =
                    block.entries.remove(result).expect("result step checked");
                ("block", vec![result_path], conclusion, None, None)
            }
            Evidence::StepRef { index } => {
                let block = scope
                    .blocks
                    .last()
                    .ok_or_else(|| format!("{path}: out-of-scope block step"))?;
                let (statement, step_path) = block
                    .entries
                    .get(index)
                    .ok_or_else(|| format!("{path}: out-of-scope block step {index}"))?;
                (
                    "step_ref",
                    vec![step_path.clone()],
                    statement.shift(scope.binders.len() - block.depth),
                    None,
                    None,
                )
            }
            Evidence::AndIntro { left, right } => {
                let left_path = format!("{path}.left");
                let right_path = format!("{path}.right");
                let left = self.infer(left, scope, &left_path)?;
                let right = self.infer(right, scope, &right_path)?;
                (
                    "and_intro",
                    vec![left_path, right_path],
                    Proposition::And {
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    None,
                    None,
                )
            }
            Evidence::AndElimL { proof } | Evidence::AndElimR { proof } => {
                let proof_path = format!("{path}.proof");
                let left_rule = matches!(evidence, Evidence::AndElimL { .. });
                let rule = if left_rule {
                    "and_elim_l"
                } else {
                    "and_elim_r"
                };
                let inferred = self.infer(proof, scope, &proof_path)?;
                let premise = if matches!(inferred, Proposition::And { .. }) {
                    inferred
                } else {
                    convert(&inferred, &self.functions)?
                };
                let Proposition::And { left, right } = premise else {
                    return Err(format!("{path}: {rule} requires a conjunction"));
                };
                (
                    rule,
                    vec![proof_path],
                    if left_rule { *left } else { *right },
                    None,
                    None,
                )
            }
        };
        self.charge(&conclusion)?;
        if let Some(item) = &premise_conversion {
            self.charge(&item.left)?;
            self.charge(&item.right)?;
            self.charge(&item.common_normal_form)?;
        }
        let context_id = self.context_id(scope);
        let mut variables = scope
            .variables
            .iter()
            .map(|var| (var.name.as_str(), var.sort))
            .collect();
        self.steps.push(Step {
            id: path.to_owned(),
            rule,
            explanation: rule_explanation(rule, reference_id.as_deref()),
            context_id,
            conclusion_sort: Sort::Prop,
            premises,
            conclusion_text: self.render_scoped(&conclusion, false, false, &mut variables),
            conclusion: conclusion.clone(),
            binder,
            discharged,
            discharged_cases,
            reference_id,
            substitutions,
            context,
            binder_sort,
            introduced_variable,
            introduced_hypothesis,
            provenance,
            law,
            premise_conversion,
            conclusion_conversion: None,
        });
        Ok(conclusion)
    }
}

fn lemma_path(id: &str) -> String {
    format!("lemma[{id:?}].proof")
}
