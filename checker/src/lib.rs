//! Verification for the first portable Logos proof fragment.
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet};

pub const FORMAT: &str = "logos-proof-v1";
pub const THEORY: &str = "logos-core-v1";
pub const PROTOCOL_VERSION: u32 = 1;

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "tag", rename_all = "snake_case", deny_unknown_fields)]
pub enum Proposition {
    Symbol { id: String },
    And { left: Box<Self>, right: Box<Self> },
    Implies { left: Box<Self>, right: Box<Self> },
}

#[derive(Deserialize)]
#[serde(tag = "tag", rename_all = "snake_case", deny_unknown_fields)]
enum Evidence {
    ImpliesIntro {
        binder: String,
        premise: Proposition,
        body: Box<Self>,
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
}

impl Evidence {
    fn lemma_dependencies<'a>(&'a self, dependencies: &mut Vec<&'a str>) {
        match self {
            Self::ImpliesIntro { body, .. } => body.lemma_dependencies(dependencies),
            Self::AndElimL { proof } | Self::AndElimR { proof } => {
                proof.lemma_dependencies(dependencies);
            }
            Self::AndIntro { left, right } => {
                left.lemma_dependencies(dependencies);
                right.lemma_dependencies(dependencies);
            }
            Self::TheoremRef { id } => dependencies.push(id),
            Self::AxiomRef { .. } | Self::HypRef { .. } => {}
        }
    }
}

#[derive(Clone, Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Sort {
    Prop,
    Int,
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
    pub statement: Proposition,
    pub statement_text: String,
    pub custom_axioms: Vec<UsedAxiom>,
}

#[derive(Serialize)]
pub struct Step {
    pub id: String,
    pub rule: &'static str,
    pub premises: Vec<String>,
    pub conclusion: Proposition,
    pub conclusion_text: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub binder: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reference_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub discharged: Option<String>,
}

pub struct Verified {
    pub judgment: Judgment,
    pub steps: Vec<Step>,
}

type Declarations<'a> = HashMap<&'a str, &'a Declaration>;
type Scope<'a> = Vec<(&'a str, &'a Proposition, String)>;

pub fn verify(bytes: &[u8]) -> Result<Verified, String> {
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
    // Validate every supplied lemma, in dependency order and with an empty local scope.
    for lemma in &bundle.lemmas {
        checker.check_lemmas(lemma, &lemmas)?;
    }
    let statement = checker.check_conclusion(&bundle.proof, &bundle.target, "proof")?;
    let statement_text = checker.render(&statement, false, false);
    let (custom_axioms, steps) = checker.target_trace();
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
            statement,
            statement_text,
            custom_axioms,
        },
        steps,
    })
}

struct Checker<'a> {
    declarations: Declarations<'a>,
    ambiguous_names: HashSet<&'a str>,
    steps: Vec<Step>,
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
            ambiguous_names,
            steps: Vec::new(),
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
                lemma.proof.lemma_dependencies(&mut dependencies);
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
        let derived = self.infer(evidence, &mut Vec::new(), path)?;
        if &derived != expected {
            let location = if path == "proof" {
                String::new()
            } else {
                format!("{path}: ")
            };
            return Err(format!(
                "{location}proof conclusion mismatch\nExpected: {}\nDerived:  {}",
                self.render(expected, false, false),
                self.render(&derived, false, false),
            ));
        }
        Ok(derived)
    }

    fn target_trace(self) -> (Vec<UsedAxiom>, Vec<Step>) {
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
        (used, steps)
    }

    fn check_proposition(&self, proposition: &Proposition) -> Result<(), String> {
        match proposition {
            Proposition::Symbol { id } => match self.declarations.get(id.as_str()) {
                Some(declaration) if declaration.sort == Sort::Prop => Ok(()),
                Some(_) => Err(format!("declaration {id:?} has sort int, expected prop")),
                None => Err(format!("undeclared symbol {id:?}")),
            },
            Proposition::And { left, right } | Proposition::Implies { left, right } => {
                self.check_proposition(left)?;
                self.check_proposition(right)
            }
        }
    }

    fn render(&self, proposition: &Proposition, nested: bool, typed: bool) -> String {
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
                    format!("{label}[{id:?}]:prop")
                } else if self.ambiguous_names.contains(name) {
                    format!("{label}[{id:?}]")
                } else {
                    label
                };
            }
            Proposition::And { left, right } => (left, "∧", right),
            Proposition::Implies { left, right } => (left, "→", right),
        };
        let text = format!(
            "{} {op} {}",
            self.render(left, true, typed),
            self.render(right, true, typed)
        );
        if nested { format!("({text})") } else { text }
    }

    fn infer(
        &mut self,
        evidence: &'a Evidence,
        scope: &mut Scope<'a>,
        path: &str,
    ) -> Result<Proposition, String> {
        let mut reference_id = None;
        let (rule, premises, conclusion, binder, discharged) = match evidence {
            Evidence::ImpliesIntro {
                binder,
                premise,
                body,
            } => {
                self.check_proposition(premise)?;
                if binder.is_empty() {
                    return Err(format!("{path}: empty hypothesis binder"));
                }
                let assumption = format!("{path}.assumption");
                self.steps.push(Step {
                    id: assumption.clone(),
                    rule: "local_assumption",
                    premises: Vec::new(),
                    conclusion: premise.clone(),
                    conclusion_text: self.render(premise, false, false),
                    binder: Some(binder.clone()),
                    discharged: None,
                    reference_id: None,
                });
                scope.push((binder, premise, assumption.clone()));
                let body_path = format!("{path}.body");
                let result = self.infer(body, scope, &body_path);
                scope.pop();
                let conclusion = Proposition::Implies {
                    left: Box::new(premise.clone()),
                    right: Box::new(result?),
                };
                (
                    "implies_intro",
                    vec![assumption.clone(), body_path],
                    conclusion,
                    Some(binder.clone()),
                    Some(assumption),
                )
            }
            Evidence::HypRef { binder } => {
                let (_, proposition, assumption) = scope
                    .iter()
                    .rev()
                    .find(|(name, _, _)| *name == binder)
                    .ok_or_else(|| format!("{path}: out-of-scope hypothesis {binder:?}"))?;
                (
                    "hyp_ref",
                    vec![assumption.clone()],
                    (*proposition).clone(),
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
                ("axiom_ref", Vec::new(), axiom.statement.clone(), None, None)
            }
            Evidence::TheoremRef { id } => {
                let lemma = self
                    .checked_lemmas
                    .get(id.as_str())
                    .ok_or_else(|| format!("{path}: unknown theorem reference {id:?}"))?;
                reference_id = Some(id.clone());
                (
                    "theorem_ref",
                    vec![lemma_path(id)],
                    lemma.statement.clone(),
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
                let Proposition::And { left, right } = self.infer(proof, scope, &proof_path)?
                else {
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
        self.steps.push(Step {
            id: path.to_owned(),
            rule,
            premises,
            conclusion_text: self.render(&conclusion, false, false),
            conclusion: conclusion.clone(),
            binder,
            discharged,
            reference_id,
        });
        Ok(conclusion)
    }
}

fn lemma_path(id: &str) -> String {
    format!("lemma[{id:?}].proof")
}
