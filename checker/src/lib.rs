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
    AndElimL {
        proof: Box<Self>,
    },
    AndElimR {
        proof: Box<Self>,
    },
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
    custom_axioms: Vec<serde_json::Value>,
    lemmas: Vec<serde_json::Value>,
    target: Proposition,
    proof: Evidence,
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
    pub custom_axioms: Vec<Proposition>,
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
    if !bundle.custom_axioms.is_empty() || !bundle.lemmas.is_empty() {
        return Err("custom axioms and lemma dependencies are unsupported in this fragment".into());
    }

    let mut declarations = HashMap::new();
    for declaration in &bundle.declarations {
        if declaration.id.is_empty() {
            return Err("empty declaration ID".into());
        }
        if declarations
            .insert(declaration.id.as_str(), declaration)
            .is_some()
        {
            return Err(format!("duplicate declaration ID {:?}", declaration.id));
        }
    }

    let mut checker = Checker::new(declarations);
    checker.check_proposition(&bundle.target)?;
    let statement = checker.infer(&bundle.proof, &mut Vec::new(), "proof")?;
    let statement_text = checker.render(&statement, false);
    if statement != bundle.target {
        return Err(format!(
            "proof conclusion mismatch\nExpected: {}\nDerived:  {statement_text}",
            checker.render(&bundle.target, false)
        ));
    }

    let steps = checker.steps;
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
            custom_axioms: Vec::new(),
        },
        steps,
    })
}

struct Checker<'a> {
    declarations: Declarations<'a>,
    ambiguous_names: HashSet<&'a str>,
    steps: Vec<Step>,
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
        }
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

    fn render(&self, proposition: &Proposition, nested: bool) -> String {
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
                return if self.ambiguous_names.contains(name) {
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
            self.render(left, true),
            self.render(right, true)
        );
        if nested { format!("({text})") } else { text }
    }

    fn infer(
        &mut self,
        evidence: &'a Evidence,
        scope: &mut Scope<'a>,
        path: &str,
    ) -> Result<Proposition, String> {
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
                    conclusion_text: self.render(premise, false),
                    binder: Some(binder.clone()),
                    discharged: None,
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
            conclusion_text: self.render(&conclusion, false),
            conclusion: conclusion.clone(),
            binder,
            discharged,
        });
        Ok(conclusion)
    }
}
