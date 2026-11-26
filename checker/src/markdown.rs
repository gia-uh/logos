use logos_checker::{Judgment, Proposition, Sort, Verified};
use std::collections::HashMap;
use std::fmt::Write;

pub fn render(checked: &Verified) -> String {
    let judgment = &checked.judgment;
    let math = Math::new(judgment);
    let steps: HashMap<_, _> = checked
        .steps
        .iter()
        .enumerate()
        .map(|(index, step)| (step.id.as_str(), index + 1))
        .collect();
    let step_number = |id: &str| steps[id];
    let mut out = String::new();
    writeln!(out, "# Checked proof\n").unwrap();
    let verdict = if judgment.status == "policy_denied" {
        "Valid derivation. Strict policy denied it because it uses custom axioms."
    } else {
        "Verified."
    };
    writeln!(out, "{verdict}\n").unwrap();
    writeln!(out, "- Theory: `{}`", judgment.theory).unwrap();
    writeln!(out, "- Artifact SHA-256: `{}`", judgment.artifact_sha256).unwrap();
    if let Some(label) = &judgment.unverified_author_label {
        writeln!(out, "- Unverified author label: {}", code(label)).unwrap();
    }
    writeln!(out, "\n## Theorem").unwrap();
    display(&mut out, &math.formula(&judgment.statement, &[]));

    writeln!(out, "## Domains and definitions\n").unwrap();
    writeln!(out, "- $`\\mathbb{{Z}}`$ is the type of mathematical integers. $`\\mathsf{{Prop}}`$ is the type of propositions.").unwrap();
    for symbol in &judgment.declarations {
        writeln!(
            out,
            "- Free symbol $`{} \\in {}`$ (declaration {}).",
            math.symbols[symbol.id.as_str()],
            domain(symbol.sort),
            code(&symbol.id),
        )
        .unwrap();
    }
    for function in &judgment.functions {
        let label = &math.functions[function.id.as_str()];
        let mut params = Vec::new();
        for (index, sort) in function.params.iter().enumerate() {
            params.push(format!("p_{{{}}}", index + 1));
            writeln!(
                out,
                "- Parameter $`{} \\in {}`$ of $`{label}`$.",
                params[index],
                domain(*sort)
            )
            .unwrap();
        }
        let call = format!("{label}\\left({}\\right)", params.join(", "));
        if let Some(body) = &function.body {
            writeln!(
                out,
                "- Transparent definition {} with result type $`{}`$.",
                code(&function.id),
                domain(function.result)
            )
            .unwrap();
            display(
                &mut out,
                &format!("{call} \\mathrel{{:=}} {}", math.formula(body, &params)),
            );
        } else {
            writeln!(
                out,
                "- Opaque function $`{call}`$ with result type $`{}`$ (declaration {}).",
                domain(function.result),
                code(&function.id)
            )
            .unwrap();
        }
    }
    writeln!(out, "\n## Custom axioms\n").unwrap();
    if judgment.custom_axioms.is_empty() {
        writeln!(out, "Uses zero custom axioms.\n").unwrap();
    }
    for axiom in &judgment.custom_axioms {
        let first_use = axiom.path.last().expect("checker recorded the axiom use");
        writeln!(
            out,
            "Assume {}. The checked trace uses it at Step {}.",
            code(&axiom.id),
            step_number(first_use),
        )
        .unwrap();
        display(&mut out, &math.formula(&axiom.statement, &[]));
    }

    writeln!(out, "## Proof scopes\n").unwrap();
    for scope in &checked.contexts {
        let variables = scoped_names(scope.variables.iter().map(|var| var.name.as_str()));
        let mut active: Vec<_> = scope
            .variables
            .iter()
            .zip(&variables)
            .map(|(var, latex)| format!("$`{latex} \\in {}`$", domain(var.sort)))
            .collect();
        active.extend(
            scope
                .hypotheses
                .iter()
                .map(|hyp| format!("hypothesis from Step {}", step_number(&hyp.id))),
        );
        if active.is_empty() {
            active.push("no local variables or hypotheses".into());
        }
        writeln!(out, "- Scope {}: {}.", scope.id + 1, active.join(", ")).unwrap();
    }
    writeln!(out, "\n## Proof steps\n").unwrap();
    for (index, step) in checked.steps.iter().enumerate() {
        let scope = &checked.contexts[step.context_id];
        let vars = scoped_names(scope.variables.iter().map(|var| var.name.as_str()));
        writeln!(
            out,
            "**Step {}** (scope {}). {}",
            index + 1,
            scope.id + 1,
            step.explanation,
        )
        .unwrap();
        if !step.premises.is_empty() {
            let premises = step
                .premises
                .iter()
                .map(|id| step_number(id).to_string())
                .collect::<Vec<_>>();
            writeln!(out, " Premises: {}.", premises.join(", ")).unwrap();
        }
        if let Some(id) = &step.discharged {
            writeln!(
                out,
                " Discharges the hypothesis introduced at Step {}.",
                step_number(id)
            )
            .unwrap();
        }
        if let Some(id) = &step.introduced_variable {
            let body = &checked.steps[step_number(&step.premises[0]) - 1];
            let body_scope = &checked.contexts[body.context_id];
            let pos = body_scope
                .variables
                .iter()
                .position(|var| &var.id == id)
                .expect("introduced variable is in the body scope");
            let names = scoped_names(body_scope.variables.iter().map(|var| var.name.as_str()));
            writeln!(
                out,
                " The arbitrary variable $`{} \\in {}`$ was introduced in Step {}'s scope.",
                names[pos],
                domain(body_scope.variables[pos].sort),
                step_number(&body.id)
            )
            .unwrap();
        }
        if let Some(provenance) = &step.provenance {
            match provenance.kind {
                "custom_axiom" => writeln!(out, " Custom axiom {}.", code(&provenance.id)).unwrap(),
                "checked_lemma" => {
                    writeln!(out, " Checked lemma {}.", code(&provenance.id)).unwrap()
                }
                _ => {}
            }
        }
        if let Some(law) = &step.law {
            let substitutions = law
                .substitution
                .iter()
                .map(|sub| {
                    format!(
                        "{} \\mapsto {}",
                        name(sub.formal),
                        math.formula(&sub.actual, &vars),
                    )
                })
                .collect::<Vec<_>>();
            writeln!(
                out,
                " Core law {} with $`{}`$.",
                code(&law.id),
                substitutions.join(", ")
            )
            .unwrap();
            writeln!(
                out,
                " Its formal equality is $`{}`$.",
                math.formal(&law.formal_statement)
            )
            .unwrap();
        }
        if let Some(template) = &step.context {
            let mut with_hole = vars.clone();
            with_hole.push("\\square".into());
            writeln!(
                out,
                " The substitution context is $`{}`$.",
                math.formula(template, &with_hole)
            )
            .unwrap();
        }
        if step.rule == "forall_elim" {
            let witness = &step.substitutions.as_ref().expect("checked witness")[0];
            writeln!(
                out,
                " The witness term is $`{}`$.",
                math.formula(witness, &vars)
            )
            .unwrap();
        }
        display(&mut out, &math.formula(&step.conclusion, &vars));
        for (label, left_label, right_label, conversion) in [
            (
                "Premise conversion",
                "First middle expression",
                "Second middle expression",
                &step.premise_conversion,
            ),
            (
                "Conclusion conversion",
                "Derived statement",
                "Declared statement",
                &step.conclusion_conversion,
            ),
        ] {
            if let Some(conversion) = conversion {
                writeln!(
                    out,
                    "**{label}.** {} The rows show the two compared forms and their checked common normal form.",
                    conversion.explanation,
                ).unwrap();
                let left = math.formula(&conversion.left, &vars);
                let right = math.formula(&conversion.right, &vars);
                let normal = math.formula(&conversion.common_normal_form, &vars);
                display(
                    &mut out,
                    &format!(
                        "\\begin{{aligned}}\n\\text{{{left_label}}}\\quad & {left} \\\\\n\\text{{{right_label}}}\\quad & {right} \\\\\n\\text{{Common normal form}}\\quad & {normal}\n\\end{{aligned}}",
                    ),
                );
            }
        }
    }
    writeln!(out, "## Conclusion\n").unwrap();
    let condition = if judgment.custom_axioms.is_empty() {
        ""
    } else {
        " under the listed custom axioms"
    };
    writeln!(
        out,
        "The theorem follows from Step {}{}.",
        step_number("proof"),
        condition
    )
    .unwrap();
    display(&mut out, &math.formula(&judgment.statement, &[]));
    out
}

fn display(out: &mut String, math: &str) {
    writeln!(out, "\n$$\n{math}\n$$\n").unwrap();
}

fn domain(sort: Sort) -> &'static str {
    match sort {
        Sort::Int => "\\mathbb{Z}",
        Sort::Prop => "\\mathsf{Prop}",
    }
}

// Code spans and math have different escaping rules. Encode characters outside
// their safe alphabets with their Unicode code points.
fn code(label: &str) -> String {
    let mut text = String::from("`");
    for c in label.chars() {
        if c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '.' | ' ') {
            text.push(c);
        } else {
            write!(text, "[U+{:04X}]", c as u32).unwrap();
        }
    }
    if label.is_empty() {
        text.push_str("(empty)");
    }
    text.push('`');
    text
}

fn name(label: &str) -> String {
    if label.len() == 1 && label.as_bytes()[0].is_ascii_alphabetic() {
        return label.into();
    }
    if label.is_empty() {
        return "v".into();
    }
    let mut latex = String::from("\\mathrm{");
    for c in label.chars() {
        if c.is_ascii_alphanumeric() {
            latex.push(c);
        } else if c == '_' {
            latex.push_str("\\_");
        } else {
            write!(latex, "\\langle U+{:04X}\\rangle", c as u32).unwrap();
        }
    }
    latex.push('}');
    latex
}

fn push_name(vars: &mut Vec<String>, label: &str) {
    let base = name(label);
    let mut unique = base.clone();
    let mut suffix = 2;
    while vars.contains(&unique) {
        unique = format!("{base}_{{{suffix}}}");
        suffix += 1;
    }
    vars.push(unique);
}

fn scoped_names<'a>(labels: impl Iterator<Item = &'a str>) -> Vec<String> {
    let mut vars = Vec::new();
    for label in labels {
        push_name(&mut vars, label);
    }
    vars
}

struct Math<'a> {
    symbols: HashMap<&'a str, String>,
    functions: HashMap<&'a str, String>,
}

impl<'a> Math<'a> {
    fn new(judgment: &'a Judgment) -> Self {
        let symbols = judgment
            .declarations
            .iter()
            .enumerate()
            .map(|(index, item)| {
                (
                    item.id.as_str(),
                    format!("{}_{{s{}}}", name(&item.name), index + 1),
                )
            })
            .collect();
        let functions = judgment
            .functions
            .iter()
            .enumerate()
            .map(|(index, item)| {
                (
                    item.id.as_str(),
                    format!("{}_{{f{}}}", name(&item.name), index + 1),
                )
            })
            .collect();
        Self { symbols, functions }
    }

    fn formula(&self, formula: &Proposition, vars: &[String]) -> String {
        self.term(formula, &mut vars.to_vec(), false, false)
    }

    fn formal(&self, formula: &Proposition) -> String {
        self.term(formula, &mut Vec::new(), false, true)
    }

    fn term(
        &self,
        formula: &Proposition,
        vars: &mut Vec<String>,
        nested: bool,
        formal: bool,
    ) -> String {
        use Proposition::*;
        let (left, operator, right) = match formula {
            Symbol { id } => {
                return if formal {
                    name(id)
                } else {
                    self.symbols[id.as_str()].clone()
                };
            }
            Bound { index } => return vars[vars.len() - index - 1].clone(),
            Int { value } if nested && value.starts_with('-') => {
                return format!("\\left({value}\\right)");
            }
            Int { value } => return value.clone(),
            Add { left, right } => (left, "+", right),
            Sub { left, right } => (left, "-", right),
            Mul { left, right } => (left, "\\cdot", right),
            Eq { left, right } => (left, "=", right),
            And { left, right } => (left, "\\land", right),
            Implies { left, right } => (left, "\\implies", right),
            Neg { operand } => {
                return grouped(
                    format!("-{}", self.term(operand, vars, true, formal)),
                    nested,
                );
            }
            Pow { base, exponent } => {
                return grouped(
                    format!("{}^{{{exponent}}}", self.term(base, vars, true, formal)),
                    nested,
                );
            }
            Forall { name, sort, body } => {
                push_name(vars, name);
                let label = vars.last().unwrap().clone();
                let body = self.term(body, vars, false, formal);
                vars.pop();
                return grouped(
                    format!("\\forall {label} \\in {},\\quad {body}", domain(*sort)),
                    nested,
                );
            }
            App { id, args } => {
                let args = args
                    .iter()
                    .map(|arg| self.term(arg, vars, false, formal))
                    .collect::<Vec<_>>();
                return format!(
                    "{}\\left({}\\right)",
                    self.functions[id.as_str()],
                    args.join(", ")
                );
            }
        };
        grouped(
            format!(
                "{} {operator} {}",
                self.term(left, vars, true, formal),
                self.term(right, vars, true, formal)
            ),
            nested,
        )
    }
}

fn grouped(term: String, nested: bool) -> String {
    if nested {
        format!("\\left({term}\\right)")
    } else {
        term
    }
}
