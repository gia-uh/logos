use logos_checker::{Judgment, Proposition, Sort, Verified};
use std::collections::{HashMap, HashSet};
use std::fmt::Write;

pub fn render(checked: &Verified) -> String {
    let judgment = &checked.judgment;
    let math = Math::new(judgment);
    let steps: HashMap<_, _> = checked
        .steps
        .iter()
        .map(|step| (step.id.as_str(), step))
        .collect();
    let names = |context_id: usize| {
        math.scoped_names(
            checked.contexts[context_id]
                .variables
                .iter()
                .map(|var| var.name.as_str()),
        )
    };
    let mut equation = HashMap::new();
    let mut next_number = 1;
    for step in &checked.steps {
        if matches!(step.rule, "block" | "step_ref") && step.conclusion_conversion.is_none() {
            let premise = steps[step.premises[0].as_str()];
            if math.formula(&step.conclusion, &names(step.context_id))
                == math.formula(&premise.conclusion, &names(premise.context_id))
            {
                equation.insert(step.id.as_str(), equation[premise.id.as_str()]);
                continue;
            }
        }
        equation.insert(step.id.as_str(), next_number);
        next_number += 1;
    }
    let number = |id: &str| equation[id];
    let mut out = String::new();
    writeln!(out, "# Checked proof\n").unwrap();
    let verdict = if judgment.status == "policy_denied" {
        "Valid derivation. Strict policy denied it because it uses custom axioms."
    } else {
        "Verified."
    };
    writeln!(out, "{verdict}\n").unwrap();
    writeln!(out, "- Theory: `{}`", judgment.theory).unwrap();
    writeln!(out, "\n## Theorem").unwrap();
    display(&mut out, &math.formula(&judgment.statement, &[]));

    writeln!(out, "## Domains and definitions\n").unwrap();
    writeln!(out, "- $`\\mathbb{{Z}}`$ is the type of mathematical integers. $`\\mathsf{{Prop}}`$ is the type of propositions.").unwrap();
    for symbol in &judgment.declarations {
        writeln!(
            out,
            "- Free symbol $`{} \\in {}`$.",
            math.symbols[symbol.id.as_str()],
            domain(symbol.sort),
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
                "- Transparent definition of $`{label}`$ with result type $`{}`$.",
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
                "- Opaque function $`{call}`$ with result type $`{}`$.",
                domain(function.result)
            )
            .unwrap();
        }
    }
    writeln!(out, "\n## Custom axioms\n").unwrap();
    if judgment.custom_axioms.is_empty() {
        writeln!(out, "Uses zero custom axioms.\n").unwrap();
    }
    let assumptions: HashMap<_, _> = judgment
        .custom_axioms
        .iter()
        .enumerate()
        .map(|(index, axiom)| (axiom.id.as_str(), index + 1))
        .collect();
    for axiom in &judgment.custom_axioms {
        writeln!(out, "**Assumption {}.**", assumptions[axiom.id.as_str()]).unwrap();
        display(&mut out, &math.formula(&axiom.statement, &[]));
    }

    writeln!(out, "## Proof\n").unwrap();
    let mut next_display = 1;
    let mut introduced = HashSet::new();
    for step in &checked.steps {
        let label = number(&step.id);
        if label != next_display {
            continue;
        }
        next_display += 1;
        let vars = names(step.context_id);
        let scope = &checked.contexts[step.context_id];
        let arbitrary: Vec<_> = scope
            .variables
            .iter()
            .zip(&vars)
            .filter(|(var, _)| introduced.insert(var.id.as_str()))
            .map(|(var, name)| format!("$`{name} \\in {}`$", domain(var.sort)))
            .collect();
        if !arbitrary.is_empty() {
            writeln!(out, "Let {} be arbitrary.\n", arbitrary.join(" and ")).unwrap();
        }
        let generalization = step.introduced_variable.as_ref().map(|id| {
            let body = steps[step.premises[0].as_str()];
            let body_scope = &checked.contexts[body.context_id];
            let pos = body_scope
                .variables
                .iter()
                .position(|var| &var.id == id)
                .expect("introduced variable is in the body scope");
            let name = names(body.context_id).swap_remove(pos);
            if introduced.insert(id.as_str()) {
                writeln!(
                    out,
                    "Take $`{name} \\in {}`$ arbitrary.\n",
                    domain(body_scope.variables[pos].sort)
                )
                .unwrap();
            }
            format!("Generalize over the arbitrary variable $`{name}`$.")
        });

        let explanation = match step.rule {
            "local_assumption" => "Assume the following proposition for the implication.",
            "forall_intro" => generalization
                .as_deref()
                .expect("checked universal introduction"),
            "block" | "step_ref" => "Use the earlier derivation.",
            "trans" => "Combine the equalities by transitivity.",
            _ => step.explanation,
        };
        write!(out, "**({label})** {explanation}").unwrap();
        if !step.premises.is_empty() {
            let premises = step
                .premises
                .iter()
                .map(|id| format!("({})", number(id)))
                .collect::<Vec<_>>();
            write!(out, " From {}.", premises.join(" and ")).unwrap();
        }
        if let Some(id) = &step.discharged {
            write!(out, " Discharge the hypothesis ({}) above.", number(id)).unwrap();
        }
        if let Some(provenance) = &step.provenance {
            match provenance.kind {
                "custom_axiom" => write!(
                    out,
                    " Use Assumption {}.",
                    assumptions[provenance.id.as_str()]
                )
                .unwrap(),
                "checked_lemma" => write!(out, " This uses the earlier checked lemma.").unwrap(),
                _ => {}
            }
        }
        writeln!(out).unwrap();
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
                " Substitute $`{}`$ into the law.",
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
        let conclusion = math.formula(&step.conclusion, &vars);
        let calculation = if step.rule == "trans" {
            let first = steps[step.premises[0].as_str()];
            match (&step.conclusion, &first.conclusion) {
                (Proposition::Eq { left, right }, Proposition::Eq { right: middle, .. }) => {
                    let left = math.formula(left, &vars);
                    let middle = math.formula(middle, &vars);
                    let right = math.formula(right, &vars);
                    format!(
                        "\\begin{{aligned}}\n{left} &= {middle} \\\\\n&= {right}\n\\end{{aligned}}"
                    )
                }
                _ => conclusion,
            }
        } else {
            conclusion
        };
        display(&mut out, &calculation);
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
                if has_power(&conversion.left) || has_power(&conversion.right) {
                    writeln!(out, "In the normal form, natural powers use $`a^0 = 1`$ and $`a^{{n+1}} = a^n \\cdot a`$.").unwrap();
                }
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
        "The conclusion follows from ({}){}.",
        number("proof"),
        condition
    )
    .unwrap();
    display(&mut out, &math.formula(&judgment.statement, &[]));
    out
}

fn has_power(expr: &Proposition) -> bool {
    use Proposition::*;
    match expr {
        Pow { .. } => true,
        Add { left, right }
        | Sub { left, right }
        | Mul { left, right }
        | Eq { left, right }
        | And { left, right }
        | Implies { left, right } => has_power(left) || has_power(right),
        Forall { body, .. } | Neg { operand: body } => has_power(body),
        App { args, .. } => args.iter().any(has_power),
        _ => false,
    }
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

// Escape math labels before adding them to Markdown math delimiters.
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

fn push_name(vars: &mut Vec<String>, label: &str, reserved: &[String]) {
    let base = name(label);
    let mut unique = base.clone();
    let mut suffix = 2;
    while vars.contains(&unique) || reserved.contains(&unique) {
        unique = format!("{base}_{{{suffix}}}");
        suffix += 1;
    }
    vars.push(unique);
}

struct Math<'a> {
    symbols: HashMap<&'a str, String>,
    functions: HashMap<&'a str, String>,
    reserved: Vec<String>,
}

impl<'a> Math<'a> {
    fn new(judgment: &'a Judgment) -> Self {
        let mut reserved = Vec::new();
        let mut assign = |label: &str| {
            push_name(&mut reserved, label, &[]);
            reserved.last().unwrap().clone()
        };
        let symbols = judgment
            .declarations
            .iter()
            .map(|item| (item.id.as_str(), assign(&item.name)))
            .collect();
        let functions = judgment
            .functions
            .iter()
            .map(|item| (item.id.as_str(), assign(&item.name)))
            .collect();
        Self {
            symbols,
            functions,
            reserved,
        }
    }

    fn scoped_names<'b>(&self, labels: impl Iterator<Item = &'b str>) -> Vec<String> {
        let mut vars = Vec::new();
        for label in labels {
            push_name(&mut vars, label, &self.reserved);
        }
        vars
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
                push_name(vars, name, &self.reserved);
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
