use crate::{Proposition, Sort};
use serde::Serialize;

#[derive(Clone, Serialize)]
pub struct Variable {
    pub id: String,
    pub name: String,
    pub sort: Sort,
}

#[derive(Serialize)]
pub struct LocalHypothesis {
    pub id: String,
    pub binder: String,
    pub binder_depth: usize,
}

#[derive(Serialize)]
pub struct Context {
    pub id: usize,
    pub variables: Vec<Variable>,
    pub hypotheses: Vec<LocalHypothesis>,
}

#[derive(Serialize)]
pub struct Provenance {
    pub kind: &'static str,
    pub id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_step: Option<String>,
}

#[derive(Serialize)]
pub struct Substitution {
    pub formal: &'static str,
    pub actual: Proposition,
    pub sort: Sort,
}

#[derive(Serialize)]
pub struct LawApplication {
    pub id: String,
    pub formal_statement: Proposition,
    pub substitution: Vec<Substitution>,
}

#[derive(Serialize)]
pub struct Conversion {
    pub explanation: &'static str,
    pub left: Proposition,
    pub right: Proposition,
    pub common_normal_form: Proposition,
}

pub fn rule_explanation(rule: &str, reference: Option<&str>) -> &'static str {
    match rule {
        "local_assumption" => "Assume this proposition for the body of the implication.",
        "hyp_ref" => "Use the indicated active local hypothesis in the current variable scope.",
        "implies_intro" => "Discharge the local hypothesis to conclude the implication.",
        "implies_elim" => "Apply the implication to its checked antecedent.",
        "or_intro_l" => "Introduce the disjunction using its left disjunct.",
        "or_intro_r" => "Introduce the disjunction using its right disjunct.",
        "or_elim" => {
            "Both cases establish the same conclusion, so it follows from the disjunction."
        }
        "not_intro" => {
            "The checked implication derives falsehood from the assumed proposition, establishing its negation."
        }
        "not_elim" => "A proposition and its negation yield falsehood.",
        "ex_falso" => "From falsehood, infer the stated conclusion.",
        "and_intro" => "Conjoin the two checked premises in their given order.",
        "and_elim_l" => "Select the left conjunct of the checked premise.",
        "and_elim_r" => "Select the right conjunct of the checked premise.",
        "axiom_ref" => "Use the declared custom axiom as an assumption.",
        "theorem_ref" => "Use the stated conclusion of the independently checked lemma.",
        "forall_intro" => "Generalize over the fresh arbitrary variable introduced in the body.",
        "forall_elim" => {
            "Substitute the given term for the quantified variable, preserving scope and sort."
        }
        "exists_intro" => "The checked premise establishes the predicate with this witness.",
        "refl" => "An expression equals itself.",
        "symm" => "Reverse the two sides of the premise equality.",
        "trans" => "Compose two equalities whose middle expressions are definitionally equal.",
        "congr" => "Substitute each side of the premise equality into the same typed context.",
        "core_law" => match reference {
            Some("add_assoc") => "Apply associativity of integer addition to regroup the sum.",
            Some("add_comm") => "Apply commutativity of integer addition to swap the two summands.",
            Some("add_zero") => "Apply the additive identity law to remove a zero on the right.",
            Some("add_inverse") => {
                "Apply the additive inverse law to cancel a term against its negation."
            }
            Some("mul_assoc") => {
                "Apply associativity of integer multiplication to regroup the product."
            }
            Some("mul_comm") => {
                "Apply commutativity of integer multiplication to swap the two factors."
            }
            Some("mul_one") => {
                "Apply the multiplicative identity law to remove a factor of one on the right."
            }
            Some("distrib") => "Distribute an integer factor across the two summands.",
            Some("lt_irrefl") => "No integer is strictly less than itself.",
            Some("lt_trans") => {
                "Two strict integer inequalities with a shared middle term compose transitively."
            }
            Some("lt_add") => {
                "Adding the same integer to both sides preserves a strict integer inequality."
            }
            Some("lt_neq") => "A strict integer inequality rules out equality of its two sides.",
            Some("le_refl") => "Every integer is less than or equal to itself.",
            Some("le_trans") => {
                "Two non-strict integer inequalities with a shared middle term compose transitively."
            }
            Some("le_antisymm") => "Two opposite non-strict integer inequalities force equality.",
            Some("le_lt_trans") => "A non-strict inequality followed by a strict one is strict.",
            Some("lt_le_trans") => "A strict inequality followed by a non-strict one is strict.",
            Some("le_total") => "Any two integers are ordered one way or the other.",
            Some("lt_trichotomy") => {
                "Two integers are ordered, equal, or ordered in the opposite direction."
            }
            Some("lt_to_le") => {
                "A strict integer inequality implies the corresponding non-strict one."
            }
            Some("lt_succ_le") => {
                "A strict integer inequality implies the successor of the left side is at most the right side."
            }
            Some("lt_add_one_le") => "An integer below a successor is at most the predecessor.",
            Some("le_add") => {
                "Adding the same integer to both sides preserves a non-strict integer inequality."
            }
            Some("not_lt_le") => {
                "If one integer is not less than another, the second is at most the first."
            }
            Some("eq_symm") => "Integer equality is symmetric.",
            Some("half_lower") => {
                "Floor half of an interval with non-negative lower bound stays above the lower bound."
            }
            Some("half_upper") => {
                "Floor half of a non-empty interval stays strictly below the upper bound."
            }
            Some("length_nonneg") => "A finite sequence has non-negative length.",
            Some("sorted_elim") => "Sortedness gives the order of any two in-range elements.",
            Some("sorted_lower") => {
                "An element at or below a smaller in-range element is also smaller than the target."
            }
            Some("sorted_upper") => {
                "An element at or above a larger in-range element also exceeds the target."
            }
            Some("sorted_gap") => {
                "A sorted sequence with a target below every left element and above every right element has no occurrence of the target."
            }
            _ => unreachable!("checked core law"),
        },
        "linear" => {
            "A non-negative rational combination of the indicated inequality hypotheses and the negated conclusion is contradictory."
        }
        "have" => {
            "The checked intermediate proposition is available under its binder while checking the body."
        }
        "program_ref" => {
            "The executable program satisfies its checked precondition, loop invariants and postcondition."
        }
        "block" => "Take the selected conclusion from the block of shared steps.",
        "step_ref" => "Reuse the indicated earlier checked step in this block.",
        _ => unreachable!("checked rule"),
    }
}
