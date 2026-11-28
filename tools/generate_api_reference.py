"""Render Chapter 15 and the separate Rift inventory from Python source.

Run without arguments to check freshness, or with --write to update both.
The generator uses ASTs so it can run before Logos and its checker are installed.
"""
from __future__ import annotations

import argparse
import ast
import re
from functools import cache
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / "logos"
CHAPTER = ROOT / "book/chapters/15-api-reference.md"
INVENTORY = ROOT / "book/maintenance/api-inventory.md"
FRONT = Path(__file__).with_name("api_reference.md")

ROOT_GROUPS = (
    ("Expressions", "Int Prop Expr Var Lit Forall Exists Implies var vars lit forall exists chain "
                    "format_expr Seq seq_var length nth sorted absent occurrence",
     "quick-start.html"),
    ("Theorems and evidence", "theorem axiom prove check Theorem Axiom ProofReceipt "
                              "LogosProofError export_proof",
     "writing-your-first-proof.html"),
    ("Definitions", "define definition recursor extern cases if_",
     "definitions-that-unfold-lemmas-you-can-name.html"),
    ("Program contracts", "contract Contract "
                                 "LogosContractError program_contract ProgramContract function "
                                 "FunctionDeclaration Clause",
     "binary-search-all-the-way-down.html"),
)
METHODS = {
    "Theorem": "proof check inspect receipt certified",
    "FunctionDeclaration": "check inspect export receipt certified clauses",
    "ProofContext": "note assume obtain apply and_intro exists subst refl symm trans not_elim "
                    "ex_falso not_lt_of_lt order linear recursor_base recursor_step rewrite least "
                    "fix negate cases contradict induction ring witness",
    "Fact": "left right",
    "Goal": "with_hyp with_statement",
    "FiniteTransitionSystem": "export_safety verify_safety replay_violation",
}
EXTENSIONS = {
    "logos.authoring": "ProofContext Fact",
    "logos.goal": "Goal",
    "logos.kernel": "ProofTerm",
    "logos.runner": "TacticFailed TacticResult",
}

# Use focused contracts where a source docstring is absent, describes internals,
# or needs book-specific failure modes and links.
CONTRACTS = {
    "Var": "Construct a symbolic variable. Its identity distinguishes it from other variables with the same name.",
    "Lit": "Construct a symbolic literal from a Python value. Use integers or Booleans for portable proofs.",
    "Exists": "Bind one symbolic variable in the supplied predicate expression. Nest calls for multiple variables.",
    "Implies": "Build the symbolic implication from its antecedent and consequent, as with `A >> B`.",
    "Seq": "The sort marker for a sequence of integers in program contracts.",
    "seq_var": "Create a fresh symbolic variable of sequence sort.",
    "length": "Build the symbolic length of a sequence.",
    "nth": "Build a symbolic zero-based element access. Program proofs must establish both index bounds.",
    "cases": "Build a piecewise symbolic expression from condition/value pairs and a default value.",
    "if_": "Build a symbolic conditional expression from a condition and its two possible values.",
    "function": "Decorate an ordinary Python function that uses the supported program fragment. Return the same callable with `requires`, `ensures`, `invariant` and `decreases` clause decorators and bound `check()`, `inspect()`, `export(path)` and `clauses()` methods. Unsupported source raises `LogosContractError`.",
    "program_contract": "Build a loop contract with precondition, postcondition, invariant and decreasing integer variant.",
    "ProgramContract": "The precondition, postcondition, invariant and variant returned by `program_contract`.",
    "FunctionDeclaration.check": "Translate and verify the decorated function and return the original callable with a current certificate. Invalid source or proof obligations fail verification.",
    "FunctionDeclaration.inspect": "Return checker-rendered Markdown for the current certificate. Requires current verification.",
    "FunctionDeclaration.export": "Write the current portable artifact to `path` and return its receipt. Requires current verification.",
    "FunctionDeclaration.receipt": "The current checker receipt, or `None` before verification or after a change invalidates it.",
    "FunctionDeclaration.certified": "Whether the declaration has a current checker receipt.",
    "FunctionDeclaration.clauses": "Return a tuple of authored contract clauses in clause-kind order.",
    "ProofContext.assume": "Introduce the antecedent of the current implication as a local fact and leave the consequent as the goal. The supplied proposition must match the antecedent.",
    "ProofContext.and_intro": "Combine two facts for A and B into a fact for A & B.",
    "ProofContext.refl": "Return a fact proving the expression equal to itself.",
    "ProofContext.symm": "Reverse an equality fact. Other fact shapes fail.",
    "ProofContext.trans": "Compose two equality facts at their matching middle expression. Non-equalities and mismatched middle expressions fail.",
    "ProofContext.not_elim": "From facts for ¬P and P, return a fact for falsehood. The operands must match.",
    "ProofContext.ex_falso": "Use a fact for falsehood to obtain a fact for the current goal. Requires an open goal.",
    "ProofContext.recursor_base": "Return the defining equality of the indicated recursor at zero.",
    "ProofContext.recursor_step": "Return the defining equality at the successor of the supplied argument. Supply a fact establishing that the argument is nonnegative.",
    "assumption": "Return a tactic that closes a goal with a matching local hypothesis, or fails if none matches.",
    "contradiction": "Return a tactic that closes a goal using a contradiction derivable from its local hypotheses. Fails if it cannot find one.",
    "exact": "Return a tactic that supplies the given proof term for checker validation against the current goal.",
    "intro": "Return a tactic that opens one universal binder, implication, or negation per supplied name. Continue with the body or consequent, or with falsehood for a negation. Unsupported goal shapes fail.",
    "left": "Return a tactic that chooses the left side of a disjunction and leaves that side as a goal. Pass the right proposition as `right_type`.",
    "right": "Return a tactic that chooses the right side of a disjunction and leaves that side as a goal. Pass the left proposition as `left_type`.",
    "split": "Return a tactic for A & B that opens A and B as subgoals in that order. Other goal shapes fail.",
    "refl": "Return a tactic that closes an equality with structurally identical sides. Other goal shapes fail.",
    "Goal.with_hyp": "Return a new goal with the same conclusion and an added or replaced named hypothesis.",
    "Goal.with_statement": "Return a new goal with the same hypotheses and the supplied conclusion.",
    "TacticFailed": "Signal that a tactic cannot handle its current goal. The proof runner reports the failure, and tactic alternatives can catch it.",
    "Int": "Alias for Python `int`, the integer sort in portable statements.",
    "Prop": "Alias for Python `bool`, the proposition sort in portable statements.",
    "var": "Return a fresh symbolic variable of the supplied type. Reuse the returned object to refer to the same symbol.",
    "vars": "Split whitespace-separated names and return one fresh symbolic variable per name.",
    "lit": "Lift a Python value into a symbolic literal. Use an integer or Boolean for portable proofs.",
    "forall": "Pass one sort per parameter followed by a callable that returns a symbolic predicate. Return the universally quantified expression. A noncallable predicate argument is rejected.",
    "exists": "Pass a sort and a unary callable returning a symbolic predicate. Return an existential expression. The callable is evaluated on a fresh symbolic variable.",
    "chain": "Build a right-associated implication from one or more propositions. `chain(A, B, C)` builds `A >> (B >> C)`. An empty chain has no conclusion and raises `IndexError`.",
    "prove": "With an expression and explicit tactics, return an anonymous proof for `check` to certify. With a `Theorem`, run bounded automatic search using `hints`, `depth` and `timeout` and return the certified theorem or raise `LogosProofError`.",
    "check": "Run the proof and certify its evidence with the Rust checker. Return the theorem, anonymous proof, or checked Python function. Missing proofs, unclosed goals and rejected evidence raise `LogosProofError`.",
    "Theorem.proof": "Attach tactics as positional arguments or as a list, and return the theorem. As a decorator, accept a zero-argument tactic-producing function or a proof function whose first argument is `p`, followed by the quantified theorem parameters. Replacing the proof clears its receipt.",
    "Theorem.receipt": "The current `ProofReceipt`, or `None` before certification or after the proof changes.",
    "Theorem.certified": "Whether the theorem has a current checker receipt.",
    "ProofContext": "The `p` argument supplied to a proof function by `@theorem_name.proof`. Its goal and available facts change as you introduce assumptions and enter scopes.",
    "Fact": "Evidence for a symbolic proposition in a proof context. Read `statement` for the proposition; obtain facts from context operations.",
    "ProofContext.exists": "Given ∃x. P(x), a value, and a `Fact` proving P(value), return a `Fact` for the existential without closing the current goal. A Python literal is lifted. A non-existential target reports `exists_goal`, and an out-of-scope value reports `witness_escape`. Mismatched evidence reports `evidence_mismatch`. See the [complete examples](#complete-existential-examples).",
    "ProofContext.witness": "For the current goal ∃x. P(x), supply a value and evidence for P(value), then return the resulting proof term. A Python literal is lifted. Diagnostics include `witness_goal` for the wrong goal shape, `witness_escape` for an out-of-scope value, and `witness_mismatch` for a fact that proves the wrong predicate. See the [complete examples](#complete-existential-examples).",
    "ProofContext.obtain": "Open a fact of shape ∃x. P(x), returning a fresh local variable and a fact for its instantiated predicate. The symbol is scoped to the elimination: it cannot appear free in the conclusion.",
    "ProofContext.induction": "Use integer induction from `lower` on the goal's variable. Prove the goal at the lower bound in `ind.base()`, and prove it at the successor from the induction hypothesis in `ind.step()`. Supply an appropriate lower-bound fact when it is not already available. See [the factorial proof](induction-that-builds-a-factorial.html).",
    "ProofContext.fix": "Enter a universal goal with `with p.fix(name) as scope`. Use the fresh symbol `scope.variable` and call `scope.finish(evidence)` inside the block. Read `scope.result` afterward. Other goal shapes fail.",
    "ProofContext.negate": "Enter a negation goal with its operand as a local assumption. Derive a contradiction inside the block.",
    "ProofContext.cases": "Split a disjunction fact into two branches. Prove the same conclusion with the left alternative in one branch and the right in the other.",
    "ProofContext.contradict": "Enter a branch with the given proposition assumed and derive falsehood to discharge that assumption.",
    "ProofContext.ring": "Return a fact for an integer polynomial equality, optionally using equality facts. If normalization cannot establish the identity, the proof step fails.",
    "witness": "Return a tactic for an existential goal ∃x. P(x). Pass a symbolic value such as `lit(5)`. The tactic opens one subgoal P(value) with the same hypotheses; the next tactic supplies its evidence. Other goal shapes raise `TacticFailed` with `witness: expected Exists`. The checker validates the witness sort and evidence. See the [complete examples](#complete-existential-examples).",
    "decide": "Test a closed Boolean proposition as a tactic. False or unsupported propositions fail. A successful test returns legacy evidence that does not certify the proposition under Rust replay. For portable integer inequalities use `ProofContext.linear`.",
    "linarith": "Search for a linear arithmetic consequence of local hypotheses. Unsupported goals or failed searches raise `TacticFailed`. The legacy evidence returned on success does not certify the inequality under Rust replay. Use `ProofContext.linear` for portable certificates.",
    "ring": "Return a tactic that closes integer polynomial equalities such as `a*m + b*m == (a+b)*m`. A non-equality or distinct polynomial normal forms fail. See [the complete divisibility proof](what-divides-two-neighbours.html) for the corresponding proof-context operation.",
    "Theorem.inspect": "Return checker-rendered Markdown for a currently certified proof. A missing or stale receipt raises `LogosProofError`.",
    "Goal": "Construct a tactic input containing `context` (named hypotheses) and `statement` (the conclusion to prove).",
    "TacticResult": "A closing `ProofTerm` or a pair of subgoals and a function composing their proofs into evidence for the original goal.",
    "ProofTerm": "Base type for evidence returned by tactics and checked by the verifier.",
    "Fact.left": "Project the left conjunct from a conjunction fact.",
    "Fact.right": "Project the right conjunct from a conjunction fact.",
}


@cache
def parse(module):
    path = PACKAGE.joinpath(*module.split(".")[1:])
    path = path / "__init__.py" if path.is_dir() else path.with_suffix(".py")
    return ast.parse(path.read_text(encoding="utf-8"))


@cache
def definitions(module):
    return {node.name: (module, node) for node in parse(module).body
            if isinstance(node, (ast.FunctionDef, ast.ClassDef))}


@cache
def source_entries(module):
    entries = definitions(module)
    for node in parse(module).body:
        if isinstance(node, ast.ImportFrom):
            for item in node.names:
                entries[item.asname or item.name] = (node.module, item.name)
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    entries[target.id] = (module, node)
    return entries


def resolve(module, name):
    origin, node = source_entries(module)[name]
    return resolve(origin, node) if isinstance(node, str) else (origin, node)


def member(module, node, name):
    for child in node.body:
        if isinstance(child, ast.FunctionDef) and child.name == name:
            return child
    for base in node.bases:
        if isinstance(base, ast.Name) and base.id in definitions(module):
            return member(module, definitions(module)[base.id][1], name)
    raise ValueError(f"{module}.{node.name} has no member {name}")


# Only these record classes are constructed directly by readers. The other
# dataclasses in the index are returned by proof or contract operations.
RECORD_CONSTRUCTORS = {"Var", "Lit", "Implies", "Goal"}


def signature(name, node, *, bound=False):
    if isinstance(node, ast.ClassDef):
        constructor = next((item for item in node.body
                            if isinstance(item, ast.FunctionDef) and item.name == "__init__"), None)
        # Some classes have generated dataclass constructors or are handles
        # returned by another operation. List their type rather than inventing a call.
        if constructor:
            return signature(name, constructor, bound=True)
        if name in RECORD_CONSTRUCTORS:
            fields = [ast.unparse(field) for field in node.body
                      if isinstance(field, ast.AnnAssign)]
            return f"{name}({', '.join(fields)})"
        return name
    if not isinstance(node, ast.FunctionDef) or is_property(node):
        return name
    arguments = node.args
    text = ast.unparse(arguments)
    if bound:
        receiver = arguments.posonlyargs + arguments.args
        text = text.removeprefix(receiver[0].arg).removeprefix(", ")
    result = f"{name}({text})"
    if node.returns:
        result += f" -> {ast.unparse(node.returns)}"
    return result


def is_property(node):
    return any(isinstance(item, ast.Name) and item.id == "property"
               for item in node.decorator_list)


def doc_summary(node):
    if not isinstance(node, (ast.FunctionDef, ast.ClassDef)):
        return ""
    paragraphs = (ast.get_docstring(node) or "").split("\n\n")
    summary = " ".join(paragraphs[0].split())
    # Source docstrings use reStructuredText inline literals.
    return summary.replace("``", "`")


def render_entry(module, name, node, *, owner=None, origin=None):
    label = f"{owner}.{name}" if owner else f"{module}.{name}"
    purpose = CONTRACTS.get(f"{owner}.{name}" if owner else name) or doc_summary(node)
    if not purpose:
        raise ValueError(f"Missing API description for {label}")
    call = signature(name, node, bound=owner is not None)
    # Scriptorium folds case when turning headings into fragment IDs.
    heading = label
    if module == "logos" and owner is None and name in {
        "Var", "Lit", "Forall", "Exists", "Theorem", "Axiom", "Contract",
    }:
        heading += " constructor"
    lines = [f"### {heading}\n\n"]
    if owner:
        lines.append(f"`{call}` on `{owner}`.\n\n")
    else:
        lines.append(f"Import with `from {module} import {name}`.\n\n")
        if call != name:
            lines.append(f"`{call}`\n\n")
    lines.append(purpose + "\n\n")
    for method in METHODS.get(name, "").split() if owner is None else ():
        child = member(origin or module, node, method)
        lines.extend(render_entry(module, method, child, owner=name))
    return lines


def render():
    lines = [FRONT.read_text(encoding="utf-8")]
    for title, names, link in ROOT_GROUPS:
        lines.append(f"## {title}\n\n[Complete checked example]({link})\n\n")
        for name in names.split():
            origin, node = resolve("logos", name)
            lines.extend(render_entry("logos", name, node, origin=origin))
    lines.append("## Proof context\n\n"
                 "[Complete checked proof functions](witnesses-and-their-scope.html). "
                 "For context managers, use the methods on the object they yield.\n\n")
    for name in EXTENSIONS["logos.authoring"].split():
        lines.extend(render_entry("logos.authoring", name, definitions("logos.authoring")[name][1]))
    lines.append("## Tactics\n\n"
                 "A tactic receives a `Goal` and returns evidence or subgoals with a "
                 "function to compose their evidence. Supply tactics in order to the "
                 "runner. A failed step raises `TacticFailed` and a sequence with "
                 "unclosed goals fails certification. See the [complete examples]"
                 "(#complete-existential-examples).\n\n")
    for name in sorted(source_entries("logos.tactics")):
        _, node = resolve("logos.tactics", name)
        lines.extend(render_entry("logos.tactics", name, node))
    lines.append("## Tactic extensions\n\n"
                 "[Complete custom tactic](extend-the-checked-language-with-a-domain.html).\n\n")
    for module, names in EXTENSIONS.items():
        if module == "logos.authoring":
            continue
        for name in names.split():
            _, node = resolve(module, name)
            lines.extend(render_entry(module, name, node))
    lines.append("## Finite transition systems\n\n"
                 "[Complete checked lock model](can-two-clients-hold-the-lock.html).\n\n")
    module = "logos.domains.transition_systems"
    name = "FiniteTransitionSystem"
    _, node = resolve(module, name)
    lines.extend(render_entry(module, name, node))
    return "".join(lines).rstrip() + "\n"


def inventory():
    """Keep the broader, syntactic Rift coverage off the public page."""
    blocks = ["# Maintainer source inventory\n\n"
              "Generated by `tools/generate_api_reference.py`. Includes implementation "
              "names for Rift coverage. See Chapter 15 for supported imports.\n"]
    pattern = re.compile(r"^class ([A-Za-z]\w*)|^def ([a-z]\w*)|^    def ([a-z]\w*)\((?:self|cls)\b",
                         re.MULTILINE)
    for path in sorted(PACKAGE.rglob("*.py")):
        matches = [next(name for name in match.groups() if name)
                   for match in pattern.finditer(path.read_text(encoding="utf-8"))]
        if matches:
            names = ", ".join(f"`{name}`" for name in dict.fromkeys(matches))
            blocks.append(f"\n- `{path.relative_to(ROOT)}` — {names}\n")
    return "".join(blocks)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="write the generated files")
    options = parser.parse_args()
    stale = []
    for path, content in ((CHAPTER, render()), (INVENTORY, inventory())):
        if options.write:
            path.write_text(content, encoding="utf-8")
        elif not path.exists() or path.read_text(encoding="utf-8") != content:
            stale.append(str(path.relative_to(ROOT)))
    if stale:
        print(f"Stale: {', '.join(stale)}. Run {Path(__file__).name} --write.")
        return 1
    print("2 reference files " + ("written" if options.write else "match the source"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
