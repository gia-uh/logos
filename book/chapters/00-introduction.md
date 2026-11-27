---
theme: book
title: Introduction
stem: introduction
---

Logos is a Python library for writing mathematical arguments that another program can check. This book is the guided path from the first checked proof through number theory to Euclid's theorem. The same canonical source renders as this site and as [a single PDF](book.pdf) for offline reading.

# Introduction

Logos is a Python library for writing mathematical arguments that another program can check. You state a theorem as a Python function, build evidence for it with a small set of operations, and hand that evidence to an independent Rust executable. The executable either accepts the exact derivation or reports the first step it cannot justify.

This book teaches the library by using it. Every Python block runs when the book is built, against the installed package and the installed checker. If a claim in the prose stops being true, the build fails.

## Two programs, two jobs

A proof has a producer and a judge.

The producer is Python: your proof function, a tactic from `logos.tactics`, a search procedure, or a language model that proposes a derivation. The producer is allowed to be clever, incomplete, randomized or wrong. It is not trusted.

The judge is the `logos` executable, built from `checker/`. It owns a fixed set of inference rules. For each rule it reads the rule name and its typed arguments, recomputes the conclusion, and compares that conclusion with the next step of the derivation. It never runs your Python. It never accepts a step because the producer called it `obvious`.

This separation is the central design choice. A model can propose a proof, but only the checker produces a verdict. The model in your head is not the certificate either: the certificate is the artifact the checker read.

## What the trusted checker owns

The trusted part is deliberately small:

- The proof terms in `logos.kernel`: reflexivity, transitivity, substitution, implication introduction and elimination, conjunction and disjunction rules, universal and existential rules, induction, and a few arithmetic and order laws.
- The portable encoding of a statement, its declarations, its evidence and its optional commentary.
- The Rust checker that replays the evidence and recomputes every conclusion.

The Python authoring layer is not trusted. It chooses useful terms, gives them readable names and produces diagnostics. A bug in that layer can make a proof fail or a message confusing; it cannot make the checker accept an invalid step, because the checker does not consult it.

Some rules are cited by name rather than rebuilt in Python. `p.order("lt_irrefl", a)` cites the checker-owned law that no integer is less than itself. `p.ring(...)` produces an explicit polynomial certificate. `p.linear(...)` produces an exact rational Farkas certificate. In each case the checker parses the certificate and recomputes the result.

## What a receipt is

After a successful check, a theorem has a **receipt**. The receipt contains the exact bytes of the artifact and their SHA-256 digest. The artifact contains the statement, its declarations, the evidence and any authored commentary.

`theorem.inspect()` does not rebuild the argument in Python. It sends the receipt's bytes to the `logos` executable and returns the checker's Markdown reading. If the receipt is missing or the evidence has changed, `inspect()` raises an error instead of showing a stale reading.

A reading reports the checked statement, the derivation, the authored commentary and whether the derivation used any **custom axioms**. A custom axiom is an assumption an author declares with `@logos.axiom`. A proof with zero custom axioms depends only on the checker's rules and on the definitions in the artifact. That is the strongest claim this book makes, and the reading states it explicitly.

## Scope

The current checker covers:

- propositional connectives: conjunction `&`, disjunction `|`, negation `~`, implication `>>`;
- equality, integer arithmetic, and the strict and non-strict order on integers;
- transparent definitions, whose bodies the checker unfolds during conversion;
- primitive recursion on the natural numbers;
- universal and existential quantification over integers;
- contracts for ordinary Python functions and for loops.

It does not cover sets, real analysis, quotient types, general recursive functions, or a guarantee that a proof search will succeed. A failed search leaves the conjecture open; it does not prove the negation. Chapter 4 makes that distinction precise with a checked counterexample.

## How to read a lesson

The Quick Start installs both programs and checks one theorem. Chapter 1 then explains that theorem line by line.

The User Guide chapters follow the order in which the operations become necessary:

1. conjunction and named intermediate facts;
2. case splits, contradiction and counterexamples;
3. universal and existential quantifiers with scoped witnesses;
4. transparent definitions and reusable lemmas.

Each lesson states its prerequisites and outcomes before the first block, and includes a diagnostic that shows what a specific mistake looks like and an exit exercise that uses only the operations introduced so far. Later chapters assume the earlier ones.

The chapters are not a reference manual. They teach the mechanism: which evidence a step produces, why the checker accepts it, and what the Python name does and does not mean. The generated [Public API Reference](public-api-reference.html) collects the public names, and the checker's `--help` describes the portable commands.

## Conventions

In the prose, $P$, $Q$ and $R$ are propositions, and $a$, $b$, $c$ and $d$ are integers. In Python, `P`, `Q` and `R` are `Prop` values, which Logos represents as symbolic propositions, and `a`, `b`, `c` and `d` are `Int` values.

The Python operator `>>` is implication, `&` is conjunction, `|` is disjunction and `~` is negation. They build symbolic expressions; they do not evaluate to Python booleans. Parentheses matter because Python's precedence is not mathematical precedence. When a nested implication is hard to read, build it with `logos.chain(...)` instead of a chain of `>>`.

Every proof function receives a context named `p`. The context records the current goal, the local hypotheses and the evidence already built. Operations such as `p.assume`, `p.apply` and `p.and_intro` return a **fact**: a proposition together with checked evidence for it. A fact is not a string and not a Python boolean. It is the thing the next step consumes.
