---
theme: book
title: Introduction
stem: introduction
---

Logos is a Python library for writing mathematical arguments that an independent checker can verify. This book starts with a small proof and builds toward number theory and program contracts. It is also available as [a single PDF](book.pdf).

# Introduction

Suppose your assumptions are $P$ and $P \Rightarrow Q$, and your goal is $Q$. On paper you apply the implication to $P$. In Logos you propose that same step, pointing to where you got each premise. The checker confirms that both premises are available and computes the conclusion $Q$. If you claim that this application yields $R$, the checker rejects the step because the implication concludes $Q$.

## Two programs, two jobs

Python produces the derivation. You can write the steps yourself, call a tactic, or ask a search procedure or language model to propose them. If search stops without a derivation, you still have an open question. Unsuccessful search leaves both the claim and its negation unproved by that search.

The independent Rust checker reads the proposed derivation. It recomputes what each rule concludes from its inputs and checks that the final conclusion matches the stated theorem. Your Python runs when producing evidence. The checker runs separately on the resulting artifact.

## What the trusted checker owns

The trusted checker implements a fixed set of rules for logic and arithmetic. Applying an implication is one of those rules. The artifact records the theorem, its declarations, and the steps proposed as evidence. The Rust checker reads that portable record and checks the derivation. Names, comments and tactics in Python help you produce or explain it.

## What a receipt is

After acceptance, Logos stores a receipt with the exact artifact bytes and their SHA-256 digest. You can inspect the receipt to ask the checker to recheck those saved bytes and explain the accepted derivation. Here is how to read three parts of a result for the argument above, summarized in words.

- **Statement.** For any propositions $P$ and $Q$, if $P$ holds and $P \Rightarrow Q$ holds, then $Q$ follows.
- **Evidence.** Introduce each premise as a local hypothesis, apply the implication, and account for those hypotheses in the conditional conclusion.
- **Axiom status.** Zero custom axioms. The two local hypotheses appear as premises of the statement. A custom axiom is a separate, author-declared assumption on which a derivation may rely.

## Scope

The checker covers propositional logic, equality, integer arithmetic and order, transparent definitions, primitive recursion on the natural numbers, integer quantifiers, and contracts for supported Python functions and loops. Sets, real analysis, quotient types and general recursion are outside this scope. The chapter on cases shows how a checked counterexample can settle a question that unsuccessful proof search leaves open.

## Conventions

In Python, a Logos proposition is a symbolic expression. For example, `P >> Q` builds an implication from symbolic propositions. Python does not evaluate it to a Boolean truth value. Build and check a theorem in the [Quick Start](quick-start.html). For lookup, use the [Public API Reference](public-api-reference.html) or the checker’s `--help`.

## Exit exercise

Classify each report. What, if anything, has been established?

1. With premises $P$ and $P \Rightarrow Q$, a producer applies the implication and claims $R$.
2. A search for a proof of $R$ runs out of time. Has it established $\neg R$?
3. The checker accepts a derivation and reports one custom axiom.

## Answers

1. The proposed application is invalid. The implication yields $Q$.
2. The search found no proof before it stopped. The status of $R$ is still open on that evidence.
3. The checker verified the derivation using the declared custom axiom as an assumption.
