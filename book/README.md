# The Logos book

This directory is the English Scriptorium project for Logos. It is the canonical
book: the Introduction, the Quick Start and the User Guide chapters are one
source that renders to a web site and a PDF, and every Python block runs against
the installed package and the Rust checker when the book is built.

The project is [`scriptorium.yaml`](scriptorium.yaml). The chapters are under
[`chapters/`](chapters/):

| File | Part | Topic |
|---|---|---|
| `00-introduction.md` | Introduction | Scope, the trusted checker, producer versus judge |
| `01-quick-start.md` | Quick Start | Clean install, `PATH`, one checked theorem |
| `02-first-proof.md` | User Guide | Implication, `p.assume`, `p.apply`, `inspect()` |
| `03-conjunction.md` | User Guide | Projections, `p.and_intro`, named facts |
| `04-cases.md` | User Guide | `p.cases`, contradiction, a checked counterexample |
| `05-witnesses.md` | User Guide | `p.obtain`, `p.witness`, `p.fix`, scope |
| `06-definitions.md` | User Guide | Transparent definitions and reusable lemmas |
| `07-parity.md` | User Guide | Even and odd, witnesses, the divisibility lemmas |
| `08-neighbours.md` | User Guide | Consecutive divisors, negation, cases |
| `09-factorial.md` | User Guide | Primitive recursion, induction, factorial divisibility |
| `10-least-prime.md` | User Guide | A negated definition, `p.least`, the least prime divisor |
| `11-euclid.md` | User Guide | Euclid's theorem composed from named lemmas |
| `12-finite-graph.md` | User Guide | A finite graph as a table, an order invariant, paths and cycles |
| `13-binary-search.md` | User Guide | Total correctness, bounds, variant, duplicates and a precondition counterexample |
| `14-production-contract.md` | User Guide | A standard-library function, source binding, mutation and strict verification |

## Build it

The chapters use the installed wheel and the installed checker. From a machine
with both on `PATH`:

```bash
scriptorium render book/scriptorium.yaml --only site
scriptorium render book/scriptorium.yaml --only print
```

The site lands in `book/site/` and the PDF in `book/book.pdf`. A single chapter
can be rendered without the project wrapper:

```bash
cd book
scriptorium render chapters/03-conjunction.md --html
```

The chapters are native Scriptorium pages: they use `{run}` and `{run continue}`
blocks and need no `scriptorium tangle` step. `freeze: file` caches a chapter's
results while its text is unchanged; CI starts from a clean checkout, so every
chapter runs there.

## What the tests check

`tests/test_first_proof_chapter.py` renders chapter 2 and checks the whole
`compose.inspect()` reading in one `::: proof` panel: title, theory, both
docstrings, checked statement, domains, zero custom axioms, steps 1–14 in order,
the note between steps 7 and 8, and the conclusion. It checks the scoped
`h3`/`h4` headings, that no proof heading enters the TOC, that the same Markdown
renders the same standalone and embedded, the failed application, and the PDF
text when WeasyPrint is installed.

`tests/test_english_book.py` renders every English chapter from the installed
wheel, requires a traceback-free page, and checks one targeted broken variant per
lesson for the diagnostic it documents. It also checks that `scriptorium.yaml`
lists every chapter in order, that every quoted number theory snippet matches
`logos/domains/number_theory.py`, and that the Euclid certificate verifies with
`--strict` while the altered `n! + 1` line fails at the consecutive-divisor
application and writes no certificate. The finite graph chapter is checked with
a descending edge, the binary search chapter with a shifted midpoint, a weakened
invariant and an unsorted counterexample, and the production chapter with a
mutated bias expression and a source drift after decoration. The production
chapter's copied body is compared with the code object of
`encodings.punycode.adapt` from the interpreter that runs the book.

`tests/test_number_theory.py` checks the domain on its own: every lemma, the
strict certificate for `euclid`, and the exported artifact.

The `English book` workflow in `.github/workflows/book.yml` runs those tests and
renders both outputs on a pull request. It uploads the site as an artifact and
does not deploy it.

## The live site

The Quarto site in `docs-site/` and its GitHub Pages deployment are unchanged.
They keep publishing while this book is reviewed. The replacement happens in a
separate change: compare the rendered book with the live guide, move any page
that still has unique material, and only then point Pages at `book/site/`.
Until that change lands, `docs-site/` is the public site and this book is the
candidate.

## Editorial map for later stages

The book stops after Euclid's theorem. The next stages, in the order the
material becomes useful:

| Stage | Content | Why it comes here | Status |
|---|---|---|---|
| Arithmetic and induction | Primitive recursion and the factorial | Chapter 9 teaches the mechanism before contracts and finite structures | Drafted |
| Number theory | Divisibility, least divisors, Euclid's theorem | Chapters 7 to 11, with the reusable domain in `logos/domains/number_theory.py` | Drafted |
| Logic puzzles | Finite models, `KnightsKnaves`, guided and automatic search | Shows a domain that searches for a model instead of a proof, and a diagnostic that reports a counterexample | Not drafted |
| Contracts | Function contracts, branch selection, loop invariants, binary search | The engineering half of the project; assumes quantifiers and definitions | Not drafted |
| Developer Guide | Kernel terms, portable encoding, the Rust checker, the authoring API | Explains how to extend the checker without weakening it | Not drafted |
| Embedding | Serve the built book from the CLI and the API; search over its sections | Needs the site and the PDF to be stable first | Not drafted |

The number theory domain (`logos/domains/number_theory.py`) earned its place:
chapters 8 to 11 use its lemmas by name, and the chapter 11 composition matches
the domain's `euclid` proof. The chapters quote the domain source and the tests
compare the quotes with the module, so the reusable copy and the lesson cannot
drift apart.

Open editorial decisions:

- When the Developer Guide starts: after contracts, or in parallel with the
  remaining User Guide material.
- Which pages of the Quarto guide have no replacement and must be migrated
  before the site switches.

## Spanish regression fixtures

`vecinos.md` and `euclides.md` are no longer part of the book's navigation.
They remain in the directory as regression fixtures for the `scriptorium tangle`
path: `tests/test_book.py` and `tests/installed_portable.py` still tangle them,
run the generated modules, verify the certificates and exercise their negative
controls. They are not listed in `scriptorium.yaml` and the English chapters do
not link to them.
