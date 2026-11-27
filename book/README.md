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
| `12-binary-search.md` | User Guide | Declarative clauses, a checked caller, named invariants, bounds, variant and a precondition counterexample |
| `13-production-contract.md` | User Guide | A standard-library function, source binding, mutation and strict verification |
| `14-developer-guide.md` | Developer Guide | A checked interval domain, the tactic protocol and the portable encoding |
| `15-api-reference.md` | Reference | Generated public class, function and method inventory |

## Build it

The chapters use the installed wheel and the installed checker. From a machine
with both on `PATH`:

```bash
scriptorium render book/scriptorium.yaml --only site
scriptorium render book/scriptorium.yaml --only print
```

The site lands in `book/site/` and the PDF in `book/book.pdf`. Finish the
published surface with the custom domain, PDF URL, redirects and validation:

```bash
python tools/publish_book.py
```

The release wheel also carries the same pages and PDF for offline reading. After
rendering and publishing:

```bash
python tools/package_reading.py
python -m logos book --json
```

`tools/package_reading.py` copies `book/site/` and `book/book.pdf` into
`logos/_book/`, which the wheel includes as package data. A single chapter can
be rendered without the project wrapper:

```bash
cd book
scriptorium render chapters/03-conjunction.md --html
```

The chapters are native Scriptorium pages: they use `{run}` and `{run continue}`
blocks, and the two contract lessons use `{export=...}` blocks that write the
real module before the chapter imports it. The generated file is not a copy of
the page: it is the page's own block, written out by the render, so the reader
reads exactly the module the checker binds. `book/examples/` holds those
generated modules; `scriptorium tangle --test` fails if they drift from the
chapters. `freeze: file` caches a chapter's results while its text is unchanged;
CI starts from a clean checkout, so every chapter runs there.

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
application and writes no certificate. The binary search chapter is checked with
a shifted midpoint, a weakened invariant and an unsorted counterexample, and the
production chapter with a mutated bias expression and a source drift after
decoration. The production chapter's copied body is compared with the code
object of `encodings.punycode.adapt` from the interpreter that runs the book.

`tests/test_number_theory.py` checks the domain on its own: every lemma, the
strict certificate for `euclid`, and the exported artifact.

`tests/test_book_reading.py` checks the offline API and the
`python -m logos book` entry point. The `English book` workflow in
`.github/workflows/book.yml` runs those tests, renders both outputs, runs
`tools/publish_book.py`, packages the reading into a final wheel, installs that
wheel in a clean environment, and checks the bundled entry. On `main` it
deploys `book/site/` to GitHub Pages.

## Publication

`book/` is the canonical source for the public site at
<https://logos.uhgia.org/> and for the PDF at
<https://logos.uhgia.org/book.pdf>. The old Quarto pages and their workflow are
gone. `book/redirects.json` maps every old route, and
[`PUBLICATION.md`](PUBLICATION.md) records the route and reference inventory.
The release wheel bundles the same site and PDF under `logos/_book/`, read with
`python -m logos book` or `import logos.book`.

## Editorial map for later stages

The book stops after Euclid's theorem. The next stages, in the order the
material becomes useful:

| Stage | Content | Why it comes here | Status |
|---|---|---|---|
| Arithmetic and induction | Primitive recursion and the factorial | Chapter 9 teaches the mechanism before contracts and algorithms | Drafted |
| Number theory | Divisibility, least divisors, Euclid's theorem | Chapters 7 to 11, with the reusable domain in `logos/domains/number_theory.py` | Drafted |
| Logic puzzles | Finite models, `KnightsKnaves`, guided and automatic search | Shows a domain that searches for a model instead of a proof, and a diagnostic that reports a counterexample | Not drafted |
| Finite graphs | A concrete relation as a table, an order invariant, paths and cycles | Needs a reusable graph domain and a standalone fixture first; see backlog issue #60 | Deferred |
| Contracts | `@logos.function` with named clauses, checked calls, loop invariants, binary search | The engineering half of the project; assumes quantifiers and definitions | Drafted |
| Developer Guide | Kernel terms, portable encoding, the Rust checker, the authoring API | Explains how to extend the checker without weakening it | Drafted |
| Embedding | Serve the built book from the CLI and the API; search over its sections | Needs the site and the PDF to be stable first | Shipped |

The number theory domain (`logos/domains/number_theory.py`) earned its place:
chapters 8 to 11 use its lemmas by name, and the chapter 11 composition matches
the domain's `euclid` proof. The chapters quote the domain source and the tests
compare the quotes with the module, so the reusable copy and the lesson cannot
drift apart.

Open editorial decisions:

- When logic puzzles join the linear guide instead of the Developer Guide.
- Whether the PDF should carry a generated index in addition to the site search.

## Spanish regression fixtures

`vecinos.md` and `euclides.md` are no longer part of the book's navigation.
They remain in the directory as regression fixtures for the `scriptorium tangle`
path: `tests/test_book.py` and `tests/installed_portable.py` still tangle them,
run the generated modules, verify the certificates and exercise their negative
controls. They are not listed in `scriptorium.yaml` and the English chapters do
not link to them.
