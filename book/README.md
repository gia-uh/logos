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

`tests/test_first_proof_chapter.py` renders chapter 2 and checks the compact
verified quote, the failed application and the zero-axiom result.

`tests/test_english_book.py` renders every English chapter from the installed
wheel, requires a traceback-free page, and checks one targeted broken variant per
lesson for the diagnostic it documents. It also checks that `scriptorium.yaml`
lists every chapter in order.

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

The current book stops after reusable lemmas. The next stages, in the order the
material becomes useful:

| Stage | Content | Why it comes here | Status |
|---|---|---|---|
| Arithmetic and induction | A second pass over induction, primitive recursion and the factorial | The Spanish Euclid chapter already proves it; the English book needs the mechanism before contracts | Not drafted |
| Number theory | Least divisors, Euclid's theorem, the infinitude of primes | Reuses `divides` and the lemmas from chapter 6; the Spanish pages are the source material | Not drafted |
| Logic puzzles | Finite models, `KnightsKnaves`, guided and automatic search | Shows a domain that searches for a model instead of a proof, and a diagnostic that reports a counterexample | Not drafted |
| Contracts | Function contracts, branch selection, loop invariants, binary search | The engineering half of the project; assumes quantifiers and definitions | Not drafted |
| Developer Guide | Kernel terms, portable encoding, the Rust checker, the authoring API | Explains how to extend the checker without weakening it | Not drafted |
| Embedding | Serve the built book from the CLI and the API; search over its sections | Needs the site and the PDF to be stable first | Not drafted |

Open editorial decisions:

- Whether a reusable number-theory domain earns its place, or whether the
  lessons should keep spelling out `divides` in each chapter.
- Whether the Spanish `vecinos.md` and `euclides.md` pages move under `book/es/`
  or become translations of the English chapters.
- When the Developer Guide starts: after contracts, or in parallel with the
  number-theory chapters.
- Which pages of the Quarto guide have no replacement and must be migrated
  before the site switches.

## Legacy Spanish pages

The Spanish checked chapters remain at [`vecinos.md`](vecinos.md) and
[`euclides.md`](euclides.md). They are Scriptorium sources with `export=` blocks,
so they are replayed with `scriptorium tangle`:

- `vecinos.md` stops at `common_divisor`, the lemma about two consecutive
  integers, and introduces transparent divisibility, implication introduction,
  existential witnesses and the source-located failure report.
- `euclides.md` reuses that definition and proof, then carries the argument
  through the least prime divisor, factorial positivity, factorial divisibility
  and Euclid's theorem that every integer `n >= 2` has a prime `q > n`.


```bash
cd book
scriptorium tangle vecinos.md
python vecinos.py
logos check --strict vecinos.logos
```

`tests/test_book.py` and `tests/installed_portable.py` keep them working. They
are not part of the English project and are not listed in `scriptorium.yaml`.
