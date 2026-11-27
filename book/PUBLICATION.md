# Publication map

`book/` is the one canonical source. It renders the site at
<https://logos.uhgia.org/>, the PDF at <https://logos.uhgia.org/book.pdf>, and
the offline copy that ships under `logos/_book/` in the wheel. The old Quarto
project and its publish workflow no longer build or deploy.

## Owning files

| File | Purpose |
|---|---|
| `book/scriptorium.yaml` | Site and PDF outputs, public URL and chapter order |
| `book/CNAME` | GitHub Pages custom domain |
| `book/redirects.json` | Old Quarto URLs and their new destinations |
| `tools/publish_book.py` | Adds CNAME, PDF, redirects, robots and validates targets |
| `tools/package_reading.py` | Copies the site and PDF into `logos/_book/` for the wheel |
| `tools/check_installed_reading.py` | Checks the offline entry from an installed wheel |

## Old routes

Every old Quarto page has a redirect with the same path, and a page removed from
the book keeps a redirect from its published URL. A redirect preserves a known
deep link through the `anchors` map in `book/redirects.json`; an unknown fragment
is carried to the new page rather than dropped.

| Old route | New destination |
|---|---|
| `/` | `/` |
| `/guide/expressions.html` | `/introduction.html#conventions` |
| `/guide/propositions.html` | `/writing-your-first-proof.html#state-what-you-intend-to-prove` |
| `/guide/defining.html` | `/definitions-that-unfold-lemmas-you-can-name.html` |
| `/guide/theorems.html` | `/writing-your-first-proof.html#check-the-proof` |
| `/guide/tactics/index.html` | `/extend-the-checked-language-with-a-domain.html#a-tactic-returns-evidence-not-trust` |
| `/guide/tactics/structural.html` | `/facts-that-hold-together.html` |
| `/guide/tactics/arithmetic.html` | `/even-odd-and-what-divides-means.html#a-divisor-is-a-quotient-you-can-name` |
| `/guide/tactics/rewrite.html` | `/definitions-that-unfold-lemmas-you-can-name.html#a-definition-is-a-body-the-checker-can-unfold` |
| `/guide/tactics/combinators.html` | `/extend-the-checked-language-with-a-domain.html#a-tactic-returns-evidence-not-trust` |
| `/guide/tactics/custom.html` | `/extend-the-checked-language-with-a-domain.html#a-tactic-returns-evidence-not-trust` |
| `/guide/examples/index.html` | `/` |
| `/guide/examples/number-theory.html` | `/even-odd-and-what-divides-means.html` |
| `/guide/examples/infinitely-many-primes.html` | `/one-more-prime-always.html` |
| `/guide/examples/knights-knaves.html` | `/extend-the-checked-language-with-a-domain.html` |
| `/guide/examples/data-structures.html` | `/a-contract-on-code-that-ships.html` |
| `/a-finite-graph-you-can-audit.html` | `/binary-search-all-the-way-down.html` |
| `/reference/api.html` | `/public-api-reference.html` |

## Reference content

The old reference material was split between the Quarto API page and the tactic
pages. The generated `Public API Reference` chapter documents public imports and call contracts. The lessons supply complete proofs
that use those operations.

| Old content | New home |
|---|---|
| Top-level `logos` functions, `@logos.theorem`, `check`, `prove`, `define`, `extern`, `cases` | `Public API Reference` |
| `logos.expr` classes and operator tables | `Public API Reference#expressions`; expression conventions in `Introduction#conventions` |
| Structural, arithmetic, rewriting and combinator tactics | The lessons that use them, plus the Developer Guide's tactic protocol |
| Kernel proof terms and helpers | `Public API Reference#tactic-extensions` |
| Exceptions | `Public API Reference#logoslogosprooferror` |
| Number theory examples | `Even, Odd, and What Divides Means` through `One More Prime, Always` |
| Infinitely many primes | `One More Prime, Always` |
| Knights and Knaves | `Extend the Checked Language with a Domain`, which teaches the domain and tactic protocol; the runnable example remains in the checker's `logos example knights-knaves` |
| Data structures and contracts | `A Contract on Code That Ships` |
| Quarto navigation | Replaced by the Scriptorium sidebar, search index, outline and previous/next links |

## Build and verify

```bash
scriptorium render book/scriptorium.yaml --only site
scriptorium render book/scriptorium.yaml --only print
python tools/publish_book.py
python tools/package_reading.py
```

`tools/publish_book.py` fails when a redirect points at a page or section the
render did not produce, when the PDF is missing, or when the homepage stops
linking the PDF. The English book workflow runs it before deploying. The final
wheel is installed in a clean directory and checked with
`tools/check_installed_reading.py`, which requires the reading to come from
`site-packages`, not from a checkout.
