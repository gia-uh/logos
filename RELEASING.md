# Releasing Logos

A release has two artifacts with one version:

| Artifact | Name | Built from | Installed by |
|---|---|---|---|
| Python distribution | `logos-ai` (import `logos`) | `pyproject.toml` | `pip install logos-ai` |
| Standalone checker | crate `logos-checker`, binary `logos` | `checker/Cargo.toml` | `cargo install --path checker` |

Both versions in `pyproject.toml` and `checker/Cargo.toml` must match the tag.
The portable format and the theory are versioned separately (`logos-proof-v1`,
`logos-core-v1`); a compatible checker keeps replaying old certificates.

## Supported targets

- Python 3.12 or newer. The wheel is `py3-none-any`. CPython 3.12, 3.13 and
  3.14 run the same proofs and produce the same artifact digest.
- Linux and macOS for the checker and the book build. The checker is a Rust
  binary built from source; this release publishes no prebuilt executable.
  Windows is not tested and not claimed.
- Rust 1.85 or newer, required by `edition = "2024"`.
- Rendered PDF and site need Pango, Fontconfig and Poppler on the build host.

## What the owner provides

These cannot be done by an agent without the account:

1. A PyPI account with 2FA and a project-scoped API token for `logos-ai`.
   The name returned 404 on the public JSON API before the first release, so it
   was unclaimed when checked; only the account holder can reserve it.
2. A TestPyPI token, if the release is rehearsed there first.
3. The tag and GitHub Release, if the release carries one.
4. The decision to publish the crate to crates.io. This release does not: the
   checker is installed from source, and `logos-checker` was unclaimed when
   checked.

No token, key or password belongs in the repository or in a commit.

## Build the artifacts

Run from a clean checkout of the commit to release, with the checker on `PATH`.

The order matters. `tools/package_reading.py` copies the rendered book into
`logos/_book/`; a wheel built before it installs but has no offline reading.

```bash
# 1. The checker that the book executes.
cargo install --locked --path checker --root "$PWD/.release/portable"
export PATH="$PWD/.release/portable/bin:$PATH"
logos --version

# 2. A clean environment with the package and the book toolchain.
python3.12 -m venv .release/author
.release/author/bin/python -m pip install -e . pytest
.release/author/bin/python -m pip install \
  "scriptorium[pdf] @ git+https://github.com/gia-uh/scriptorium@9325898877e714b4f12f12c4e88650ab65c4fe09"

# 3. Render the book, finish the site, and package the reading.
scriptorium render book/scriptorium.yaml --only site
scriptorium render book/scriptorium.yaml --only print
python tools/publish_book.py
python tools/package_reading.py

# 4. Build both artifacts from the same tree.
uv build --out-dir .release/dist
```

CI runs the same steps in `.github/workflows/book.yml` and
`.github/workflows/portable-proof.yml`. Use CI for the heavy render when the
local host is short on memory or disk.

## Gates

Run these before the artifacts are called release candidates.

```bash
# Metadata and the license travel with both artifacts.
uvx twine check .release/dist/*          # must print PASSED, with no WARNING

# Versions agree across the two manifests and the tag.
python - <<'PY'
import pathlib, re, tomllib
py = tomllib.loads(pathlib.Path("pyproject.toml").read_text())["project"]["version"]
cargo = re.search(r'^version = "([^"]+)"', pathlib.Path("checker/Cargo.toml").read_text(), re.M).group(1)
assert py == cargo, (py, cargo)
print("version", py)
PY

# The wheel and sdist carry the offline book, not only the code.
python - <<'PY'
import tarfile, zipfile
wheel = next(__import__("pathlib").Path(".release/dist").glob("*.whl"))
sdist = next(__import__("pathlib").Path(".release/dist").glob("*.tar.gz"))
names = zipfile.ZipFile(wheel).namelist()
for needed in ("logos/_book/manifest.json", "logos/_book/book.pdf", "logos/_book/site/index.html"):
    assert needed in names, needed
print("wheel files", len(names))
with tarfile.open(sdist) as t:
    tn = t.getnames()
assert any(n.endswith("/LICENSE") for n in tn), "LICENSE missing from sdist"
print("sdist files", len(tn))
PY

# The checker's own suite and formatting.
cargo fmt --manifest-path checker/Cargo.toml --check
cargo test --locked --manifest-path checker/Cargo.toml

# The Python suite, with the checker on PATH.
python -m pytest -q
```

Record the SHA-256 of both artifacts:

```bash
sha256sum .release/dist/*
```

## Verify as a recipient

Install from the artifacts, outside the checkout, and use them.

```bash
python3.12 -m venv /tmp/logos-reader
/tmp/logos-reader/bin/python -m pip install .release/dist/*.whl
cd /tmp
/tmp/logos-reader/bin/python -m logos book --json     # bundled site and PDF
logos example primes
logos check --strict primes.logos                     # exit 0, zero custom axioms
logos inspect --markdown --strict primes.logos > primes.md
```

A strict check of a certificate that uses a custom axiom must exit 3 and name
the axiom. A tampered certificate must exit 1. A wheel without `logos/_book`
is not a release candidate.

## Publish

Only the owner runs these steps.

```bash
# Tag the released commit on the release branch head.
git tag -a v0.1.0 -m "Logos 0.1.0"
git push origin v0.1.0

# Upload the exact artifacts that passed the gates.
uvx twine upload .release/dist/*

# Optional GitHub Release with the CHANGELOG section for this version.
gh release create v0.1.0 --notes-file release-notes.md .release/dist/*
```

Publish the wheel and the sdist from the same build. Do not rebuild between the
gate run and the upload.

## Checklist

- [ ] Release branch created from `origin/main` and green in CI.
- [ ] `pyproject.toml` and `checker/Cargo.toml` carry the release version.
- [ ] `CHANGELOG.md` has a dated section for the version.
- [ ] Checker installed from the same commit; `logos --version` matches.
- [ ] Book rendered, site published, reading packaged into `logos/_book`.
- [ ] Both artifacts built after packaging, hashes recorded.
- [ ] `twine check` passes without warnings.
- [ ] Rust suite and Python suite green on the release commit.
- [ ] Clean install outside the checkout reads the book and strict-checks a
      certificate offline.
- [ ] Owner has the PyPI token, the tag decision and the crates.io decision.
