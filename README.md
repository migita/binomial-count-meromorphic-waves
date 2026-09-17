# A binomial count of meromorphic travelling waves

Alexander Migita

This repository holds the arXiv source package of the paper and a Lean 4
formalisation of two of its theorems.

## Layout

- `paper/`: the arXiv package. Sources are `main.tex`, `authors.tex`,
  `references.bib`, `main.bbl` and `sections/`;
  the ancillary material in `anc/` contains the exact verification script,
  the Singular calculation for order five, the continuous-convolution
  rigidity certificate through degree 72 with its replay script, and the
  exact checks for the purely dispersive and purely dissipative subfamilies.
  `MANIFEST.sha256` lists the package files; `main.pdf` is the compiled paper.
- `certificates/`: the exact computations that make all pairs distinct at the composite
  indices 15 (`p = 8`, finite field and Hensel lifting) and 21 (`p = 11`, archived 19-adic
  certificate with its validation record); see `certificates/README.md`.
- `lean/`: a Lean 4 project pinned to Mathlib v4.33.1. It proves

  - continuous-convolution rigidity `(R_d)` when `2d+1` is prime
    (`PolynomialRigidity.rigidity_prime_index`);
  - the prime-index enumeration theorem: for `2p-1` prime, the normalised
    one-pole rational-exponential pairs are finite, number
    `(2p-1).choose (p-1)`, and are all simple, both for the coefficient
    matching system (`primeIndexCountAndSimplicity`) and for the direct
    rational-function ODE formulation
    (`primeIndexRationalExponentialCountAndSimplicity`), together with the
    correspondence between the two formulations for every order.

  The all-order counting and simplicity statement is stated as a
  proposition and remains a conjecture. See `lean/README.md`,
  `lean/ENUMERATION.md` and `lean/ENUMERATION_PROGRESS.md`.

## Checking

Paper, from `paper/`:

```sh
sha256sum -c MANIFEST.sha256
tectonic main.tex        # or pdflatex + bibtex + pdflatex twice
python3 anc/verify_manuscript.py
python3 anc/rigidity/verify_coverage.py
```

Lean, from `lean/`, with Elan installed:

```sh
lake exe cache get
lake build
lake env lean EnumerationCheck.lean
lake env lean Check.lean
```

The check files verify that the proofs have exactly the stated propositions
as their types and that the theorems depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

The paper's final section, "Tool and computational resource disclosure",
names the AI systems used in the work and their roles. The Lean
formalisation in `lean/` was produced by gpt-6-astra (OpenAI) in dialogue
with the author on 14 September 2026 and was checked independently with
Claude Code (Anthropic): statement audit against the manuscript, rebuild
from source, and axiom audit.
