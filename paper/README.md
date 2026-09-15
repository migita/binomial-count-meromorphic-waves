# A binomial count of meromorphic travelling waves

English manuscript: **A binomial count of meromorphic travelling waves**.

The readable manuscript is [main.pdf](main.pdf). Its editable sources are
main.tex, authors.tex, references.bib, and sections/. The three figures are
vector PDFs in figures/.

The author is Alexander Migita. A Tool and computational resource
disclosure section at the end of the paper names all AI systems used and
their roles. This package has not been submitted to arXiv.

A Lean 4 formalization of the prime-index rigidity and enumeration
theorems (Remark 4.5 and Appendix A of the paper) is available at
https://github.com/migita/binomial-count-meromorphic-waves in the
directory lean/.

## Mathematical scope

The paper's main results are the two enumeration formulas below.
Its analytic foundation is a uniform proof of meromorphic completeness for
odd-order operators and for even operator polynomials, using Eremenko's theorem
and, in the second case, a fixed energy level. The odd-order statement is
attributed to Yuan--Li--Qi and related work; the energy device is attributed
to Eremenko--Liao--Ng and its subsequent applications.
The paper gives the rational, rational-exponential and elliptic coefficient
systems.

The enumeration counts normalized complex operator--profile pairs as the monic
operator varies over its full coefficient family. It covers both:

- rational-exponential pairs at unit rate, with left endpoint zero:
  N_p = binomial(2p-1,p-1);
- elliptic pairs on a fixed nonsingular lattice, retaining its scale, the
  marked pole and the constant background:
  M_p = 2 binomial(2p-2,p-2).

Neither count requires odd p or an even polynomial P. Those hypotheses are
used only for global meromorphic completeness.
Continuous-convolution rigidity gives both lengths with multiplicities
through p=73. When 2p-1 is prime, all rational-exponential pairs are simple;
the elliptic pairs are simple on a nonempty open set of lattices.
The separate exact p=5 calculation gives 126 simple rational-exponential
points and, by the nodal transfer theorem, 112 generically simple elliptic
points. General simplicity is not asserted throughout the degree-73 range.
At p=7 the two counts are 1716 and 1584.
Their difference N_p-M_p is the Catalan number C_{p-1}.

In every order, a fixed monic operator admits at most one normalized
rational-exponential one-pole profile. Thus a count of distinct
rational-exponential pairs also counts distinct operators. This injectivity
statement does not require the rigidity conjecture.

There are three worked examples, each treating both sectors:

| Family | Rational-exponential | Generic fixed-lattice elliptic |
| --- | ---: | ---: |
| KdV--Burgers, full p=2 family | 3 | 2 |
| Kuramoto--Sivashinsky, full p=3 family | 10 | 8 |
| Kawahara, even p=4 family | 3 | 6 |

The KS calculation determines all exceptional nonsingular lattices:
j=-300 gives six distinct points with multiplicities 2,2,1,1,1,1;
j=0 gives two points of multiplicity four each.
The Kawahara count is for the even coefficient restriction; the unrestricted
p=4 counts are 35 and 30.
The profiles and parameter relations are linked explicitly to the earlier
literature. The KS ten-pair list recovers the tables of Kudryashov--Zargaryan
(1996) and Conte--Musette (2009), with both signs of dispersion retained.
The Kawahara parameter choices and meromorphic completeness are attributed
to Demina--Kudryashov (2010) and the subsequent literature.
Kudryashov--Migita is cited for context rather than treated as a fourth
worked example.

The all-degree rigidity and simplicity conjectures remain open. The manuscript
does not reproduce the older draft's unsupported claim of complete simplicity
at order eleven. Mixed even operators, Fisher and the Darboux test datum are
confined to the open-questions discussion.

## Build the manuscript

The source uses standard LaTeX packages and the supplied main.bbl.
With a conventional TeX installation:

    pdflatex main.tex
    bibtex main
    pdflatex main.tex
    pdflatex main.tex

Alternatively:

    tectonic --keep-logs --keep-intermediates main.tex

Build the ancillary proof from its own directory:

    cd anc/rigidity
    pdflatex proof.tex
    pdflatex proof.tex

The source archive contains all manuscript inputs, figures and ancillary
checks. It omits build logs, review images and the generated main PDF.

## Exact checks

Use Python 3.9 or later (Python 3.11 was used for the exact checks). SymPy is the
only dependency for the two verification commands:

    python anc/verify_manuscript.py
    python anc/rigidity/verify_coverage.py

The first reconstructs the convolutions and checks the three displayed
examples, the exact correspondence with the two classical KS tables,
the KS collision multiplicities, the Kawahara literature
normalization, the physical scaling, energy identities, Fisher identity and
mixed fourth-order test datum. It reconstructs the elliptic operator
elimination, its weights and the nodal coefficient change at orders 2--4,
and the complete order-five Singular input.
It also checks the leading-coefficient comparison in the injectivity proof
for polynomial degrees one through four; the proof itself applies in every
degree.
The uniform counting and deformation proofs are in the manuscript.

The second checks the original integer certificate identities, every residual
degree, the prime certificates and all 72 degree choices. It independently
checks 132,348 original ordered convolution coefficients. The reduction proof
is [anc/rigidity/proof.pdf](anc/rigidity/proof.pdf), with source proof.tex.

For the full order-five count, install Singular and run:

    Singular -q anc/p5_count.sing

The expected output is:

    DIMENSION
    0
    LENGTH
    126
    ALL_SIMPLE
    1

The saved output is anc/p5_count.txt. This calculation was executed afresh
when preparing the manuscript.

## Figures

The figure program uses the formulas checked above:

    python -m pip install -r anc/requirements.txt
    python anc/make_figures.py

The listed versions were used in preparing the figures. Figure evaluations
are illustrations of exact formulas, not evidence for enumeration or
dynamical stability.

## Verification record

The source archive includes MANIFEST.sha256. After extraction, verify it with:

    sha256sum -c MANIFEST.sha256

The files anc/verification.json and anc/rigidity/verification.json record the
mathematical check results and their scope.
The local preparation directory additionally contains a PDF review and a
reference audit; these working files are not part of the arXiv source bundle.
