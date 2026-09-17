# A binomial count of meromorphic travelling waves

English manuscript: **A binomial count of meromorphic travelling waves**.

The readable manuscript is [main.pdf](main.pdf). Its editable sources are
main.tex, authors.tex, references.bib, and sections/.

The author is Alexander Migita. A Tool and computational resource
disclosure section at the end of the paper names all AI systems used and
their roles. This package has not been submitted to arXiv.

A Lean 4 formalization of the prime-index rigidity and enumeration
theorems (Remark 5.5 and Appendix A of the paper) is available at
https://github.com/migita/binomial-count-meromorphic-waves in the
directory lean/.

## Mathematical scope

The paper studies meromorphic travelling waves of
u_t + u u_x + sum_j b_j d_x^(j+1) u = 0, whose profiles satisfy
P(D)v + v^2/2 = 0 with P monic of degree p.

**Classification.** For evolution equations of even order (p odd) and for
purely dispersive equations (only odd-order derivatives, P even), every
nonconstant meromorphic travelling wave is rational, rational in an
exponential, or elliptic, with one pole per period. The odd-order statement is
attributed to Yuan--Li--Qi and related work; the energy device is attributed to
Eremenko--Liao--Ng and its subsequent applications. The purely dispersive case
is the one in which the profile equation is invariant under z -> -z.

**The count.** Normalized complex operator--profile pairs are counted as the
monic operator varies over its full coefficient family:

- rational-exponential pairs at unit rate, with the limit at e^z -> 0 equal to
  zero: N_p = binomial(2p-1,p-1);
- elliptic pairs on a fixed nonsingular lattice, retaining its scale, the
  marked pole and both backgrounds: M_p = 2 binomial(2p-2,p-2).

Neither count requires the hypotheses of the classification.
Continuous-convolution rigidity gives both counts with multiplicities through
p=73. When 2p-1 is prime, all rational-exponential pairs are simple, and the
elliptic pairs are simple on a nonempty open set of lattices. The separate
exact p=5 calculation gives 126 simple rational-exponential points and, by the
nodal transfer theorem, 112 generically simple elliptic points. General
simplicity is not asserted throughout the degree-73 range.

**The two pure subfamilies.** The reflection z -> -z acts on the pairs. Its
fixed points are the pairs of the purely dispersive equations (p even) and of
the purely dissipative equations (only even-order derivatives in the linear
part, p odd). Their number is F_p = binomial(p-1, floor((p-1)/2)), under the same
hypotheses as for N_p; the purely dispersive equations also account for 2 F_p of
the elliptic pairs. Purely dispersive equations carry only pulses. Purely
dissipative equations carry only fronts; this is proved when all pairs are
distinct, and for real waves in every order.

**A single equation.** Rescaling x moves the coefficient vector of an equation
along a weighted curve. An equation has a one-pole travelling wave rational in
an exponential exactly when its coefficient vector lies on one of at most
(N_p + F_p)/2 such curves. For odd p >= 5 (with rigidity), the equations that
have any nonconstant meromorphic travelling wave form a set of dimension at
most two in the (p-1)-dimensional coefficient space; at p=3 it is the union of
the four classical Kuramoto--Sivashinsky curves.

In every order, a fixed monic operator admits at most one normalized
rational-exponential one-pole profile, so a count of distinct pairs also
counts distinct operators. This does not require the rigidity conjecture.

The examples are chosen to show the counts at work:

| p | N_p | M_p | pure subfamily of this order | F_p | 2 F_p |
| --- | ---: | ---: | --- | ---: | ---: |
| 2 | 3 | 2 | dispersive (KdV) | 1 | 2 |
| 3 | 10 | 8 | dissipative (KS without dispersion) | 2 | -- |
| 4 | 35 | 30 | dispersive (Kawahara) | 3 | 6 |
| 5 | 126 | 112 | dissipative (Nikolaevskiy) | 6 | -- |
| 6 | 462 | 420 | dispersive (seventh-order KdV) | 10 | 20 |

Orders two and three are worked out by hand for the full family. The KS
calculation determines all exceptional nonsingular lattices: j=-300 gives six
distinct points with multiplicities 2,2,1,1,1,1, and j=0 gives two points of
multiplicity four each; it is the paper's illustration of multiplicity.
The profiles and parameter relations are linked explicitly to the earlier
literature. The KS ten-pair list recovers the tables of Kudryashov--Zargaryan
(1996) and Conte--Musette (2009), whose six cases are the orbits of the
reflection. The Kawahara parameter choices and classification are attributed to
Demina--Kudryashov (2010) and the subsequent literature. At p=6 the ten purely
dispersive pairs are listed, two of them real. At p=5 the six purely
dissipative pairs are listed; the four real ones are the kink solutions of
Kudryashov--Migita (2007).

The all-degree rigidity and simplicity conjectures remain open. Mixed equations
of odd order and the Fisher example are confined to the open-questions
discussion.

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

The source archive contains all manuscript inputs and ancillary
checks. It omits build logs, review images and the generated main PDF.

## Exact checks

Use Python 3.9 or later (Python 3.11 was used for the exact checks). SymPy is the
only dependency for the two verification commands:

    python anc/verify_manuscript.py
    python anc/rigidity/verify_coverage.py

The first reconstructs the convolutions and checks the order-two, order-three
and order-four examples, the exact correspondence with the two classical KS tables,
the KS collision multiplicities, the Kawahara literature
normalization, the physical scaling, energy identities, Fisher identity and
mixed fourth-order test datum. It reconstructs the elliptic operator
elimination, its weights and the nodal coefficient change at orders 2--4,
and the complete order-five Singular input.
It also checks the leading-coefficient comparison in the injectivity proof
for polynomial degrees one through four; the proof itself applies in every
degree.
A few of its checks concern formulas of an earlier version of the manuscript
that are no longer displayed (the cnoidal and Jacobi forms, the operator
D^4+a_0, the mixed fourth-order test datum); they are kept because they are
harmless and exact.
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

The checks for the two pure subfamilies and for single equations are in
anc/symmetry_checks/ (SymPy only; see the README there):

    python anc/symmetry_checks/reflection_checks.py
    python anc/symmetry_checks/symmetric_count.py 2 3 4 5 6 7 8
    python anc/symmetry_checks/elliptic_symmetric.py
    python anc/symmetry_checks/p6_list.py

The saved outputs are the .txt files next to the scripts.

## Verification record

The source archive includes MANIFEST.sha256. After extraction, verify it with:

    sha256sum -c MANIFEST.sha256

The files anc/verification.json and anc/rigidity/verification.json record the
mathematical check results and their scope.
The local preparation directory additionally contains a PDF review and a
reference audit; these working files are not part of the arXiv source bundle.
