# Polynomial rigidity in Lean

Both requested prime-index enumeration and simplicity theorems are proved in
[`Enumeration/PrimeEnumeration.lean`](PolynomialRigidity/Enumeration/PrimeEnumeration.lean):

```lean
theorem primeIndexCountAndSimplicity : PrimeIndexCountAndSimplicity
theorem primeIndexRationalExponentialCountAndSimplicity :
  PrimeIndexRationalExponentialCountAndSimplicity
```

These declarations are in `PolynomialRigidity.Enumeration`. For every `p ≥ 2`
with `2*p-1` prime, they prove finiteness, the exact count
`(2*p-1).choose (p-1)`, and simplicity of every solution. The matching and
simplicity correspondences with the direct rational-function ODE are also
proved for every `p ≥ 2`. The original statement definitions are unchanged.
See [`ENUMERATION.md`](ENUMERATION.md) for the precise objects counted and
[`ENUMERATION_PROGRESS.md`](ENUMERATION_PROGRESS.md) for the proof map.

This project formalises the continuous polynomial convolution

\[
H_A(x)=\sum_{i,j=0}^{d}a_i a_j\frac{i!j!}{(i+j+1)!}x^{i+j+1},
\qquad A(x)=\sum_{i=0}^{d}a_i x^i.
\]

It proves the following theorem for **every** natural number `p ≥ 2` for which
`2*p - 1` is prime:

> If `A ∈ ℂ[X]` is nonzero, `deg A = p - 1`, and `A ∣ H_A`, then
> `A = A.leadingCoeff * X^(p - 1)`.

For monic `A`, the conclusion is `A = X^(p - 1)`.

The main declarations are:

| Declaration | Meaning |
| --- | --- |
| `convolution A` | The polynomial `H_A`, defined by the displayed coefficient formula. |
| `Rigidity K` | The full rigidity statement as a proposition; no all-degree proof is asserted. |
| `RigidityAtDegree K d` | The manuscript's monic statement `(R_d)`. |
| `rigidity_prime_index` | `(R_(p-1))` over `ℂ` when `p ≥ 2` and `2*p - 1` is prime. |
| `polynomial_rigidity_prime_index` | The explicit theorem above for arbitrary nonzero complex polynomials. |
| `eq_monomial_of_prime` | The same result over any algebraically closed field of characteristic zero, indexed by `2*deg A + 1`. |

These continuous-rigidity declarations are in the namespace `PolynomialRigidity`.
The general statement is formalised as a definition; the proved scope is the
prime-index case requested here.

## Check the proof

Lean and mathlib are pinned to **v4.33.1**. The exact dependency revisions are
recorded in `lake-manifest.json`.

From this directory, with Elan installed:

```sh
~/.elan/bin/lake exe cache get
~/.elan/bin/lake build
~/.elan/bin/lake env lean EnumerationCheck.lean
~/.elan/bin/lake env lean Check.lean
```

The cache download is only needed on a fresh checkout. `lake build` checks
the entire proof. `EnumerationCheck.lean` checks both prime enumeration proof
types against the original propositions and audits them and the correspondence
theorems. `Check.lean` checks continuous-rigidity applications at `p = 2, 3, 51`.
The public theorems depend only on Lean's standard axioms `propext`,
`Classical.choice`, and `Quot.sound`. The audits fail if any additional axiom,
including a proof placeholder, appears.

All three checks pass. The proof contains no `sorry`, `admit`, added axioms, or
`native_decide`. Automatic implicit parameters are disabled for the project.

## Proof and correspondence with the manuscript

The source statement is equation `(R_d)` in
[`sections/counting.tex`](../arxiv_meromorphic_waves/sections/counting.tex).
The proof formalises the prime reduction used in Step 3 of the prime-index
theorem and the zero-gap case of
[`anc/rigidity/proof.tex`](../arxiv_meromorphic_waves/anc/rigidity/proof.tex).

1. Put `ℓ = 2*d + 1`. Construct a valuation of the coefficient field with
   `v(ℓ) < 1`, using a valuation subring dominating the integer subring at `ℓ`.
   Mathlib's existence theorem applies directly to fields containing
   transcendental coefficients as well.
2. In the residue field, every factorial `n!` with `n < ℓ` is nonzero. Hence
   `v(n!) = 1`. For the leading term, cancellation gives
   `ℓ * beta d d = (d!)²/(2*d)!`, a valuation unit.
3. For a monic polynomial whose coefficients have valuation at most one,
   the leading summand of `ℓ*H_A(1)` has valuation one and every other summand
   has valuation strictly less than one. The nonarchimedean triangle property
   therefore implies `H_A(1) ≠ 0`.
4. If a solution has a nonzero root, choose a root `r` of maximal valuation.
   Scaling the roots by `r⁻¹` makes all roots, and consequently all coefficients,
   integral. The scaled polynomial has root `1`. Divisibility and the proved
   convolution scaling identity give `H(1) = 0`, contradicting step 3.
5. Thus every root is zero. Factorisation gives `A = X^d` in the monic case;
   scaling the leading coefficient gives the general statement.

Using a valuation directly on the coefficient field replaces the manuscript's
preliminary reduction to algebraic coordinates. The maximal-root normalisation
also avoids choosing a ramified extension for weighted coefficient scaling.

The convolution is formalised algebraically, exactly as in the source's
coefficient formula. The separate discrete-convolution enumeration proof uses
prime reduction, injectivity, Hensel lifting of every residue label, and the
proved ODE correspondence. The unrestricted composite-index assertions remain
conjectures.

## Files

- [`PolynomialRigidity/Convolution.lean`](PolynomialRigidity/Convolution.lean):
  definitions and scaling identities.
- [`PolynomialRigidity/Valuation.lean`](PolynomialRigidity/Valuation.lean):
  existence of the valuation, factorial units, and integral normalisation.
- [`PolynomialRigidity/Prime.lean`](PolynomialRigidity/Prime.lean):
  the surviving-term argument and the rigidity theorems.
- [`Check.lean`](Check.lean): public examples and axiom audit.
- [`PolynomialRigidity/EnumerationStatement.lean`](PolynomialRigidity/EnumerationStatement.lean):
  count and simplicity propositions, with explicit correspondence obligations.
- [`PolynomialRigidity/Enumeration/PrimeEnumeration.lean`](PolynomialRigidity/Enumeration/PrimeEnumeration.lean):
  proofs of both original prime count and simplicity propositions.
- [`PolynomialRigidity/Enumeration/PrimeLowerBound.lean`](PolynomialRigidity/Enumeration/PrimeLowerBound.lean):
  lifting all labels and transferring the resulting finite family to complex solutions.
- [`PolynomialRigidity/Enumeration/Correspondence.lean`](PolynomialRigidity/Enumeration/Correspondence.lean)
  and [`SimplicityCorrespondence.lean`](PolynomialRigidity/Enumeration/SimplicityCorrespondence.lean):
  the matching bijection and the equivalence of simplicity conditions.
- [`EnumerationCheck.lean`](EnumerationCheck.lean): exact proof-type checks and transitive axiom audits.
