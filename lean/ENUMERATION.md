# Enumeration and simplicity: proved prime-index case

[`PolynomialRigidity/EnumerationStatement.lean`](PolynomialRigidity/EnumerationStatement.lean)
defines the original requested propositions without any changes to their scope.
Both prime-index propositions now have proofs in
[`Enumeration/PrimeEnumeration.lean`](PolynomialRigidity/Enumeration/PrimeEnumeration.lean).
The correspondence with the direct rational ODE, including the equivalence
of the two simplicity conditions, is proved for every `p ≥ 2`.
See [`ENUMERATION_PROGRESS.md`](ENUMERATION_PROGRESS.md) for the proof map.
There are no placeholder proofs or new axioms; the transitive audits report
only `propext`, `Classical.choice`, and `Quot.sound`.
Everything is in the namespace `PolynomialRigidity.Enumeration`.

The source is the current manuscript's
[`sections/counting.tex`](../arxiv_meromorphic_waves/sections/counting.tex),
using its monic-operator normalisation. The direct infinitesimal formulation
also follows the counting and simplicity
[`formulation note`](../codex_one_pole_count_simplicity_formulation_20260909.md).

## Objects counted

The direct definition `NormalizedODEPairs p` consists of pairs
`(P, R) ∈ ℂ[ρ] × ℂ(t)` satisfying:

- `P` is monic and has degree exactly `p`.
- The **reduced**, monic denominator of `R` is exactly `(t+1)^p`.
- Its numerator has degree at most `p` and vanishes at `t=0`.
- With `δ = t d/dt`, the rational-function identity
  `P(δ)R + R²/2 = 0` holds.

Thus `v(z) = R(exp z)` has the prescribed single pole at `exp z = -1`,
of exact order `p`, finite values at the two cylinder ends, and value zero
at the selected end. The exponential rate is one. Both the operator and
profile vary; reflection-related pairs are counted separately.

`exponentialDerivative` is defined explicitly by the quotient rule on the
canonical reduced numerator and denominator. The ODE is an identity in
the rational function field. An analytic realisation theorem is not proved
in this file.

The direct statement at order `p` is:

```lean
def RationalExponentialCountAndSimplicityAtOrder (p : ℕ) : Prop :=
  Finite (NormalizedODEPairs p) ∧
  Nat.card (NormalizedODEPairs p) = expectedCount p ∧
  ∀ s : NormalizedODEPairs p, IsSimpleODEPair p s.val
```

Here `expectedCount p = (2*p - 1).choose (p - 1)`. Finiteness is asserted
as part of the conclusion, so no finite-solution assumption is hidden in
the use of a cardinality function.

## Meaning of simplicity

For the direct pair `(P,R)`, perturb the monic operator by `hP`, of degree
strictly less than `p`. Perturb the numerator by `hN`, of degree at most
`p` and with `hN(0)=0`, giving `hV = hN/(t+1)^p`.

`IsSimpleODEPair p (P,R)` states:

\[
 P(\delta)hV+hP(\delta)R+RhV=0
 \quad\Longrightarrow\quad hP=hN=0.
\]

This is absence of infinitesimal deformations in the normalised matching
problem. The pole position and exponential rate are fixed throughout.

## The manuscript's coefficient equations

The independent algebraic formulation uses

\[
 A(\rho)=\rho^{p-1}+a_1\rho^{p-2}+\cdots+a_{p-1}.
\]

`Coefficients p = Fin (p-1) → ℂ`; index `j` represents `a_(j+1)`.
The universal coefficients lie in `MvPolynomial (Fin (p-1)) ℂ`.
`universalRemainder p` is the remainder of `A ⋆ A` on monic division by
`A`. Its coefficients `r=0,...,p-2` are `remainderEquation p r`.

The discrete convolution is given by a finite Bernoulli-polynomial
formula, exactly as in the manuscript's verification script:

\[
 \operatorname{powerSum}_m(x)=
 \frac{B_{m+1}(x)-B_{m+1}(0)}{m+1}-\mathbf1_{m=0},
\]

\[
 X^i\star X^j=
 \sum_{k=0}^j(-1)^k\binom jk X^{j-k}
 \operatorname{powerSum}_{i+k}(X).
\]

The endpoint correction is necessary: `1 ⋆ 1 = X-1`. In particular,
this is the discrete convolution, separate from the previously formalised
continuous convolution.

`MatchingSolutions p` is the subtype of coefficient vectors satisfying
all these remainder equations. The Jacobian is defined explicitly:

```lean
def matchingJacobian (p : ℕ) (a : Coefficients p) :
    Matrix (Fin (p - 1)) (Fin (p - 1)) ℂ :=
  fun r j => MvPolynomial.eval a
    (MvPolynomial.pderiv j (remainderEquation p r))

def IsSimpleMatchingSolution (p : ℕ) (a : Coefficients p) : Prop :=
  (matchingJacobian p a).det ≠ 0
```

`CountAndSimplicityAtOrder p` asserts finiteness, the binomial count of
distinct matching points, and this determinant condition at every point.

## Scope of the proved theorems

Both formulations have an unrestricted and a prime-index version:

```lean
def UniversalCountAndSimplicity : Prop :=
  ∀ p : ℕ, 2 ≤ p → CountAndSimplicityAtOrder p

def PrimeIndexCountAndSimplicity : Prop :=
  ∀ p : ℕ, 2 ≤ p → (2 * p - 1).Prime → CountAndSimplicityAtOrder p
```

The corresponding direct ODE declarations are
`UniversalRationalExponentialCountAndSimplicity` and
`PrimeIndexRationalExponentialCountAndSimplicity`.
The unrestricted assertion is the project's conjecture. The prime versions
have these Lean proofs:

```lean
theorem primeIndexCountAndSimplicity : PrimeIndexCountAndSimplicity := by
  intro p hp hprime
  obtain ⟨hfinite, hupper⟩ := prime_index_finite_and_card_le hp hprime
  exact ⟨hfinite, Nat.le_antisymm hupper (prime_index_card_ge hp hprime),
    prime_index_all_simple hp hprime⟩

theorem primeIndexRationalExponentialCountAndSimplicity :
    PrimeIndexRationalExponentialCountAndSimplicity := by
  intro p hp hprime
  exact rationalCountAndSimplicity_of_matching hp
    (primeIndexCountAndSimplicity p hp hprime) (simplicityCorrespondenceAtOrder hp)
```

Every lemma used here has a checked proof. The lower bound lifts every monic
degree-`p-1` divisor of `X^(2*p-1)-X` over the residue field of the
`ℓ`-adic integers, where `ℓ = 2*p-1`, then transfers the finite family of rational polynomial solutions
to `ℂ`. Reduction injectivity gives the upper bound, and the tangent argument
gives simplicity at every complex solution.

## Correspondence obligations are explicit

These additional definitions keep the correspondence statements explicit.
All four now have checked proofs for their stated domains:

- `DiscreteConvolutionSpecification`: the Bernoulli formula evaluates to
  `∑ j ∈ Ico 1 n, F(j) G(n-j)` for every positive integer `n`.
- `MatchingDivisibilityAtOrder p`: the evaluated remainder equations are
  equivalent to `A ∣ A ⋆ A`.
- `MatchingCorrespondenceAtOrder p`: the formulas
  `v_A = (2/beta_d) A(D)Q` and `P_A = (A ⋆ A)/(beta_d A)` give a bijection
  between matching parameters and the direct normalised ODE pairs.
- `SimplicityCorrespondenceAtOrder p`: the remainder Jacobian condition
  agrees with the direct infinitesimal ODE condition.

None of these is inserted as a hypothesis of either counting statement.

## Validation

From the `lean/` directory:

```sh
~/.elan/bin/lake build
~/.elan/bin/lake env lean EnumerationCheck.lean
~/.elan/bin/lake env lean Check.lean
```

All three commands pass. The first checks every proof module. The second
checks the exact proof types of both prime-index propositions, audits their
transitive axioms and the correspondence theorems, and checks three small
convolution identities for the endpoint and sign conventions. The last
retains the audit of the continuous-rigidity proof.
