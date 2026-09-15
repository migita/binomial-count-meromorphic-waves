# Completed prime enumeration and simplicity

The requested objective is complete. The original propositions in
`PolynomialRigidity/EnumerationStatement.lean` are unchanged and now have
proofs in `PolynomialRigidity/Enumeration/PrimeEnumeration.lean`:

```lean
theorem primeIndexCountAndSimplicity : PrimeIndexCountAndSimplicity
theorem primeIndexRationalExponentialCountAndSimplicity :
  PrimeIndexRationalExponentialCountAndSimplicity
```

For every `p ≥ 2` with `ℓ = 2*p-1` prime, both the matching solution type and
the direct normalized rational ODE pair type are finite, have exactly
`ℓ.choose (p-1)` elements, and every element is simple in its original
specified sense. The unrestricted all-order propositions remain conjectures.

## Proof map

1. **The actual discrete equations.** `Basic.lean` proves universal remainder
   specialization and `matchingDivisibilityAtOrder`. `Discrete.lean` proves
   `discreteConvolutionSpecification`, including the excluded endpoints.
   `UniversalEquations.lean` constructs the rational-coefficient versions of
   these equations and proves their specialization to the unchanged complex
   equations.
2. **Rational-function correspondence.** `RationalCalculus.lean` and
   `LogisticIdentity.lean` prove the differential-operator identities.
   `LogisticPolynomial.lean`, `InverseLogistic.lean`, `ConvolutionDegree.lean`,
   `MobiusCoordinates.lean`, and `OperatorLeading.lean` supply the inverse
   coordinates, exact degrees and pole order, and forced normalization.
   `Correspondence.lean` proves `matchingCorrespondenceAtOrder` and the
   equivalence `matchingODEEquiv` for every `p ≥ 2`.
3. **Simplicity correspondence.** `CoefficientDerivation.lean`,
   `JacobianColumns.lean`, and `MatchingTangent.lean` identify the original
   coefficient Jacobian with polynomial transversality. `LinearizedODE.lean`
   and `SimplicityCorrespondence.lean` prove `simplicityCorrespondenceAtOrder`
   for every `p ≥ 2`, allowing every numerator and operator variation in the
   original definition of `IsSimpleODEPair`.
4. **Prime reduction and integrality.** `GeneralConvolution.lean`,
   `IntegralCoefficients.lean`, `PrimeConvolutionKernel.lean`, and
   `PrimeReduction.lean` prove the normalized congruence
   `ℓ*S_A ↦ c*(X^ℓ-X)` with `c ≠ 0`. `RateScaling.lean` proves
   `monic_matching_integral` for every complex matching solution.
5. **Simplicity and the upper bound.** `ReducedMatchingData.lean` and
   `CoefficientNormalization.lean` provide coprimality and nonzero reduced
   variations. `PrimeTransversality.lean` proves `prime_index_all_simple`.
   `PrimeUniqueness.lean` proves injectivity of reduction, and
   `PrimeUpperBound.lean` proves `prime_index_finite_and_card_le` for all
   complex matching points. `FiniteLabels.lean` supplies the exact binomial
   count of residue labels.
6. **Lifting every label.** `MultivariateHensel.lean` proves the generic
   `PolynomialSystem.hensel_simple_system` using a standard smooth
   presentation and formal smooth lifting into a complete local ring.
   `FactorJacobian.lean` proves that the fixed-factor remainder system has
   invertible Jacobian at every monic divisor of a separable polynomial,
   over any field. `UniversalKernel.lean` and `IntegralMatchingSystem.lean`
   construct the denominator-cleared universal system, prove its reduction
   to that factor system, and prove that its characteristic-zero points
   satisfy the original rational equations.
7. **The lower bound and exact result.** `PrimeLowerBound.lean` lifts every
   residue label in `ℤ_[ℓ]`, obtains an injective family in `ℚ_[ℓ]`, and uses
   `ComplexTransfer.lean` to transfer that finite family to the actual
   complex matching solutions. This proves `prime_index_card_ge`.
   `PrimeEnumeration.lean` combines the bounds and simplicity, then uses the
   proved correspondences to establish both original target propositions.

All file names in this map are relative to `PolynomialRigidity/Enumeration/`.
No lifting, correspondence, finiteness, or simplicity claim is assumed as an
extra hypothesis of either final prime-index theorem.

## Validation

```sh
~/.elan/bin/lake build
~/.elan/bin/lake env lean EnumerationCheck.lean
~/.elan/bin/lake env lean Check.lean
```

All three checks pass with Lean and mathlib pinned to v4.33.1.
`EnumerationCheck.lean` checks the proof types against the original
propositions and uses guarded `#print axioms` audits for both final targets
and the correspondence theorems. Their only axioms are `propext`,
`Classical.choice`, and `Quot.sound`. There are no proof placeholders, new
axioms, or `native_decide` in the proof sources. The existing continuous
prime-rigidity proof and its audit also pass.
