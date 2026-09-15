import PolynomialRigidity.Enumeration.CoefficientNormalization
import PolynomialRigidity.Enumeration.MatchingTangent

/-!
# Prime-index simplicity

After normalising a nonzero variation by one of its coefficients, the
convolution term vanishes on reduction. Coprimality of the two reduced
factors then forces the reduced variation to vanish, a contradiction.
-/

noncomputable section

open Polynomial

namespace PolynomialRigidity.Enumeration

theorem integral_matching_transverse {K : Type*} [Field K] [CharZero K]
    (V : ValuationSubring K) {A : K[X]} (hA : A.Monic) (hAI : IntegralCoefficients V A)
    (hℓ : (2 * A.natDegree + 1).Prime)
    (hv : V.valuation ((2 * A.natDegree + 1 : ℕ) : K) < 1)
    (hdiv : A ∣ discreteConvolution A A) :
    ∀ F : K[X], F.degree < A.degree →
      A ∣ 2 * discreteConvolution A F - (discreteConvolution A A /ₘ A) * F → F = 0 := by
  intro F hdegree hdivF
  by_contra hF
  obtain ⟨c, hc, hHI, hHred, hHdegree⟩ := exists_integral_normalization V F hF
  let H := C c * F
  let ℓ := 2 * A.natDegree + 1
  have hH0 : H ≠ 0 :=
    mul_ne_zero (by simpa only [map_zero] using Polynomial.C_injective.ne hc) hF
  have hHdeg : H.degree < A.degree := hHdegree.trans_lt hdegree
  have hHnat : H.natDegree < A.natDegree := natDegree_lt_natDegree hH0 hHdeg
  have hSI : IntegralCoefficients V (discreteConvolution A H) :=
    discreteConvolution_integral_of_degree_lt V hℓ hv hAI hHI (by omega)
  have hS2I : IntegralCoefficients V (2 * discreteConvolution A H) :=
    (IntegralCoefficients.C (c := (2 : K)) (natCast_mem V 2)).mul hSI
  have hQI := normalizedMatchingQuotient_integral V hA hAI hℓ hv hdiv
  let U := C (ℓ : K) * (2 * discreteConvolution A H) - normalizedMatchingQuotient A * H
  have hUI : IntegralCoefficients V U :=
    ((IntegralCoefficients.C (natCast_mem V ℓ)).mul hS2I).sub (hQI.mul hHI)
  have hdivH : A ∣ 2 * discreteConvolution A H - (discreteConvolution A A /ₘ A) * H := by
    have he : 2 * discreteConvolution A H - (discreteConvolution A A /ₘ A) * H =
        C c * (2 * discreteConvolution A F - (discreteConvolution A A /ₘ A) * F) := by
      dsimp only [H]
      rw [discreteConvolution_C_mul_right]
      ring
    rw [he]
    exact dvd_mul_of_dvd_right hdivF (C c)
  have hdivU : A ∣ U := by
    have he : U = C (ℓ : K) *
        (2 * discreteConvolution A H - (discreteConvolution A A /ₘ A) * H) := by
      dsimp only [U, normalizedMatchingQuotient, ℓ]
      ring
    rw [he]
    exact dvd_mul_of_dvd_right hdivH (C (ℓ : K))
  let Abar := polynomialReduction V A hAI
  let Hbar := polynomialReduction V H hHI
  let Cbar := polynomialReduction V (normalizedMatchingQuotient A) hQI
  have hUred : polynomialReduction V U hUI = -(Cbar * Hbar) := by
    rw [polynomialReduction_sub V _ _ ((IntegralCoefficients.C (natCast_mem V ℓ)).mul hS2I)
      (hQI.mul hHI), polynomialReduction_C_mul_eq_zero V (ℓ : K) _ (natCast_mem V ℓ) hv hS2I,
      polynomialReduction_mul V _ _ hQI hHI, zero_sub]
  have hredDiv := polynomialReduction_dvd V hAI hUI hA hdivU
  rw [hUred, dvd_neg] at hredDiv
  have hcop : IsCoprime Abar Cbar := (reduced_matching_data V hA hAI hℓ hv hdiv).2
  have hAH : Abar ∣ Hbar := hcop.dvd_of_dvd_mul_left hredDiv
  have hdegBar : Hbar.degree < Abar.degree := by
    rw [polynomialReduction_degree V A hAI hA]
    exact (polynomialReduction_degree_le V H hHI).trans_lt hHdeg
  exact hHred (eq_zero_of_dvd_of_degree_lt hAH hdegBar)

/-- Every point of the stated prime-index matching system has nonzero Jacobian determinant. -/
theorem prime_index_all_simple {p : ℕ} (hp : 2 ≤ p) (hprime : (2 * p - 1).Prime) :
    ∀ a : MatchingSolutions p, IsSimpleMatchingSolution p a.val := by
  obtain ⟨V, hv⟩ := exists_prime_valuation (K := ℂ) hprime
  intro a
  let A := coefficientPolynomial p a.val
  have hA : A.Monic := coefficientPolynomial_monic p a.val
  have he : 2 * A.natDegree + 1 = 2 * p - 1 := by
    simp only [A, coefficientPolynomial_natDegree]
    omega
  have hℓ : (2 * A.natDegree + 1).Prime := by simpa only [he] using hprime
  have hvA : V.valuation ((2 * A.natDegree + 1 : ℕ) : ℂ) < 1 := by simpa only [he] using hv
  have hdiv : A ∣ discreteConvolution A A := (matchingDivisibilityAtOrder p a.val).mp a.property
  have hAI := monic_matching_integral V hA hℓ hvA hdiv
  apply (isSimpleMatchingSolution_iff_transverse p a.val).mpr
  exact integral_matching_transverse V hA hAI hℓ hvA hdiv

end PolynomialRigidity.Enumeration
