import PolynomialRigidity.Enumeration.RateScaling

/-!
# The reduced matching factorisation

For an integral matching polynomial, the normalised cofactor is integral.
Its reduction is coprime to the reduced input, and the input is a divisor
of `X^ℓ-X`. These facts are used for both uniqueness and simplicity.
-/

noncomputable section

open Polynomial

namespace PolynomialRigidity.Enumeration

variable {K : Type*} [Field K] [CharZero K]

def normalizedMatchingQuotient (A : K[X]) : K[X] :=
  C ((2 * A.natDegree + 1 : ℕ) : K) * (discreteConvolution A A /ₘ A)

theorem normalizedMatchingQuotient_mul {A : K[X]} (hA : A.Monic) (hdiv : A ∣ discreteConvolution A A) :
    A * normalizedMatchingQuotient A = C ((2 * A.natDegree + 1 : ℕ) : K) * discreteConvolution A A := by
  have hz := (modByMonic_eq_zero_iff_dvd hA).mpr hdiv
  have he := modByMonic_add_div (discreteConvolution A A) A
  rw [hz, zero_add] at he
  unfold normalizedMatchingQuotient
  calc
    _ = C ((2 * A.natDegree + 1 : ℕ) : K) * (A * (discreteConvolution A A /ₘ A)) := by ring
    _ = _ := by rw [he]

theorem normalizedMatchingQuotient_integral (V : ValuationSubring K) {A : K[X]}
    (hA : A.Monic) (hAI : IntegralCoefficients V A) (hℓ : (2 * A.natDegree + 1).Prime)
    (hv : V.valuation ((2 * A.natDegree + 1 : ℕ) : K) < 1) (hdiv : A ∣ discreteConvolution A A) :
    IntegralCoefficients V (normalizedMatchingQuotient A) := by
  apply IntegralCoefficients.of_monic_mul (A := A) _ hAI hA
  rw [normalizedMatchingQuotient_mul hA hdiv]
  exact normalizedConvolution_integral V hA hAI hℓ hv

theorem reduced_matching_data (V : ValuationSubring K) {A : K[X]}
    (hA : A.Monic) (hAI : IntegralCoefficients V A) (hℓ : (2 * A.natDegree + 1).Prime)
    (hv : V.valuation ((2 * A.natDegree + 1 : ℕ) : K) < 1) (hdiv : A ∣ discreteConvolution A A) :
    polynomialReduction V A hAI ∣ (X ^ (2 * A.natDegree + 1) - X) ∧
    IsCoprime (polynomialReduction V A hAI)
      (polynomialReduction V (normalizedMatchingQuotient A)
        (normalizedMatchingQuotient_integral V hA hAI hℓ hv hdiv)) := by
  let ℓ := 2 * A.natDegree + 1
  let : CharP (IsLocalRing.ResidueField V) ℓ := residueField_charP V hℓ hv
  let hQI := normalizedMatchingQuotient_integral V hA hAI hℓ hv hdiv
  let Abar := polynomialReduction V A hAI
  let Cbar := polynomialReduction V (normalizedMatchingQuotient A) hQI
  obtain ⟨c, hc, hred⟩ := normalizedConvolution_reduction V hA hAI hℓ hv
  have hprod : Abar * Cbar = C c * (X ^ ℓ - X) := by
    calc
      _ = polynomialReduction V (A * normalizedMatchingQuotient A) (hAI.mul hQI) :=
        (polynomialReduction_mul V A (normalizedMatchingQuotient A) hAI hQI).symm
      _ = polynomialReduction V (C (ℓ : K) * discreteConvolution A A)
          (normalizedConvolution_integral V hA hAI hℓ hv) :=
        polynomialReduction_congr V (normalizedMatchingQuotient_mul hA hdiv) _ _
      _ = _ := hred
  have hdvd : Abar * Cbar ∣ X ^ ℓ - X := by
    refine ⟨C c⁻¹, ?_⟩
    rw [hprod]
    calc
      _ = C (c * c⁻¹) * (X ^ ℓ - X) := by rw [mul_inv_cancel₀ hc, C_1, one_mul]
      _ = _ := by rw [map_mul]; ring
  have hsep : (X ^ ℓ - X : (IsLocalRing.ResidueField V)[X]).Separable :=
    galois_poly_separable ℓ ℓ (dvd_refl ℓ)
  exact ⟨(dvd_mul_right _ _).trans hdvd, (hsep.of_dvd hdvd).isCoprime⟩

end PolynomialRigidity.Enumeration
