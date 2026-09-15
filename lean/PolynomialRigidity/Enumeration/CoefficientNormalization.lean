import PolynomialRigidity.Enumeration.ReducedMatchingData

/-!
# Scalar normalisation of a polynomial variation

Dividing by a coefficient of maximal valuation makes all coefficients
integral and leaves a coefficient equal to one. The reduced polynomial is
therefore nonzero, even over ramified valuation rings.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

variable {K : Type*} [Field K]

theorem exists_integral_normalization (V : ValuationSubring K) (F : K[X]) (hF : F ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ ∃ hI : IntegralCoefficients V (C c * F),
      polynomialReduction V (C c * F) hI ≠ 0 ∧ (C c * F).degree = F.degree := by
  classical
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image F.support (fun i => V.valuation (F.coeff i))
    (support_nonempty.mpr hF)
  have hi0 : F.coeff i ≠ 0 := mem_support_iff.mp hi
  let c := (F.coeff i)⁻¹
  have hc : c ≠ 0 := inv_ne_zero hi0
  have hI : IntegralCoefficients V (C c * F) := by
    intro n
    rw [coeff_C_mul]
    by_cases hn : F.coeff n = 0
    · rw [hn, mul_zero]
      exact V.zero_mem
    · apply (V.valuation_le_one_iff _).mp
      change V.valuation ((F.coeff i)⁻¹ * F.coeff n) ≤ 1
      rw [map_mul, map_inv₀, mul_comm, ← div_eq_mul_inv]
      exact (div_le_one₀ (V.valuation.pos_iff.mpr hi0)).mpr (hmax n (mem_support_iff.mpr hn))
  have hunit : (C c * F).coeff i = 1 := by
    rw [coeff_C_mul]
    exact inv_mul_cancel₀ hi0
  refine ⟨c, hc, hI, ?_, degree_C_mul hc⟩
  intro hz
  have hsmall := (polynomialReduction_eq_zero_iff V (C c * F) hI).mp hz i
  rw [hunit, map_one] at hsmall
  exact lt_irrefl _ hsmall

end PolynomialRigidity.Enumeration
