import PolynomialRigidity.Enumeration.GeneralConvolution
import PolynomialRigidity.Enumeration.IntegralCoefficients
import PolynomialRigidity.Prime

/-!
# The prime denominator in the discrete convolution

At degree d, the sole nonintegral inverse-factorial term is the term indexed
by ℓ = 2d+1. Its normalisation is a unit and multiplies
`(X-1)⋯(X-ℓ)`. All lower terms are integral.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

section ValuationScalars

variable {K : Type*} [Field K]

theorem inverseLogisticBasisScalar_mem (V : ValuationSubring K) {ℓ n : ℕ}
    (hℓ : ℓ.Prime) (hv : V.valuation (ℓ : K) < 1) (hn : n < ℓ) :
    (((-1 : K) ^ n * (n.factorial : K))⁻¹) ∈ V := by
  have hval : V.valuation ((-1 : K) ^ n * (n.factorial : K)) = 1 := by
    simp only [map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul,
      valuation_factorial_eq_one V hℓ hv hn]
  apply (V.valuation_le_one_iff _).mp
  simp only [map_inv₀, hval, inv_one, le_refl]

theorem residueField_charP (V : ValuationSubring K) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hv : V.valuation (ℓ : K) < 1) : CharP (IsLocalRing.ResidueField V) ℓ := by
  apply (CharP.charP_iff_prime_eq_zero hℓ).mpr
  have hp : (ℓ : V) ∈ IsLocalRing.maximalIdeal V :=
    (V.valuation_lt_one_iff (ℓ : V)).mpr (by simpa using hv)
  simpa only [map_natCast] using (IsLocalRing.residue_eq_zero_iff (ℓ : V)).mpr hp

end ValuationScalars

section CharacteristicZero

variable {K : Type*} [Field K] [CharZero K]

def convolutionTail (A : K[X]) : K[X] :=
  ∑ n ∈ range (2 * A.natDegree + 1),
    C ((-logisticTransform A * logisticTransform A).coeff (n + 1) /
      ((-1 : K) ^ n * (n.factorial : K))) * spectralBasis n

theorem discreteConvolution_self_eq_top_add_tail {A : K[X]} (hA : A.Monic) :
    discreteConvolution A A =
      C (beta A.natDegree A.natDegree) * spectralBasis (2 * A.natDegree + 1) + convolutionTail A := by
  have hT : logisticTransform A ≠ 0 := by
    intro hz
    apply hA.ne_zero
    apply logisticTransform_injective
    simpa only [map_zero] using hz
  have hd : (-logisticTransform A * logisticTransform A).natDegree = 2 * A.natDegree + 1 + 1 := by
    rw [natDegree_mul (neg_ne_zero.mpr hT) hT, natDegree_neg, logisticTransform_natDegree hA.ne_zero]
    omega
  have hcT : (logisticTransform A).coeff (A.natDegree + 1) =
      (-1 : K) ^ A.natDegree * (A.natDegree.factorial : K) := by
    simpa only [hA.leadingCoeff, one_mul] using logisticTransform_top_coeff A
  have hc : (-logisticTransform A * logisticTransform A).coeff (2 * A.natDegree + 1 + 1) =
      -(A.natDegree.factorial : K) ^ 2 := by
    rw [show 2 * A.natDegree + 1 + 1 = (A.natDegree + 1) + (A.natDegree + 1) by omega]
    rw [coeff_mul_add_eq_of_natDegree_le
      (by rw [natDegree_neg, logisticTransform_natDegree hA.ne_zero])
      (by rw [logisticTransform_natDegree hA.ne_zero])]
    simp only [coeff_neg, hcT]
    rcases neg_one_pow_eq_or K A.natDegree with hs | hs <;> simp [hs, pow_two]
  have hsign : (-1 : K) ^ (2 * A.natDegree + 1) = -1 := by
    simp [pow_add, pow_mul]
  have htop : (-logisticTransform A * logisticTransform A).coeff (2 * A.natDegree + 1 + 1) /
      ((-1 : K) ^ (2 * A.natDegree + 1) * ((2 * A.natDegree + 1).factorial : K)) =
        beta A.natDegree A.natDegree := by
    rw [hc, hsign]
    simp [beta, pow_two, two_mul]
  rw [discreteConvolution_eq_inverse_general, inverseLogisticTransform, hd, Finset.sum_range_succ, htop]
  exact add_comm _ _

omit [CharZero K] in
theorem convolutionTail_integral (V : ValuationSubring K) {A : K[X]}
    (hA : IntegralCoefficients V A) (hℓ : (2 * A.natDegree + 1).Prime)
    (hv : V.valuation ((2 * A.natDegree + 1 : ℕ) : K) < 1) :
    IntegralCoefficients V (convolutionTail A) := by
  have hB := hA.logisticTransform.neg.mul hA.logisticTransform
  apply IntegralCoefficients.sum
  intro n hn
  apply IntegralCoefficients.mul
  · apply IntegralCoefficients.C
    rw [div_eq_mul_inv]
    exact V.toSubring.mul_mem (hB (n + 1))
      (inverseLogisticBasisScalar_mem V hℓ hv (Finset.mem_range.mp hn))
  · exact IntegralCoefficients.spectralBasis n

/-- Products below the critical total degree have no prime denominator at all. -/
theorem discreteConvolution_integral_of_degree_lt (V : ValuationSubring K) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hv : V.valuation (ℓ : K) < 1) {F G : K[X]}
    (hF : IntegralCoefficients V F) (hG : IntegralCoefficients V G)
    (hdegree : F.natDegree + G.natDegree + 1 < ℓ) :
    IntegralCoefficients V (discreteConvolution F G) := by
  have hB := hF.logisticTransform.neg.mul hG.logisticTransform
  have hbound : (-logisticTransform F * logisticTransform G).natDegree ≤
      F.natDegree + G.natDegree + 2 := by
    apply natDegree_mul_le.trans
    rw [natDegree_neg]
    have h₁ := logisticTransform_natDegree_le F
    have h₂ := logisticTransform_natDegree_le G
    omega
  rw [discreteConvolution_eq_inverse_general, inverseLogisticTransform]
  apply IntegralCoefficients.sum
  intro n hn
  have hnℓ : n < ℓ := by have := Finset.mem_range.mp hn; omega
  apply IntegralCoefficients.mul
  · apply IntegralCoefficients.C
    rw [div_eq_mul_inv]
    exact V.toSubring.mul_mem (hB (n + 1)) (inverseLogisticBasisScalar_mem V hℓ hv hnℓ)
  · exact IntegralCoefficients.spectralBasis n

theorem normalizedConvolution_eq {A : K[X]} (hA : A.Monic) :
    C ((2 * A.natDegree + 1 : ℕ) : K) * discreteConvolution A A =
      C (((2 * A.natDegree + 1 : ℕ) : K) * beta A.natDegree A.natDegree) *
        spectralBasis (2 * A.natDegree + 1) +
      C ((2 * A.natDegree + 1 : ℕ) : K) * convolutionTail A := by
  rw [discreteConvolution_self_eq_top_add_tail hA, mul_add, ← mul_assoc, ← C_mul]

theorem normalizedConvolution_integral (V : ValuationSubring K) {A : K[X]}
    (hA : A.Monic) (hAI : IntegralCoefficients V A) (hℓ : (2 * A.natDegree + 1).Prime)
    (hv : V.valuation ((2 * A.natDegree + 1 : ℕ) : K) < 1) :
    IntegralCoefficients V (C ((2 * A.natDegree + 1 : ℕ) : K) * discreteConvolution A A) := by
  rw [normalizedConvolution_eq hA]
  apply IntegralCoefficients.add
  · apply IntegralCoefficients.mul
    · apply IntegralCoefficients.C
      apply (V.valuation_le_one_iff _).mp
      exact le_of_eq (PolynomialRigidity.valuation_prime_mul_beta_self V hℓ hv)
    · exact IntegralCoefficients.spectralBasis _
  · exact (IntegralCoefficients.C (natCast_mem V _)).mul (convolutionTail_integral V hAI hℓ hv)

end CharacteristicZero

end PolynomialRigidity.Enumeration
