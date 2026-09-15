import PolynomialRigidity.Enumeration.Correspondence
import PolynomialRigidity.Enumeration.MatchingTangent

/-!
# Linearised rational equations and spectral variations

Dominant balance removes the variation of the leading pole coefficient.
The remaining variations are precisely the operators of degree below `p-1`.
-/

noncomputable section

open Polynomial

namespace PolynomialRigidity.Enumeration

def numeratorVariation (p : ℕ) (hN : ℂ[X]) : RationalFunction :=
  toRationalFunction hN / toRationalFunction ((X + 1) ^ p)

def scaledVariation (p : ℕ) (F : ℂ[X]) : RationalFunction :=
  algebraMap ℂ RationalFunction (profileScale p) * applyOperator F logistic

theorem linearizedODE_residual_eq (p : ℕ) (a : Coefficients p) (P hP F : ℂ[X]) :
    applyOperator P (scaledVariation p F) + applyOperator hP (candidateProfile p a) +
        candidateProfile p a * scaledVariation p F =
      algebraMap ℂ RationalFunction (profileScale p) *
        applyOperator (P * F + hP * coefficientPolynomial p a -
          C (profileScale p) * discreteConvolution (coefficientPolynomial p a) F) logistic := by
  simp only [scaledVariation, candidateProfile, applyOperator_smul_right,
    applyOperator_sub, applyOperator_add, applyOperator_mul, applyOperator_C]
  linear_combination (algebraMap ℂ RationalFunction (profileScale p)) ^ 2 *
    applyOperator_discreteConvolution (coefficientPolynomial p a) F

theorem linearizedODE_spectral_iff (p : ℕ) (a : Coefficients p) (P hP F : ℂ[X]) :
    (applyOperator P (scaledVariation p F) + applyOperator hP (candidateProfile p a) +
        candidateProfile p a * scaledVariation p F = 0) ↔
      P * F + hP * coefficientPolynomial p a =
        C (profileScale p) * discreteConvolution (coefficientPolynomial p a) F := by
  rw [linearizedODE_residual_eq, mul_eq_zero]
  simp only [profileScale_image_ne_zero, false_or]
  rw [← applyOperator_zero logistic, applyOperator_logistic_injective.eq_iff, sub_eq_zero]

theorem linearized_profile_degree_lt {p : ℕ} (hp : 0 < p) {P B hP H : ℂ[X]}
    (hPmonic : P.Monic) (hPdeg : P.natDegree = p) (hBdeg : B.natDegree = p) (hB : B ≠ 0)
    (hbase : SolvesODE P (aeval logistic B))
    (hPvar : hP.degree < (p : WithBot ℕ)) (hH : H.natDegree ≤ p)
    (hlin : applyOperator P (aeval logistic H) + applyOperator hP (aeval logistic B) +
      aeval logistic B * aeval logistic H = 0) : H.natDegree < p := by
  by_contra hlt
  have hHdeg : H.natDegree = p := Nat.le_antisymm hH (Nat.le_of_not_gt hlt)
  have hH0 : H ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hHdeg
    omega
  have hPnat : hP.natDegree < p := by
    by_cases hz : hP = 0
    · simpa only [hz, natDegree_zero] using hp
    · exact (natDegree_lt_iff_degree_lt hz).mpr hPvar
  have hpoly : polynomialOperator P H + polynomialOperator hP B + B * H = 0 := by
    apply logistic_aeval_injective
    simpa only [map_add, map_mul, map_zero, polynomialOperator_aeval] using hlin
  have hop := polynomialOperator_top_coeff P H
  rw [hPdeg, hHdeg, hPmonic.leadingCoeff, one_mul] at hop
  have hother : (polynomialOperator hP B).coeff (p + p) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    apply (polynomialOperator_natDegree_le hP B).trans_lt
    rw [hBdeg]
    omega
  have hprod : (B * H).coeff (p + p) = B.leadingCoeff * H.leadingCoeff := by
    have ht := coeff_mul_add_eq_of_natDegree_le (f := B) (g := H)
      (le_refl B.natDegree) (le_refl H.natDegree)
    simp only [coeff_natDegree] at ht
    simpa only [hBdeg, hHdeg] using ht
  have hlead := logistic_ODE_leadingCoeff hPmonic hPdeg hBdeg hB hbase
  have hk : (-1 : ℂ) ^ p * (p.ascFactorial p : ℂ) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hlead
    exact (leadingCoeff_ne_zero.mpr hB) hlead
  have hc := congrArg (fun F : ℂ[X] => F.coeff (p + p)) hpoly
  rw [coeff_add, coeff_add, hop, hother, add_zero, hprod, coeff_zero, hlead] at hc
  apply (mul_ne_zero hk (leadingCoeff_ne_zero.mpr hH0))
  linear_combination -hc

/-- Every allowed infinitesimal rational profile satisfying the linearised equation
comes from a polynomial variation strictly below the monic degree. -/
theorem linearized_variation_has_spectral_polynomial {p : ℕ} (hp : 2 ≤ p)
    (a : Coefficients p) (ha : IsMatchingSolution p a) (hP hN : ℂ[X])
    (hPdeg : hP.degree < (p : WithBot ℕ)) (hNdeg : hN.natDegree ≤ p) (hNzero : hN.eval 0 = 0)
    (hlin : applyOperator (candidateOperator p a) (numeratorVariation p hN) +
      applyOperator hP (candidateProfile p a) + candidateProfile p a * numeratorVariation p hN = 0) :
    ∃ F : ℂ[X], F.degree < (coefficientPolynomial p a).degree ∧
      numeratorVariation p hN = scaledVariation p F := by
  obtain ⟨B, ⟨hBdeg, hBzero, hBv⟩, _⟩ := normalizedProfile_exists_logistic (by omega)
    (candidateProfile p a) (candidateProfile_normalized hp a)
  have hB : B ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hBdeg
    omega
  let H := exponentialToLogistic p hN
  have hH0 : H.coeff 0 = 0 := by
    rw [exponentialToLogistic_coeff_zero, coeff_zero_eq_eval_zero]
    exact hNzero
  have hHv : aeval logistic H = numeratorVariation p hN := by
    rw [exponentialToLogistic_aeval p hN hNdeg]
    simp only [numeratorVariation, toRationalFunction_pow, toRationalFunction_add,
      toRationalFunction_one, add_comm]
  have hHdeg : H.natDegree < p := linearized_profile_degree_lt (by omega)
    (candidateOperator_monic p a) (candidateOperator_natDegree hp a) hBdeg hB
    (by simpa only [hBv] using candidateProfile_solvesODE p a ha) hPdeg
    (exponentialToLogistic_natDegree_le p hN) (by simpa only [hBv, hHv] using hlin)
  let F := C ((profileScale p)⁻¹) * inverseLogisticTransform H
  have hs := profileScale_ne_zero p
  have hFdegree : F.natDegree < p - 1 := by
    dsimp only [F]
    rw [natDegree_C_mul (inv_ne_zero hs)]
    by_cases hHz : H = 0
    · simp only [hHz, inverseLogisticTransform, natDegree_zero, Finset.range_zero, Finset.sum_empty]
      omega
    · have hi := inverseLogisticTransform_natDegree hH0 hHz
      omega
  have hTF : logisticTransform F = C ((profileScale p)⁻¹) * H := by
    dsimp only [F]
    rw [logisticTransform_C_mul, logisticTransform_inverseLogisticTransform H hH0]
  refine ⟨F, ?_, ?_⟩
  · rw [coefficientPolynomial_degree]
    exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hFdegree)
  · unfold scaledVariation
    rw [← logisticTransform_aeval F, hTF, map_mul, aeval_C, hHv,
      ← mul_assoc, ← map_mul, mul_inv_cancel₀ hs, map_one, one_mul]

theorem matchingQuotient_eq_scaled_operator (p : ℕ) (a : Coefficients p) :
    matchingQuotient p a = C (beta (p - 1) (p - 1) : ℂ) * candidateOperator p a := by
  unfold candidateOperator matchingQuotient
  rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (beta_ne_zero _ _), C_1, one_mul]

theorem beta_mul_profileScale (p : ℕ) : (beta (p - 1) (p - 1) : ℂ) * profileScale p = 2 := by
  unfold profileScale
  field_simp [beta_ne_zero (K := ℂ) (p - 1) (p - 1)]

theorem tangent_dvd_of_linearized_spectral (p : ℕ) (a : Coefficients p) (hP F : ℂ[X])
    (h : candidateOperator p a * F + hP * coefficientPolynomial p a =
      C (profileScale p) * discreteConvolution (coefficientPolynomial p a) F) :
    coefficientPolynomial p a ∣
      2 * discreteConvolution (coefficientPolynomial p a) F - matchingQuotient p a * F := by
  have he : matchingQuotient p a * F +
      (C (beta (p - 1) (p - 1) : ℂ) * hP) * coefficientPolynomial p a =
      2 * discreteConvolution (coefficientPolynomial p a) F := by
    calc
      _ = C (beta (p - 1) (p - 1) : ℂ) *
          (candidateOperator p a * F + hP * coefficientPolynomial p a) := by
        rw [matchingQuotient_eq_scaled_operator]
        ring
      _ = _ := by rw [h, ← mul_assoc, ← C_mul, beta_mul_profileScale, map_ofNat]
  refine ⟨C (beta (p - 1) (p - 1) : ℂ) * hP, ?_⟩
  linear_combination -he

end PolynomialRigidity.Enumeration
