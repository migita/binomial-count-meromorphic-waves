import PolynomialRigidity.Enumeration.LinearizedODE

/-!
# Simplicity correspondence

The specified remainder Jacobian is nonsingular exactly when the normalised
rational equation-profile pair has no nonzero infinitesimal deformation.
The proof retains all numerator variations allowed in the original statement.
-/

noncomputable section

open Polynomial

namespace PolynomialRigidity.Enumeration

theorem simpleODE_of_transverse {p : ℕ} (hp : 2 ≤ p) (a : Coefficients p)
    (ha : IsMatchingSolution p a) (htrans : IsTransverseMatching p a) :
    IsSimpleODEPair p (candidatePair p a) := by
  intro hP hN hPdeg hNdeg hNzero
  change (applyOperator (candidateOperator p a) (numeratorVariation p hN) +
    applyOperator hP (candidateProfile p a) + candidateProfile p a * numeratorVariation p hN = 0) →
      hP = 0 ∧ hN = 0
  intro hlin
  obtain ⟨F, hFdeg, hFv⟩ := linearized_variation_has_spectral_polynomial hp a ha hP hN
    hPdeg hNdeg hNzero hlin
  have hspec := (linearizedODE_spectral_iff p a (candidateOperator p a) hP F).mp
    (by simpa only [← hFv] using hlin)
  have hFzero := htrans F hFdeg (tangent_dvd_of_linearized_spectral p a hP F hspec)
  have hN0 : hN = 0 := by
    rw [hFzero, scaledVariation, applyOperator_zero, mul_zero] at hFv
    unfold numeratorVariation at hFv
    have hd : toRationalFunction ((X + 1) ^ p) ≠ 0 := by
      simpa only [toRationalFunction_pow, toRationalFunction_add, toRationalFunction_one,
        add_comm] using pow_ne_zero p one_add_variable_ne_zero
    apply (toRationalFunction_eq_zero hN).mp
    exact (div_eq_zero_iff.mp hFv).resolve_right hd
  have hP0 : hP = 0 := by
    rw [hFzero, mul_zero, zero_add, discreteConvolution_zero_right, mul_zero] at hspec
    exact (mul_eq_zero.mp hspec).resolve_right (coefficientPolynomial_monic p a).ne_zero
  exact ⟨hP0, hN0⟩

theorem matchingQuotient_natDegree {p : ℕ} (hp : 2 ≤ p) (a : Coefficients p) :
    (matchingQuotient p a).natDegree = p := by
  have h := candidateOperator_natDegree hp a
  unfold candidateOperator at h
  rw [natDegree_C_mul (inv_ne_zero (beta_ne_zero _ _))] at h
  exact h

theorem transverse_of_simpleODE {p : ℕ} (hp : 2 ≤ p) (a : Coefficients p)
    (hsimple : IsSimpleODEPair p (candidatePair p a)) : IsTransverseMatching p a := by
  intro F hdegree hdiv
  by_cases hFzero : F = 0
  · exact hFzero
  have hFnat : F.natDegree < p - 1 := by
    rw [coefficientPolynomial_degree] at hdegree
    exact (natDegree_lt_iff_degree_lt hFzero).mpr hdegree
  let A := coefficientPolynomial p a
  let Q := matchingQuotient p a
  let T := 2 * discreteConvolution A F - Q * F
  let k := T /ₘ A
  let hP := C ((beta (p - 1) (p - 1) : ℂ)⁻¹) * k
  let B := C (profileScale p) * logisticTransform F
  let hN := logisticNumerator p B
  have hA := (coefficientPolynomial_monic p a).ne_zero
  have hTdegree : T.natDegree ≤ 2 * (p - 1) := by
    have hfirst : (2 * discreteConvolution A F).natDegree ≤ 2 * (p - 1) := by
      rw [show (2 : ℂ[X]) = C (2 : ℂ) from rfl, natDegree_C_mul (by norm_num),
        discreteConvolution_natDegree hA hFzero, coefficientPolynomial_natDegree]
      omega
    have hsecond : (Q * F).natDegree ≤ 2 * (p - 1) := by
      apply natDegree_mul_le.trans
      rw [matchingQuotient_natDegree hp a]
      omega
    apply natDegree_le_iff_degree_le.mpr
    exact (degree_sub_le _ _).trans
      (max_le (degree_le_of_natDegree_le hfirst) (degree_le_of_natDegree_le hsecond))
  have hkdegree : k.natDegree ≤ p - 1 := by
    dsimp only [k]
    rw [natDegree_divByMonic _ (coefficientPolynomial_monic p a), coefficientPolynomial_natDegree]
    omega
  have hPdegree : hP.degree < (p : WithBot ℕ) := by
    have hnat : hP.natDegree < p := by
      dsimp only [hP]
      rw [natDegree_C_mul (inv_ne_zero (beta_ne_zero _ _))]
      omega
    exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hnat)
  have hBdegree : B.natDegree ≤ p := by
    dsimp only [B]
    rw [natDegree_C_mul (profileScale_ne_zero p), logisticTransform_natDegree hFzero]
    omega
  have hBzero : B.coeff 0 = 0 := by simp only [B, coeff_C_mul, logisticTransform_coeff_zero, mul_zero]
  have hNdegree : hN.natDegree ≤ p := logisticNumerator_natDegree_le p B
  have hNzero : hN.eval 0 = 0 := by simpa only [hN, logisticNumerator_eval_zero] using hBzero
  have hrepr : numeratorVariation p hN = scaledVariation p F := by
    have he : aeval logistic B = numeratorVariation p hN := by
      simpa only [numeratorVariation, hN, toRationalFunction_pow, toRationalFunction_add,
        toRationalFunction_one, add_comm] using aeval_logistic_eq_div p B hBdegree
    rw [← he]
    simp only [B, map_mul, aeval_C, logisticTransform_aeval, scaledVariation]
  have hfactor : A * k = T := by
    have hz : T %ₘ A = 0 :=
      (modByMonic_eq_zero_iff_dvd (coefficientPolynomial_monic p a)).mpr hdiv
    simpa only [hz, zero_add, k] using modByMonic_add_div T A
  have hspec : candidateOperator p a * F + hP * A = C (profileScale p) * discreteConvolution A F := by
    change (C ((beta (p - 1) (p - 1) : ℂ)⁻¹) * Q) * F +
      (C ((beta (p - 1) (p - 1) : ℂ)⁻¹) * k) * A = _
    calc
      _ = C ((beta (p - 1) (p - 1) : ℂ)⁻¹) * (Q * F + A * k) := by ring
      _ = C ((beta (p - 1) (p - 1) : ℂ)⁻¹) *
          (Q * F + (2 * discreteConvolution A F - Q * F)) := by rw [hfactor]
      _ = _ := by simp only [profileScale, div_eq_mul_inv, map_mul, map_ofNat]; ring
  have hlin := (linearizedODE_spectral_iff p a (candidateOperator p a) hP F).mpr hspec
  have hlinN : applyOperator (candidateOperator p a) (numeratorVariation p hN) +
      applyOperator hP (candidateProfile p a) + candidateProfile p a * numeratorVariation p hN = 0 := by
    simpa only [hrepr] using hlin
  have hz : hP = 0 ∧ hN = 0 := hsimple hP hN hPdegree hNdegree hNzero hlinN
  have hvar : scaledVariation p F = 0 := by
    rw [← hrepr, numeratorVariation, hz.2, toRationalFunction_zero, zero_div]
  apply applyOperator_logistic_injective
  change applyOperator F logistic = applyOperator 0 logistic
  rw [applyOperator_zero]
  exact (mul_eq_zero.mp hvar).resolve_left (profileScale_image_ne_zero p)

/-- The full simplicity correspondence required by the direct rational-function target. -/
theorem simplicityCorrespondenceAtOrder {p : ℕ} (hp : 2 ≤ p) : SimplicityCorrespondenceAtOrder p := by
  intro a ha
  rw [isSimpleMatchingSolution_iff_transverse]
  exact ⟨simpleODE_of_transverse hp a ha, transverse_of_simpleODE hp a⟩

end PolynomialRigidity.Enumeration
