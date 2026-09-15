import PolynomialRigidity.Enumeration.ConvolutionDegree

/-!
# The pole normalisation in logistic coordinates

Substituting `q=t/(1+t)` expresses a degree-`p` polynomial in `q` as a
rational function with denominator `(1+t)^p`. Evaluation of its numerator
at `t=-1` detects the leading coefficient, so the pole order is exact.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

local notation "ι" => toRationalFunction

@[simp]
theorem toRationalFunction_sum {α : Type*} (s : Finset α) (F : α → ℂ[X]) :
    ι (∑ i ∈ s, F i) = ∑ i ∈ s, ι (F i) := map_sum (algebraMap ℂ[X] RationalFunction) _ _

theorem logistic_eq_div : logistic = ι X / (1 + ι X) := by
  simp only [logistic, toRationalFunction_add, toRationalFunction_one]

theorem one_sub_logistic : 1 - logistic = (1 + ι X)⁻¹ := by
  rw [logistic_eq_div]
  field_simp [one_add_variable_ne_zero]
  ring

theorem logistic_power_clear_denominator (p i : ℕ) (hi : i ≤ p) :
    logistic ^ i * (1 + ι X) ^ p = ι X ^ i * (1 + ι X) ^ (p - i) := by
  have hp : (1 + ι X) ^ p = (1 + ι X) ^ i * (1 + ι X) ^ (p - i) := by
    rw [← pow_add, Nat.add_sub_of_le hi]
  rw [logistic_eq_div, div_pow, hp]
  field_simp [one_add_variable_ne_zero]

theorem logistic_bernstein_clear_denominator (p i : ℕ) (hi : i ≤ p) :
    (logistic ^ i * (1 - logistic) ^ (p - i)) * (1 + ι X) ^ p = ι X ^ i := by
  have hp : (1 + ι X) ^ p = (1 + ι X) ^ i * (1 + ι X) ^ (p - i) := by
    rw [← pow_add, Nat.add_sub_of_le hi]
  rw [one_sub_logistic, logistic_eq_div, div_pow, inv_pow, hp]
  field_simp [one_add_variable_ne_zero]

def logisticNumerator (p : ℕ) (B : ℂ[X]) : ℂ[X] :=
  ∑ i ∈ range (p + 1), C (B.coeff i) * X ^ i * (1 + X) ^ (p - i)

def exponentialToLogistic (p : ℕ) (N : ℂ[X]) : ℂ[X] :=
  ∑ i ∈ range (p + 1), C (N.coeff i) * X ^ i * (1 - X) ^ (p - i)

private theorem natDegree_substitution_le (p : ℕ) (B L : ℂ[X]) (hL : L.natDegree ≤ 1) :
    (∑ i ∈ range (p + 1), C (B.coeff i) * X ^ i * L ^ (p - i)).natDegree ≤ p := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have hip : i ≤ p := by simpa using hi
  calc
    (C (B.coeff i) * X ^ i * L ^ (p - i)).natDegree ≤
        (C (B.coeff i) * X ^ i).natDegree + (L ^ (p - i)).natDegree := natDegree_mul_le
    _ ≤ i + (p - i) := add_le_add (natDegree_C_mul_X_pow_le _ _)
      (by simpa using natDegree_pow_le_of_le (p - i) hL)
    _ = p := Nat.add_sub_of_le hip

theorem logisticNumerator_natDegree_le (p : ℕ) (B : ℂ[X]) :
    (logisticNumerator p B).natDegree ≤ p := by
  apply natDegree_substitution_le
  simpa only [C_1, add_comm] using (natDegree_X_add_C (1 : ℂ)).le

theorem exponentialToLogistic_natDegree_le (p : ℕ) (N : ℂ[X]) :
    (exponentialToLogistic p N).natDegree ≤ p := by
  apply natDegree_substitution_le
  rw [show (1 - X : ℂ[X]) = -(X - C 1) by simp, natDegree_neg, natDegree_X_sub_C]

@[simp]
theorem logisticNumerator_eval_zero (p : ℕ) (B : ℂ[X]) :
    (logisticNumerator p B).eval 0 = B.coeff 0 := by
  simp [logisticNumerator, eval_finsetSum, zero_pow_eq]

@[simp]
theorem exponentialToLogistic_coeff_zero (p : ℕ) (N : ℂ[X]) :
    (exponentialToLogistic p N).coeff 0 = N.coeff 0 := by
  rw [coeff_zero_eq_eval_zero]
  simp [exponentialToLogistic, eval_finsetSum, zero_pow_eq]

theorem logisticNumerator_eval_neg_one (p : ℕ) (B : ℂ[X]) :
    (logisticNumerator p B).eval (-1) = B.coeff p * (-1 : ℂ) ^ p := by
  rw [logisticNumerator, eval_finsetSum, Finset.sum_eq_single p]
  · simp
  · intro i hi hip
    have hpi : p - i ≠ 0 := by
      have hi' : i ≤ p := by simpa using hi
      omega
    simp [hpi]
  · simp

theorem aeval_logistic_eq_div (p : ℕ) (B : ℂ[X]) (hB : B.natDegree ≤ p) :
    aeval logistic B = ι (logisticNumerator p B) / (1 + ι X) ^ p := by
  apply (eq_div_iff (pow_ne_zero _ one_add_variable_ne_zero)).mpr
  conv_lhs =>
    lhs
    rw [B.as_sum_range_C_mul_X_pow' (Nat.lt_succ_iff.mpr hB)]
  simp only [map_sum, map_mul, aeval_C, map_pow, aeval_X, logisticNumerator,
    toRationalFunction_sum, toRationalFunction_mul, toRationalFunction_C,
    toRationalFunction_pow, toRationalFunction_add, toRationalFunction_one, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc, logistic_power_clear_denominator p i (by simpa using hi)]
  ring

theorem exponentialToLogistic_aeval (p : ℕ) (N : ℂ[X]) (hN : N.natDegree ≤ p) :
    aeval logistic (exponentialToLogistic p N) = ι N / (1 + ι X) ^ p := by
  apply (eq_div_iff (pow_ne_zero _ one_add_variable_ne_zero)).mpr
  conv_rhs => rw [N.as_sum_range_C_mul_X_pow' (Nat.lt_succ_iff.mpr hN)]
  simp only [exponentialToLogistic, map_sum, map_mul, aeval_C, map_pow, map_sub, map_one,
    aeval_X, toRationalFunction_sum, toRationalFunction_mul, toRationalFunction_C,
    toRationalFunction_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = algebraMap ℂ RationalFunction (N.coeff i) *
        ((logistic ^ i * (1 - logistic) ^ (p - i)) * (1 + ι X) ^ p) := by ring
    _ = _ := by rw [logistic_bernstein_clear_denominator p i (by simpa using hi)]

theorem logisticNumerator_exponentialToLogistic (p : ℕ) (N : ℂ[X]) (hN : N.natDegree ≤ p) :
    logisticNumerator p (exponentialToLogistic p N) = N := by
  apply toRationalFunction_injective
  apply (div_left_inj' (pow_ne_zero p one_add_variable_ne_zero)).mp
  rw [← aeval_logistic_eq_div p _ (exponentialToLogistic_natDegree_le p N),
    exponentialToLogistic_aeval p N hN]

theorem numerator_nonzero_at_pole {v : RationalFunction} {p : ℕ}
    (hp : 0 < p) (hden : v.denom = (X + 1) ^ p) : v.num.eval (-1) ≠ 0 := by
  intro hzero
  obtain ⟨F, G, hFG⟩ := v.isCoprime_num_denom
  have h := congrArg (Polynomial.eval (-1)) hFG
  simp [hden, hzero, zero_pow hp.ne'] at h

/-- A monic coprime fraction is already the canonical reduced fraction. -/
theorem rational_num_denom_of_coprime (N D : ℂ[X]) (hD : D.Monic) (hc : IsCoprime N D) :
    (ι N / ι D).num = N ∧ (ι N / ι D).denom = D := by
  let v := ι N / ι D
  have he : v.num * D = N * v.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff hD.ne_zero).mpr rfl
  have hd : v.denom ∣ D := RatFunc.denom_div_dvd N D
  have hd' : D ∣ v.denom := by
    apply hc.symm.dvd_of_dvd_mul_left
    rw [← he]
    exact dvd_mul_left _ _
  have hden : v.denom = D := eq_of_monic_of_dvd_of_natDegree_le hD v.monic_denom hd'
    (natDegree_le_of_dvd hd hD.ne_zero)
  refine ⟨?_, hden⟩
  rw [hden] at he
  exact mul_right_cancel₀ hD.ne_zero he

theorem isCoprime_pole_denominator (p : ℕ) (N : ℂ[X]) (hN : N.eval (-1) ≠ 0) :
    IsCoprime N ((X + 1) ^ p) := by
  have hn : ¬(X - C (-1 : ℂ)) ∣ N := by simpa only [dvd_iff_isRoot, IsRoot.def] using hN
  have hc := ((irreducible_X_sub_C (-1 : ℂ)).isCoprime_or_dvd N).resolve_right hn
  have hp : IsCoprime N ((X - C (-1 : ℂ)) ^ p) := hc.symm.pow_right
  simpa only [map_neg, C_1, sub_neg_eq_add] using hp

/-- The polynomial logistic parametrisation has exactly the pole order appearing in the statement. -/
theorem normalizedProfile_of_logistic {p : ℕ} (B : ℂ[X]) (hdegree : B.natDegree = p)
    (hB : B ≠ 0) (hzero : B.coeff 0 = 0) :
    IsNormalizedProfile p (aeval logistic B) := by
  have hn : (logisticNumerator p B).eval (-1) ≠ 0 := by
    rw [logisticNumerator_eval_neg_one, ← hdegree]
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hB) (pow_ne_zero _ (by norm_num))
  have hD : ((X + 1 : ℂ[X]) ^ p).Monic := by
    simpa only [C_1] using (monic_X_add_C (1 : ℂ)).pow p
  have hcanon := rational_num_denom_of_coprime (logisticNumerator p B) ((X + 1) ^ p)
    hD (isCoprime_pole_denominator p _ hn)
  have hrepr : aeval logistic B = ι (logisticNumerator p B) / ι ((X + 1) ^ p) := by
    simpa only [toRationalFunction_pow, toRationalFunction_add, toRationalFunction_one,
      add_comm] using aeval_logistic_eq_div p B hdegree.le
  unfold IsNormalizedProfile
  rw [hrepr, hcanon.1, hcanon.2]
  exact ⟨rfl, logisticNumerator_natDegree_le p B, by simpa only [logisticNumerator_eval_zero] using hzero⟩

/-- Every profile in the direct target has a unique polynomial logistic representation. -/
theorem normalizedProfile_exists_logistic {p : ℕ} (hp : 0 < p) (v : RationalFunction)
    (hv : IsNormalizedProfile p v) :
    ∃! B : ℂ[X], B.natDegree = p ∧ B.coeff 0 = 0 ∧ aeval logistic B = v := by
  let B := exponentialToLogistic p v.num
  have he : aeval logistic B = v := by
    rw [exponentialToLogistic_aeval p v.num hv.2.1]
    have hnum : ι v.num / ι v.denom = v := v.num_div_denom
    rw [hv.1, toRationalFunction_pow, toRationalFunction_add,
      toRationalFunction_one, add_comm (ι X) 1] at hnum
    exact hnum
  have htop : B.coeff p ≠ 0 := by
    have hn := numerator_nonzero_at_pole hp hv.1
    rw [← logisticNumerator_exponentialToLogistic p v.num hv.2.1,
      logisticNumerator_eval_neg_one] at hn
    exact (mul_ne_zero_iff.mp hn).1
  have hdeg : B.natDegree = p :=
    natDegree_eq_of_le_of_coeff_ne_zero (exponentialToLogistic_natDegree_le p v.num) htop
  refine ⟨B, ⟨hdeg, ?_, he⟩, ?_⟩
  · change (exponentialToLogistic p v.num).coeff 0 = 0
    rw [exponentialToLogistic_coeff_zero, coeff_zero_eq_eval_zero]
    exact hv.2.2
  · intro C hC
    apply logistic_aeval_injective
    exact hC.2.2.trans he.symm

end PolynomialRigidity.Enumeration
