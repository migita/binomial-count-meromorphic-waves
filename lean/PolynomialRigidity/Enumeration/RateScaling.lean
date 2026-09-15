import PolynomialRigidity.Enumeration.PrimeReduction

/-!
# Scaling at a root and integrality of every complex matching solution

Scaling the input roots also scales the logistic and falling-factorial
bases. At a root whose valuation is greater than one, the scaled rate is
in the maximal ideal, so the surviving spectral factor evaluates to a unit
at the normalised root 1.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

section ScalingIdentities

variable {K : Type*} [Field K] [CharZero K]

theorem logisticBasis_natDegree (n : ℕ) : (logisticBasis (R := K) n).natDegree = n + 1 :=
  natDegree_eq_of_le_of_coeff_ne_zero (logisticBasis_natDegree_le n)
    (by rw [logisticBasis_top_coeff]; exact logisticBasisScalar_ne_zero n)

omit [CharZero K] in
theorem logisticTransform_apply_range (A : K[X]) :
    logisticTransform A = ∑ i ∈ range (A.natDegree + 1), C (A.coeff i) * logisticBasis i := by
  rw [logisticTransform_apply]
  change A.sum (fun i c => C c * logisticBasis i) = _
  exact Polynomial.sum_over_range A (by intro i; simp)

def rateLogisticTransform (A : K[X]) (s : K) : K[X] :=
  ∑ i ∈ range (A.natDegree + 1), C (A.coeff i) * (logisticBasis i).scaleRoots s

theorem rateLogisticTransform_scaleRoots (A : K[X]) (s : K) (hA : A ≠ 0) :
    rateLogisticTransform (A.scaleRoots s) s = (logisticTransform A).scaleRoots s := by
  ext n
  rw [coeff_scaleRoots, logisticTransform_natDegree hA, logisticTransform_apply_range, finsetSum_coeff]
  simp only [rateLogisticTransform, natDegree_scaleRoots, finsetSum_coeff, coeff_C_mul,
    coeff_scaleRoots, logisticBasis_natDegree]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ A.natDegree := by simpa using hi
  by_cases hn : n ≤ i + 1
  · have hp : s ^ (A.natDegree - i) * s ^ (i + 1 - n) = s ^ (A.natDegree + 1 - n) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      _ = (A.coeff i * (logisticBasis (R := K) i).coeff n) *
          (s ^ (A.natDegree - i) * s ^ (i + 1 - n)) := by ring
      _ = _ := by rw [hp]
  · have hz : (logisticBasis (R := K) i).coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt ((logisticBasis_natDegree_le i).trans_lt (Nat.lt_of_not_ge hn))
    simp only [hz, zero_mul, mul_zero]

omit [CharZero K] in
theorem neg_scaleRoots_eq (F : K[X]) (s : K) : (-F).scaleRoots s = -(F.scaleRoots s) := by
  ext n
  simp only [coeff_scaleRoots, coeff_neg, natDegree_neg, neg_mul]

def rateInverseLogisticTransform (B : K[X]) (s : K) : K[X] :=
  ∑ n ∈ range B.natDegree,
    C (B.coeff (n + 1) / ((-1 : K) ^ n * (n.factorial : K))) * (spectralBasis n).scaleRoots s

theorem rateInverse_scaleRoots_eval (B : K[X]) (s r : K) :
    (rateInverseLogisticTransform (B.scaleRoots s) s).eval (s * r) =
      s ^ (B.natDegree - 1) * (inverseLogisticTransform B).eval r := by
  simp only [rateInverseLogisticTransform, inverseLogisticTransform, natDegree_scaleRoots,
    eval_finsetSum, eval_mul, eval_C, scaleRoots_eval_mul, spectralBasis_natDegree, coeff_scaleRoots]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : n < B.natDegree := Finset.mem_range.mp hn
  have hp : s ^ (B.natDegree - (n + 1)) * s ^ n = s ^ (B.natDegree - 1) := by
    rw [← pow_add]
    congr 1
    omega
  simp only [div_eq_mul_inv]
  calc
    _ = (s ^ (B.natDegree - (n + 1)) * s ^ n) *
        (B.coeff (n + 1) * (((-1 : K) ^ n * (n.factorial : K))⁻¹) * (spectralBasis n).eval r) := by ring
    _ = _ := by rw [hp]

def rateInverseTail (ℓ : ℕ) (B : K[X]) (s : K) : K[X] :=
  ∑ n ∈ range ℓ,
    C (B.coeff (n + 1) / ((-1 : K) ^ n * (n.factorial : K))) * (spectralBasis n).scaleRoots s

omit [CharZero K] in
theorem normalizedRateInverse_eq (d : ℕ) (B : K[X]) (s : K)
    (hdegree : B.natDegree = 2 * d + 1 + 1) (hlead : B.leadingCoeff = -(d.factorial : K) ^ 2) :
    C ((2 * d + 1 : ℕ) : K) * rateInverseLogisticTransform B s =
      C (((2 * d + 1 : ℕ) : K) * beta d d) * (spectralBasis (2 * d + 1)).scaleRoots s +
        C ((2 * d + 1 : ℕ) : K) * rateInverseTail (2 * d + 1) B s := by
  have hsign : (-1 : K) ^ (2 * d + 1) = -1 := by simp [pow_add, pow_mul]
  have htop : B.coeff (2 * d + 1 + 1) /
      ((-1 : K) ^ (2 * d + 1) * ((2 * d + 1).factorial : K)) = beta d d := by
    rw [← hdegree, coeff_natDegree, hlead]
    rw [hsign]
    simp [beta, pow_two, two_mul]
  rw [rateInverseLogisticTransform, hdegree, Finset.sum_range_succ, htop,
    mul_add, ← mul_assoc, ← C_mul]
  exact add_comm _ _

end ScalingIdentities

section IntegralRates

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem rateLogisticTransform_integral (V : ValuationSubring K) {A : K[X]} {s : K}
    (hA : IntegralCoefficients V A) (hs : s ∈ V) : IntegralCoefficients V (rateLogisticTransform A s) :=
  IntegralCoefficients.sum _ _ (fun i _hi =>
    (IntegralCoefficients.C (hA i)).mul ((IntegralCoefficients.logisticBasis i).scaleRoots hs))

omit [CharZero K] in
theorem rateInverseTail_integral (V : ValuationSubring K) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hv : V.valuation (ℓ : K) < 1) {B : K[X]} {s : K}
    (hB : IntegralCoefficients V B) (hs : s ∈ V) : IntegralCoefficients V (rateInverseTail ℓ B s) := by
  apply IntegralCoefficients.sum
  intro n hn
  apply IntegralCoefficients.mul
  · apply IntegralCoefficients.C
    rw [div_eq_mul_inv]
    exact V.toSubring.mul_mem (hB (n + 1))
      (inverseLogisticBasisScalar_mem V hℓ hv (Finset.mem_range.mp hn))
  · exact (IntegralCoefficients.spectralBasis n).scaleRoots hs

omit [CharZero K] in
theorem spectralBasis_scaled_eval_unit (V : ValuationSubring K) {s : K}
    (hs : V.valuation s < 1) (n : ℕ) :
    V.valuation (((spectralBasis (R := K) n).scaleRoots s).eval 1) = 1 := by
  have hfactor (j : ℕ) : V.valuation (1 - (j : K) * s) = 1 := by
    have hj : V.valuation (j : K) ≤ 1 := (V.valuation_le_one_iff _).mpr (natCast_mem V j)
    have hsmall : V.valuation ((j : K) * s) < 1 := by
      rw [map_mul]
      exact (mul_le_mul_of_nonneg_right hj zero_le).trans_lt (by simpa only [one_mul] using hs)
    simpa only [map_one] using
      V.valuation.map_sub_eq_of_lt_left (x := 1) (by simpa only [map_one] using hsmall)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [spectralBasis_succ, mul_scaleRoots_of_noZeroDivisors, X_sub_C_scaleRoots,
      eval_mul, eval_sub, eval_X, eval_C, map_mul, hfactor, ih, one_mul]

/-- The normalised prime term cannot vanish at 1 when the rate is in the maximal ideal. -/
theorem rateInverse_eval_one_ne_zero (V : ValuationSubring K) {d : ℕ} {B : K[X]} {s : K}
    (hℓ : (2 * d + 1).Prime) (hv : V.valuation ((2 * d + 1 : ℕ) : K) < 1)
    (hB : IntegralCoefficients V B) (hdegree : B.natDegree = 2 * d + 1 + 1)
    (hlead : B.leadingCoeff = -(d.factorial : K) ^ 2) (hs : V.valuation s < 1) :
    (rateInverseLogisticTransform B s).eval 1 ≠ 0 := by
  have hsV := (V.valuation_le_one_iff _).mp hs.le
  have htail : V.valuation ((rateInverseTail (2 * d + 1) B s).eval 1) ≤ 1 :=
    (V.valuation_le_one_iff _).mpr ((rateInverseTail_integral V hℓ hv hB hsV).eval V.one_mem)
  have htop : V.valuation ((((2 * d + 1 : ℕ) : K) * beta d d) *
      ((spectralBasis (2 * d + 1)).scaleRoots s).eval 1) = 1 := by
    rw [map_mul, PolynomialRigidity.valuation_prime_mul_beta_self V hℓ hv,
      spectralBasis_scaled_eval_unit V hs, one_mul]
  have hsmall : V.valuation (((2 * d + 1 : ℕ) : K) * (rateInverseTail (2 * d + 1) B s).eval 1) < 1 := by
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_left htail zero_le).trans_lt (by simpa only [mul_one] using hv)
  have he : ((2 * d + 1 : ℕ) : K) * (rateInverseLogisticTransform B s).eval 1 =
      (((2 * d + 1 : ℕ) : K) * beta d d) * ((spectralBasis (2 * d + 1)).scaleRoots s).eval 1 +
        ((2 * d + 1 : ℕ) : K) * (rateInverseTail (2 * d + 1) B s).eval 1 := by
    simpa only [eval_mul, eval_add, eval_C] using
      congrArg (Polynomial.eval 1) (normalizedRateInverse_eq d B s hdegree hlead)
  have hsum := V.valuation.map_add_eq_of_lt_left
    (x := (((2 * d + 1 : ℕ) : K) * beta d d) * ((spectralBasis (2 * d + 1)).scaleRoots s).eval 1)
    (y := ((2 * d + 1 : ℕ) : K) * (rateInverseTail (2 * d + 1) B s).eval 1)
    (by rw [htop]; exact hsmall)
  rw [htop] at hsum
  intro hz
  rw [← he, hz, mul_zero, map_zero] at hsum
  exact zero_ne_one hsum

end IntegralRates

/-- Every complex monic matching polynomial is integral at the prime index. -/
theorem monic_matching_integral (V : ValuationSubring ℂ) {A : ℂ[X]} (hA : A.Monic)
    (hℓ : (2 * A.natDegree + 1).Prime)
    (hv : V.valuation ((2 * A.natDegree + 1 : ℕ) : ℂ) < 1)
    (hdiv : A ∣ discreteConvolution A A) : IntegralCoefficients V A := by
  classical
  have hsplit := IsAlgClosed.splits A
  have hroots : ∀ r ∈ A.roots, V.valuation r ≤ 1 := by
    intro r hr
    by_contra hle
    have hrbig : 1 < V.valuation r := lt_of_not_ge hle
    have hne : A.roots ≠ 0 := by intro hz; simp [hz] at hr
    obtain ⟨m, hm, hmax⟩ := Multiset.exists_max_image V.valuation hne
    have hmbig : 1 < V.valuation m := hrbig.trans_le (hmax r hr)
    have hmpos : 0 < V.valuation m := zero_lt_one.trans hmbig
    have hm0 : m ≠ 0 := V.valuation.pos_iff.mp hmpos
    have hs : V.valuation m⁻¹ < 1 := by
      rw [map_inv₀]
      exact (inv_lt_one₀ hmpos).mpr hmbig
    have hsV := (V.valuation_le_one_iff _).mp hs.le
    have hAI : IntegralCoefficients V (A.scaleRoots m⁻¹) :=
      (integralCoefficients_iff_valuation V _).mpr
        (valuation_coeff_scaleRoots_le_one V hA hsplit hm0 hmax)
    have hTI : IntegralCoefficients V ((logisticTransform A).scaleRoots m⁻¹) := by
      rw [← rateLogisticTransform_scaleRoots A m⁻¹ hA.ne_zero]
      exact rateLogisticTransform_integral V hAI hsV
    let B := -logisticTransform A * logisticTransform A
    let Bₛ := B.scaleRoots m⁻¹
    have hBI : IntegralCoefficients V Bₛ := by
      dsimp only [Bₛ, B]
      rw [mul_scaleRoots_of_noZeroDivisors, neg_scaleRoots_eq]
      exact hTI.neg.mul hTI
    have hT : logisticTransform A ≠ 0 := by
      intro hz
      apply hA.ne_zero
      apply logisticTransform_injective
      simpa only [map_zero] using hz
    have hBdegree : Bₛ.natDegree = 2 * A.natDegree + 1 + 1 := by
      dsimp only [Bₛ, B]
      rw [natDegree_scaleRoots, natDegree_mul (neg_ne_zero.mpr hT) hT, natDegree_neg,
        logisticTransform_natDegree hA.ne_zero]
      omega
    have hTlead : (logisticTransform A).leadingCoeff =
        (-1 : ℂ) ^ A.natDegree * (A.natDegree.factorial : ℂ) := by
      simpa only [hA.leadingCoeff, one_mul] using logisticTransform_leadingCoeff hA.ne_zero
    have hBlead : Bₛ.leadingCoeff = -(A.natDegree.factorial : ℂ) ^ 2 := by
      dsimp only [Bₛ, B]
      rw [leadingCoeff_scaleRoots, leadingCoeff_mul, leadingCoeff_neg, hTlead]
      rcases neg_one_pow_eq_or ℂ A.natDegree with hsgn | hsgn <;> simp [hsgn, pow_two]
    have hnonzero := rateInverse_eval_one_ne_zero V hℓ hv hBI hBdegree hBlead hs
    have hAm : A.eval m = 0 := (Polynomial.mem_roots hA.ne_zero).mp hm
    have hSm : (discreteConvolution A A).eval m = 0 := by
      obtain ⟨Q, hQ⟩ := hdiv
      rw [hQ, eval_mul, hAm, zero_mul]
    have hi : inverseLogisticTransform B = discreteConvolution A A :=
      (discreteConvolution_eq_inverse_general A A).symm
    have he := rateInverse_scaleRoots_eval B m⁻¹ m
    rw [inv_mul_cancel₀ hm0, hi, hSm, mul_zero] at he
    exact hnonzero he
  exact (integralCoefficients_iff_valuation V A).mpr (valuation_coeff_le_one V hA hsplit hroots)

end PolynomialRigidity.Enumeration
