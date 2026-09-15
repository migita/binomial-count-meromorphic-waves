import PolynomialRigidity.Enumeration.InverseLogistic

/-!
# Degrees and leading coefficients in the discrete matching problem

The logistic transform raises degree by one and turns discrete convolution
into negative multiplication. This gives the exact degree and beta leading
coefficient, including the normalisation of the candidate ODE operator.
-/

noncomputable section

open Polynomial

namespace PolynomialRigidity.Enumeration

theorem beta_ne_zero {K : Type*} [Field K] [CharZero K] (i j : ℕ) :
    beta (K := K) i j ≠ 0 :=
  div_ne_zero
    (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

theorem logisticTransform_ne_zero {K : Type*} [Field K] [CharZero K] {A : K[X]} (hA : A ≠ 0) :
    logisticTransform A ≠ 0 := by
  intro hz
  have hc := logisticTransform_top_coeff_ne_zero hA
  rw [hz, coeff_zero] at hc
  exact hc rfl

theorem discreteConvolution_ne_zero {A B : ℂ[X]} (hA : A ≠ 0) (hB : B ≠ 0) :
    discreteConvolution A B ≠ 0 := by
  intro hzero
  have h := logisticTransform_discreteConvolution A B
  rw [hzero, map_zero] at h
  exact (mul_ne_zero (neg_ne_zero.mpr (logisticTransform_ne_zero hA))
    (logisticTransform_ne_zero hB)) h.symm

theorem discreteConvolution_natDegree {A B : ℂ[X]} (hA : A ≠ 0) (hB : B ≠ 0) :
    (discreteConvolution A B).natDegree = A.natDegree + B.natDegree + 1 := by
  have h := congrArg Polynomial.natDegree (logisticTransform_discreteConvolution A B)
  rw [logisticTransform_natDegree (discreteConvolution_ne_zero hA hB),
    natDegree_mul (neg_ne_zero.mpr (logisticTransform_ne_zero hA)) (logisticTransform_ne_zero hB),
    natDegree_neg, logisticTransform_natDegree hA, logisticTransform_natDegree hB] at h
  omega

theorem discreteConvolution_leadingCoeff {A B : ℂ[X]} (hA : A ≠ 0) (hB : B ≠ 0) :
    (discreteConvolution A B).leadingCoeff =
      A.leadingCoeff * B.leadingCoeff * beta A.natDegree B.natDegree := by
  have h := congrArg Polynomial.leadingCoeff (logisticTransform_discreteConvolution A B)
  rw [logisticTransform_leadingCoeff (discreteConvolution_ne_zero hA hB),
    leadingCoeff_mul, leadingCoeff_neg,
    logisticTransform_leadingCoeff hA, logisticTransform_leadingCoeff hB,
    discreteConvolution_natDegree hA hB] at h
  unfold beta
  rw [← mul_div_assoc]
  apply (eq_div_iff (Nat.cast_ne_zero.mpr
    (Nat.factorial_ne_zero (A.natDegree + B.natDegree + 1)))).mpr
  have hsign : (-1 : ℂ) ^ A.natDegree * (-1 : ℂ) ^ B.natDegree ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  apply mul_right_cancel₀ hsign
  simp only [pow_succ, pow_add] at h
  linear_combination -h

theorem candidateOperator_natDegree {p : ℕ} (hp : 2 ≤ p) (a : Coefficients p) :
    (candidateOperator p a).natDegree = p := by
  have hA := (coefficientPolynomial_monic p a).ne_zero
  rw [candidateOperator, natDegree_C_mul (inv_ne_zero (beta_ne_zero _ _)),
    natDegree_divByMonic _ (coefficientPolynomial_monic p a),
    discreteConvolution_natDegree hA hA, coefficientPolynomial_natDegree]
  omega

theorem candidateOperator_monic (p : ℕ) (a : Coefficients p) :
    (candidateOperator p a).Monic := by
  have hA := (coefficientPolynomial_monic p a).ne_zero
  have hS := discreteConvolution_ne_zero hA hA
  have hdeg : (coefficientPolynomial p a).degree ≤
      (discreteConvolution (coefficientPolynomial p a) (coefficientPolynomial p a)).degree := by
    rw [degree_eq_natDegree hS]
    apply degree_le_of_natDegree_le
    rw [discreteConvolution_natDegree hA hA]
    omega
  unfold candidateOperator
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [leadingCoeff_divByMonic_of_monic (coefficientPolynomial_monic p a) hdeg,
    discreteConvolution_leadingCoeff hA hA, (coefficientPolynomial_monic p a).leadingCoeff,
    one_mul, one_mul, coefficientPolynomial_natDegree, inv_mul_cancel₀ (beta_ne_zero _ _)]

theorem profileScale_ne_zero (p : ℕ) : profileScale p ≠ 0 :=
  div_ne_zero (by norm_num) (beta_ne_zero _ _)

theorem candidateProfile_ne_zero (p : ℕ) (a : Coefficients p) : candidateProfile p a ≠ 0 := by
  unfold candidateProfile
  apply mul_ne_zero
  · simpa only [map_zero] using (algebraMap ℂ RationalFunction).injective.ne (profileScale_ne_zero p)
  · intro hzero
    apply (coefficientPolynomial_monic p a).ne_zero
    apply applyOperator_logistic_injective
    simpa only [applyOperator_zero] using hzero

end PolynomialRigidity.Enumeration
