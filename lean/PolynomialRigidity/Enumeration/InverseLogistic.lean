import PolynomialRigidity.Enumeration.LogisticPolynomial

/-!
# The inverse logistic operator transform

The falling-factorial operators map to scalar powers of the logistic
coordinate. Their factorial denominators are also the denominators that
control the prime reduction of the discrete convolution.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

section IntegralBasis

variable {R : Type*} [CommRing R]

/-- `(X-1)⋯(X-n)`, the operator for the `(n+1)`st logistic power. -/
def spectralBasis (n : ℕ) : R[X] :=
  ∏ j ∈ Finset.Ico 1 (n + 1), (X - C (j : R))

@[simp]
theorem spectralBasis_zero : spectralBasis (R := R) 0 = 1 := by simp [spectralBasis]

theorem spectralBasis_succ (n : ℕ) :
    spectralBasis (R := R) (n + 1) = (X - C ((n + 1 : ℕ) : R)) * spectralBasis n := by
  rw [spectralBasis, Finset.prod_Ico_succ_top (by omega : 1 ≤ n + 1)]
  exact mul_comm _ _

theorem spectralBasis_monic (n : ℕ) : (spectralBasis (R := R) n).Monic :=
  monic_prod_X_sub_C (fun j : ℕ => (j : R)) _

theorem spectralBasis_map {S : Type*} [CommRing S] (f : R →+* S) (n : ℕ) :
    (spectralBasis (R := R) n).map f = spectralBasis (R := S) n := by
  simp only [spectralBasis, Polynomial.map_prod, Polynomial.map_sub, map_X,
    map_natCast, Polynomial.map_natCast]

@[simp]
theorem spectralBasis_natDegree [Nontrivial R] (n : ℕ) :
    (spectralBasis (R := R) n).natDegree = n := by
  rw [spectralBasis, natDegree_finsetProd_X_sub_C_eq_card]
  simp

@[simp]
theorem logisticTransform_one : logisticTransform (R := R) 1 = X := by
  simpa using logisticTransform_monomial (R := R) 0 1

/-- An integral identity, valid in every characteristic. -/
theorem logisticTransform_spectralBasis (n : ℕ) :
    logisticTransform (spectralBasis (R := R) n) =
      C ((-1 : R) ^ n * (n.factorial : R)) * X ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [spectralBasis_succ, sub_mul, map_sub, logisticTransform_X_mul,
      logisticTransform_C_mul, ih]
    simp only [logisticDelta, LinearMap.coe_mk, AddHom.coe_mk]
    rw [derivative_C_mul, derivative_X_pow]
    simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, map_mul, map_pow, map_neg, map_one, map_add,
      C_eq_natCast, pow_succ]
    ring

end IntegralBasis

section Inverse

variable {K : Type*} [Field K] [CharZero K]

theorem logisticBasisScalar_ne_zero (n : ℕ) : (-1 : K) ^ n * (n.factorial : K) ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

/-- The operator polynomial associated to a logistic polynomial with zero constant coefficient. -/
def inverseLogisticTransform (B : K[X]) : K[X] :=
  ∑ n ∈ range B.natDegree,
    C (B.coeff (n + 1) / ((-1 : K) ^ n * (n.factorial : K))) * spectralBasis n

theorem logisticTransform_inverseLogisticTransform (B : K[X]) (hB : B.coeff 0 = 0) :
    logisticTransform (inverseLogisticTransform B) = B := by
  rw [inverseLogisticTransform, map_sum]
  simp_rw [logisticTransform_C_mul, logisticTransform_spectralBasis]
  calc
    _ = ∑ n ∈ range B.natDegree, C (B.coeff (n + 1)) * X ^ (n + 1) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← mul_assoc, ← C_mul, div_mul_cancel₀ _ (logisticBasisScalar_ne_zero n)]
    _ = B := by
      conv_rhs => rw [B.as_sum_range_C_mul_X_pow, Finset.sum_range_succ']
      simp only [hB, C_0, zero_mul, add_zero]

@[simp]
theorem inverseLogisticTransform_logisticTransform (A : K[X]) :
    inverseLogisticTransform (logisticTransform A) = A := by
  apply logisticTransform_injective
  exact logisticTransform_inverseLogisticTransform _ (logisticTransform_coeff_zero A)

theorem inverseLogisticTransform_ne_zero {B : K[X]} (hB : B.coeff 0 = 0) (hB0 : B ≠ 0) :
    inverseLogisticTransform B ≠ 0 := by
  intro hz
  have h := logisticTransform_inverseLogisticTransform B hB
  rw [hz, map_zero] at h
  exact hB0 h.symm

theorem inverseLogisticTransform_natDegree {B : K[X]} (hB : B.coeff 0 = 0) (hB0 : B ≠ 0) :
    (inverseLogisticTransform B).natDegree + 1 = B.natDegree := by
  rw [← logisticTransform_natDegree (inverseLogisticTransform_ne_zero hB hB0),
    logisticTransform_inverseLogisticTransform B hB]

theorem logisticTransform_leadingCoeff {A : K[X]} (hA : A ≠ 0) :
    (logisticTransform A).leadingCoeff =
      A.leadingCoeff * ((-1 : K) ^ A.natDegree * (A.natDegree.factorial : K)) := by
  rw [leadingCoeff, logisticTransform_natDegree hA, logisticTransform_top_coeff]

/-- The explicit inverse also recovers the whole discrete convolution. -/
theorem discreteConvolution_eq_inverse (A B : ℂ[X]) :
    discreteConvolution A B =
      inverseLogisticTransform (-logisticTransform A * logisticTransform B) := by
  rw [← logisticTransform_discreteConvolution, inverseLogisticTransform_logisticTransform]

end Inverse

end PolynomialRigidity.Enumeration
