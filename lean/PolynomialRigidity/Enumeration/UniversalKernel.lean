import PolynomialRigidity.Enumeration.GeneralConvolution
import PolynomialRigidity.Prime

/-!
# A denominator-cleared convolution formula in parameter rings

Only rational scalar inverses occur. The formula therefore applies to the
universal coefficient ring, rather than requiring its fraction field.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

theorem normalized_top_scalar_rat (d : ℕ) :
    ((2 * d + 1 : ℕ) : ℚ) * (-(d.factorial : ℚ) ^ 2) * inverseLogisticScalar (R := ℚ) (2 * d + 1) =
      (d.factorial : ℚ) ^ 2 / ((2 * d).factorial : ℚ) := by
  have hsign : (-1 : ℚ) ^ (2 * d + 1) = -1 := by simp [pow_add, pow_mul]
  have ht : (-(d.factorial : ℚ) ^ 2) * inverseLogisticScalar (R := ℚ) (2 * d + 1) =
      beta (K := ℚ) d d := by
    simp only [inverseLogisticScalar, Algebra.algebraMap_self, RingHom.id_apply, hsign]
    simp [beta, pow_two, two_mul, div_eq_mul_inv]
  rw [mul_assoc, ht]
  simpa only [pow_two] using (PolynomialRigidity.prime_mul_beta_self (K := ℚ) d)

theorem normalized_top_scalar (R : Type*) [CommRing R] [Algebra ℚ R] (d : ℕ) :
    ((2 * d + 1 : ℕ) : R) * (-(d.factorial : R) ^ 2) * inverseLogisticScalar (R := R) (2 * d + 1) =
      algebraMap ℚ R ((d.factorial : ℚ) ^ 2 / ((2 * d).factorial : ℚ)) := by
  have h := congrArg (algebraMap ℚ R) (normalized_top_scalar_rat d)
  simpa only [inverseLogisticScalar, Algebra.algebraMap_self, RingHom.id_apply,
    map_mul, map_neg, map_pow, map_natCast] using h

theorem normalizedConvolution_universal_formula {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] [Algebra ℚ R] {A : R[X]} (hA : A.Monic) :
    C ((2 * A.natDegree + 1 : ℕ) : R) * discreteConvolution A A =
      C (algebraMap ℚ R ((A.natDegree.factorial : ℚ) ^ 2 / ((2 * A.natDegree).factorial : ℚ))) *
        spectralBasis (2 * A.natDegree + 1) +
      C ((2 * A.natDegree + 1 : ℕ) : R) *
        ∑ n ∈ range (2 * A.natDegree + 1),
          C ((-logisticTransform A * logisticTransform A).coeff (n + 1) * inverseLogisticScalar n) *
            spectralBasis n := by
  have hT : logisticTransform A ≠ 0 := by
    intro hz
    apply hA.ne_zero
    apply logisticTransform_injective
    simpa only [map_zero] using hz
  have hd : (-logisticTransform A * logisticTransform A).natDegree = 2 * A.natDegree + 1 + 1 := by
    rw [natDegree_mul (neg_ne_zero.mpr hT) hT, natDegree_neg, logisticTransform_natDegree hA.ne_zero]
    omega
  have hcT : (logisticTransform A).coeff (A.natDegree + 1) =
      (-1 : R) ^ A.natDegree * (A.natDegree.factorial : R) := by
    simpa only [hA.leadingCoeff, one_mul] using logisticTransform_top_coeff A
  have hc : (-logisticTransform A * logisticTransform A).coeff (2 * A.natDegree + 1 + 1) =
      -(A.natDegree.factorial : R) ^ 2 := by
    rw [show 2 * A.natDegree + 1 + 1 = (A.natDegree + 1) + (A.natDegree + 1) by omega]
    rw [coeff_mul_add_eq_of_natDegree_le
      (by rw [natDegree_neg, logisticTransform_natDegree hA.ne_zero])
      (by rw [logisticTransform_natDegree hA.ne_zero])]
    simp only [coeff_neg, hcT]
    rcases neg_one_pow_eq_or R A.natDegree with hs | hs <;> simp [hs, pow_two]
  have htop : C ((2 * A.natDegree + 1 : ℕ) : R) *
      (C ((-logisticTransform A * logisticTransform A).coeff (2 * A.natDegree + 1 + 1) *
          inverseLogisticScalar (R := R) (2 * A.natDegree + 1)) * spectralBasis (2 * A.natDegree + 1)) =
      C (algebraMap ℚ R ((A.natDegree.factorial : ℚ) ^ 2 / ((2 * A.natDegree).factorial : ℚ))) *
        spectralBasis (2 * A.natDegree + 1) := by
    rw [← mul_assoc, ← C_mul, hc, ← mul_assoc, normalized_top_scalar]
  rw [discreteConvolution_eq_rationalInverse, rationalInverseLogisticTransform, hd,
    Finset.sum_range_succ, mul_add, htop]
  exact add_comm _ _

end PolynomialRigidity.Enumeration
