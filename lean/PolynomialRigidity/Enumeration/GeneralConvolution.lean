import PolynomialRigidity.Enumeration.InverseLogistic

/-!
# The convolution transform over general coefficient rings

The rational monomial-kernel identities descend from the checked complex
identity and then extend by bilinearity to every characteristic-zero domain
which is a rational algebra. This includes the universal parameter rings.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

theorem logisticTransform_discreteMonomial (i j : ℕ) :
    logisticTransform (discreteMonomial i j) =
      -logisticBasis (R := ℚ) i * logisticBasis j := by
  apply Polynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
  rw [logisticTransform_map, Polynomial.map_mul, Polynomial.map_neg, logisticBasis_map, logisticBasis_map]
  have h := logisticTransform_discreteConvolution (monomial i (1 : ℂ)) (monomial j (1 : ℂ))
  simpa only [discreteConvolution_monomial_monomial, one_mul, C_1,
    logisticTransform_monomial, one_smul] using h

section Domains

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R] [Algebra ℚ R]

theorem logisticTransform_discreteConvolution_general (A B : R[X]) :
    logisticTransform (discreteConvolution A B) = -logisticTransform A * logisticTransform B := by
  induction A using Polynomial.induction_on' generalizing B with
  | add A₁ A₂ h₁ h₂ =>
    rw [discreteConvolution_add_left, map_add, h₁ B, h₂ B, map_add]
    ring
  | monomial i a =>
    induction B using Polynomial.induction_on' with
    | add B₁ B₂ h₁ h₂ =>
      rw [discreteConvolution_add_right, map_add, h₁, h₂, map_add]
      ring
    | monomial j b =>
      rw [discreteConvolution_monomial_monomial, logisticTransform_C_mul,
        ← logisticTransform_map (algebraMap ℚ R), logisticTransform_discreteMonomial,
        Polynomial.map_mul, Polynomial.map_neg, logisticBasis_map, logisticBasis_map,
        logisticTransform_monomial, logisticTransform_monomial]
      simp only [smul_eq_C_mul, map_mul]
      ring

theorem discreteConvolution_comm_general (A B : R[X]) : discreteConvolution A B = discreteConvolution B A := by
  apply logisticTransform_injective
  rw [logisticTransform_discreteConvolution_general, logisticTransform_discreteConvolution_general]
  ring

theorem discreteConvolution_C_mul_left (F G : R[X]) (c : R) :
    discreteConvolution (C c * F) G = C c * discreteConvolution F G := by
  rw [discreteConvolution_comm_general, discreteConvolution_C_mul_right,
    discreteConvolution_comm_general G F]

end Domains

section RationalAlgebras

variable {R : Type*} [CommRing R] [Algebra ℚ R]

def inverseLogisticScalar (n : ℕ) : R :=
  algebraMap ℚ R (((-1 : ℚ) ^ n * (n.factorial : ℚ))⁻¹)

theorem inverseLogisticScalar_mul (n : ℕ) :
    inverseLogisticScalar (R := R) n * ((-1 : R) ^ n * (n.factorial : R)) = 1 := by
  have hmap : algebraMap ℚ R ((-1 : ℚ) ^ n * (n.factorial : ℚ)) =
      (-1 : R) ^ n * (n.factorial : R) := by
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  rw [inverseLogisticScalar, ← hmap, ← map_mul,
    inv_mul_cancel₀ (logisticBasisScalar_ne_zero (K := ℚ) n), map_one]

/-- The inverse transform expressed by rational scalars, so it also makes sense in parameter rings. -/
def rationalInverseLogisticTransform (B : R[X]) : R[X] :=
  ∑ n ∈ range B.natDegree, C (B.coeff (n + 1) * inverseLogisticScalar n) * spectralBasis n

theorem logisticTransform_rationalInverse (B : R[X]) (hB : B.coeff 0 = 0) :
    logisticTransform (rationalInverseLogisticTransform B) = B := by
  rw [rationalInverseLogisticTransform, map_sum]
  simp_rw [logisticTransform_C_mul, logisticTransform_spectralBasis]
  calc
    _ = ∑ n ∈ range B.natDegree, C (B.coeff (n + 1)) * X ^ (n + 1) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← mul_assoc, ← C_mul, mul_assoc, inverseLogisticScalar_mul, mul_one]
    _ = B := by
      conv_rhs => rw [B.as_sum_range_C_mul_X_pow, Finset.sum_range_succ']
      simp only [hB, C_0, zero_mul, add_zero]

end RationalAlgebras

section Domains

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R] [Algebra ℚ R]

theorem rationalInverse_logisticTransform (A : R[X]) :
    rationalInverseLogisticTransform (logisticTransform A) = A := by
  apply logisticTransform_injective
  exact logisticTransform_rationalInverse _ (logisticTransform_coeff_zero A)

theorem discreteConvolution_eq_rationalInverse (A B : R[X]) :
    discreteConvolution A B =
      rationalInverseLogisticTransform (-logisticTransform A * logisticTransform B) := by
  rw [← logisticTransform_discreteConvolution_general, rationalInverse_logisticTransform]

end Domains

theorem rationalInverse_eq_inverse {K : Type*} [Field K] [CharZero K] (B : K[X]) :
    rationalInverseLogisticTransform B = inverseLogisticTransform B := by
  simp only [rationalInverseLogisticTransform, inverseLogisticTransform, inverseLogisticScalar,
    div_eq_mul_inv, map_inv₀, map_mul, map_pow, map_neg, map_one, map_natCast]

theorem discreteConvolution_eq_inverse_general {K : Type*} [Field K] [CharZero K] (A B : K[X]) :
    discreteConvolution A B = inverseLogisticTransform (-logisticTransform A * logisticTransform B) := by
  rw [discreteConvolution_eq_rationalInverse, rationalInverse_eq_inverse]

end PolynomialRigidity.Enumeration
