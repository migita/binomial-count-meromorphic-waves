import PolynomialRigidity.Enumeration.LogisticIdentity
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Polynomial logistic coordinates

The polynomial derivation `q(1-q)∂q` models the specified rational derivative.
Its iterates on `q` have integral coefficients and leading coefficient
`(-1)^n n!`. This provides the degree control and the integral operator basis
used by the prime reduction.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

section PolynomialCalculus

variable {R : Type*} [CommRing R]

def logisticDelta : R[X] →ₗ[R] R[X] where
  toFun F := X * (1 - X) * F.derivative
  map_add' F G := by simp only [derivative_add, mul_add]
  map_smul' c F := by simp only [derivative_smul, mul_smul_comm, RingHom.id_apply]

def logisticBasis (n : ℕ) : R[X] := (logisticDelta^[n]) X

@[simp]
theorem logisticBasis_zero : logisticBasis (R := R) 0 = X := rfl

theorem logisticBasis_succ (n : ℕ) :
    logisticBasis (R := R) (n + 1) = logisticDelta (logisticBasis n) :=
  Function.iterate_succ_apply' _ _ _

@[simp]
theorem logisticDelta_coeff_zero (F : R[X]) : (logisticDelta F).coeff 0 = 0 := by
  simp [logisticDelta]

theorem logisticDelta_coeff_succ (F : R[X]) (n : ℕ) :
    (logisticDelta F).coeff (n + 1) =
      F.coeff (n + 1) * (n + 1 : R) - F.coeff n * (n : R) := by
  have he : logisticDelta F = X * F.derivative - X * (X * F.derivative) := by
    simp only [logisticDelta, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  rw [he, coeff_sub, coeff_X_mul, coeff_X_mul]
  cases n with
  | zero => simp [coeff_derivative]
  | succ n => simp [coeff_X_mul, coeff_derivative, Nat.cast_add, Nat.cast_one]

theorem logisticDelta_natDegree_le (F : R[X]) :
    (logisticDelta F).natDegree ≤ F.natDegree + 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro N hN
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  rw [logisticDelta_coeff_succ,
    coeff_eq_zero_of_natDegree_lt (by omega : F.natDegree < n + 1),
    coeff_eq_zero_of_natDegree_lt (by omega : F.natDegree < n)]
  simp

theorem logisticBasis_natDegree_le (n : ℕ) :
    (logisticBasis (R := R) n).natDegree ≤ n + 1 := by
  induction n with
  | zero => exact natDegree_X_le
  | succ n ih =>
    rw [logisticBasis_succ]
    exact (logisticDelta_natDegree_le _).trans (Nat.add_le_add_right ih 1)

theorem logisticBasis_top_coeff (n : ℕ) :
    (logisticBasis (R := R) n).coeff (n + 1) = (-1 : R) ^ n * (n.factorial : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [logisticBasis_succ, logisticDelta_coeff_succ,
      coeff_eq_zero_of_natDegree_lt ((logisticBasis_natDegree_le n).trans_lt (by omega)), ih]
    simp only [zero_mul, zero_sub, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, pow_succ]
    ring

@[simp]
theorem logisticBasis_coeff_zero (n : ℕ) : (logisticBasis (R := R) n).coeff 0 = 0 := by
  cases n with
  | zero => simp
  | succ n => rw [logisticBasis_succ, logisticDelta_coeff_zero]

/-- The linear polynomial map `A ↦ A(q(1-q)∂q)q`. -/
def logisticTransform : R[X] →ₗ[R] R[X] :=
  Polynomial.lsum (fun n => LinearMap.toSpanSingleton R R[X] (logisticBasis n))

theorem logisticTransform_apply (A : R[X]) :
    logisticTransform A = ∑ i ∈ A.support, C (A.coeff i) * logisticBasis i := by
  simp only [logisticTransform, Polynomial.lsum_apply, Polynomial.sum_def,
    LinearMap.toSpanSingleton_apply, smul_eq_C_mul]

@[simp]
theorem logisticTransform_monomial (n : ℕ) (c : R) :
    logisticTransform (monomial n c) = c • logisticBasis n := by
  simp only [logisticTransform, Polynomial.lsum_apply]
  exact Polynomial.sum_monomial_index _ _ (by simp)

theorem logisticTransform_natDegree_le (A : R[X]) :
    (logisticTransform A).natDegree ≤ A.natDegree + 1 := by
  rw [logisticTransform_apply]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  calc
    (C (A.coeff i) * logisticBasis i).natDegree ≤ (logisticBasis (R := R) i).natDegree := by
      simpa only [natDegree_C, zero_add] using
        natDegree_mul_le (p := C (A.coeff i)) (q := logisticBasis (R := R) i)
    _ ≤ A.natDegree + 1 := (logisticBasis_natDegree_le i).trans
      (Nat.add_le_add_right (le_natDegree_of_ne_zero (mem_support_iff.mp hi)) 1)

theorem logisticTransform_top_coeff (A : R[X]) :
    (logisticTransform A).coeff (A.natDegree + 1) =
      A.leadingCoeff * ((-1 : R) ^ A.natDegree * (A.natDegree.factorial : R)) := by
  rw [logisticTransform_apply, finsetSum_coeff]
  simp only [coeff_C_mul]
  rw [Finset.sum_eq_single A.natDegree]
  · rw [logisticBasis_top_coeff]
    rfl
  · intro i hi hine
    have hi' := le_natDegree_of_ne_zero (mem_support_iff.mp hi)
    have hdeg : (logisticBasis (R := R) i).natDegree < A.natDegree + 1 :=
      (logisticBasis_natDegree_le i).trans_lt (by omega)
    rw [coeff_eq_zero_of_natDegree_lt hdeg, mul_zero]
  · intro hnot
    have hz : A.coeff A.natDegree = 0 := by simpa only [mem_support_iff, not_not] using hnot
    rw [hz, zero_mul]

@[simp]
theorem logisticTransform_coeff_zero (A : R[X]) : (logisticTransform A).coeff 0 = 0 := by
  simp only [logisticTransform_apply, finsetSum_coeff, coeff_C_mul, logisticBasis_coeff_zero,
    mul_zero, Finset.sum_const_zero]

theorem logisticTransform_X_mul (A : R[X]) :
    logisticTransform (X * A) = logisticDelta (logisticTransform A) := by
  induction A using Polynomial.induction_on' with
  | add A B hA hB => simp only [mul_add, map_add, hA, hB]
  | monomial n c =>
    rw [X, monomial_mul_monomial, one_mul, add_comm 1 n,
      logisticTransform_monomial, logisticTransform_monomial, logisticBasis_succ, map_smul]

theorem logisticTransform_C_mul (c : R) (A : R[X]) :
    logisticTransform (C c * A) = C c * logisticTransform A := by
  simpa only [smul_eq_C_mul] using (logisticTransform (R := R)).map_smul c A

end PolynomialCalculus

section ChangeCoefficients

variable {R S : Type*} [CommRing R] [CommRing S]

theorem logisticDelta_map (f : R →+* S) (F : R[X]) :
    (logisticDelta F).map f = logisticDelta (F.map f) := by
  simp only [logisticDelta, LinearMap.coe_mk, AddHom.coe_mk, Polynomial.map_mul,
    Polynomial.map_sub, map_X, Polynomial.map_one, derivative_map]

theorem logisticBasis_map (f : R →+* S) (n : ℕ) :
    (logisticBasis (R := R) n).map f = logisticBasis (R := S) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [logisticBasis_succ, logisticDelta_map, ih, logisticBasis_succ]

theorem logisticTransform_map (f : R →+* S) (A : R[X]) :
    (logisticTransform A).map f = logisticTransform (A.map f) := by
  induction A using Polynomial.induction_on' with
  | add A B hA hB => simp only [Polynomial.map_add, map_add, hA, hB]
  | monomial n c =>
    simp only [Polynomial.map_monomial, logisticTransform_monomial, smul_eq_C_mul,
      Polynomial.map_mul, map_C, logisticBasis_map]

end ChangeCoefficients

section CharacteristicZero

variable {K : Type*} [CommRing K] [IsDomain K] [CharZero K]

theorem logisticTransform_top_coeff_ne_zero {A : K[X]} (hA : A ≠ 0) :
    (logisticTransform A).coeff (A.natDegree + 1) ≠ 0 := by
  rw [logisticTransform_top_coeff]
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hA)
    (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))

theorem logisticTransform_natDegree {A : K[X]} (hA : A ≠ 0) :
    (logisticTransform A).natDegree = A.natDegree + 1 :=
  natDegree_eq_of_le_of_coeff_ne_zero (logisticTransform_natDegree_le A)
    (logisticTransform_top_coeff_ne_zero hA)

theorem logisticTransform_injective : Function.Injective (logisticTransform (R := K)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro A hA
  by_contra hne
  have hcoeff := logisticTransform_top_coeff_ne_zero hne
  rw [hA, coeff_zero] at hcoeff
  exact hcoeff rfl

end CharacteristicZero

/-- The rational logistic coordinate is transcendental over the coefficient field. -/
theorem logistic_transcendental : Transcendental ℂ logistic := by
  intro h
  have ht : IsAlgebraic ℂ (logistic * (1 - logistic)⁻¹) :=
    h.mul ((isAlgebraic_one (R := ℂ)).sub h).inv
  have he : logistic * (1 - logistic)⁻¹ = toRationalFunction X := by
    unfold logistic
    simp only [toRationalFunction_add, toRationalFunction_one]
    field_simp [one_add_variable_ne_zero]
    ring
  rw [he] at ht
  exact (RatFunc.transcendental_X (K := ℂ)) ht

theorem logistic_aeval_injective : Function.Injective (aeval logistic : ℂ[X] →ₐ[ℂ] RationalFunction) :=
  transcendental_iff_injective.mp logistic_transcendental

theorem logisticDelta_aeval (F : ℂ[X]) :
    aeval logistic (logisticDelta F) = exponentialDerivative (aeval logistic F) := by
  rw [← exponentialDerivation_apply, Derivation.map_aeval,
    exponentialDerivation_apply, exponentialDerivative_logistic]
  simp only [logisticDelta, LinearMap.coe_mk, AddHom.coe_mk,
    map_mul, map_sub, map_one, aeval_X, smul_eq_mul]
  ring

theorem logisticBasis_aeval (n : ℕ) :
    aeval logistic (logisticBasis (R := ℂ) n) = (exponentialDerivative^[n]) logistic := by
  induction n with
  | zero => simp
  | succ n ih => rw [logisticBasis_succ, logisticDelta_aeval, ih, Function.iterate_succ_apply']

theorem logisticTransform_aeval (A : ℂ[X]) :
    aeval logistic (logisticTransform A) = applyOperator A logistic := by
  simp only [logisticTransform_apply, map_sum, map_mul, aeval_C, logisticBasis_aeval,
    applyOperator]

/-- No nonzero constant-coefficient operator annihilates the logistic profile. -/
theorem applyOperator_logistic_injective :
    Function.Injective (fun A : ℂ[X] => applyOperator A logistic) := by
  intro A B h
  apply logisticTransform_injective
  apply logistic_aeval_injective
  simpa only [logisticTransform_aeval] using h

/-- A polynomial version of the rational-function convolution identity. -/
theorem logisticTransform_discreteConvolution (A B : ℂ[X]) :
    logisticTransform (discreteConvolution A B) = -logisticTransform A * logisticTransform B := by
  apply logistic_aeval_injective
  simp only [map_mul, map_neg, logisticTransform_aeval]
  have h := applyOperator_discreteConvolution A B
  linear_combination h

end PolynomialRigidity.Enumeration
