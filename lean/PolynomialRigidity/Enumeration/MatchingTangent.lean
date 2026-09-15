import PolynomialRigidity.Enumeration.JacobianColumns
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Polynomial interpretation of Jacobian nonsingularity

The coefficient variations are all polynomials of degree below `p-1`.
The specified determinant is nonzero precisely when the polynomial tangent
map has trivial kernel. This is the algebraic transversality condition used
in both the prime reduction and the ODE simplicity correspondence.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

def coefficientVariation (p : ℕ) : Coefficients p →ₗ[ℂ] ℂ[X] where
  toFun h := ∑ j : Fin (p - 1), C (h j) * X ^ (p - 1 - (j.val + 1))
  map_add' h k := by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c h := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, smul_eq_C_mul,
      Finset.mul_sum, mul_assoc, RingHom.id_apply]

theorem coefficientVariation_apply (p : ℕ) (h : Coefficients p) :
    coefficientVariation p h = ∑ j : Fin (p - 1), C (h j) * X ^ (p - 1 - (j.val + 1)) := rfl

theorem coefficientVariation_degree_lt (p : ℕ) (h : Coefficients p) :
    (coefficientVariation p h).degree < ((p - 1 : ℕ) : WithBot ℕ) :=
  degree_lowerTerms_lt _ _

theorem coefficientVariation_coeff (p : ℕ) (h : Coefficients p) (j : Fin (p - 1)) :
    (coefficientVariation p h).coeff (p - 1 - (j.val + 1)) = h j := by
  have hcoef := monicPolynomial_coeff (p - 1) h j
  change (X ^ (p - 1) + coefficientVariation p h).coeff (p - 1 - (j.val + 1)) = h j at hcoef
  rw [coeff_add, coeff_X_pow, if_neg (by have := j.is_lt; omega), zero_add] at hcoef
  exact hcoef

theorem coefficientVariation_injective (p : ℕ) : Function.Injective (coefficientVariation p) := by
  intro h k heq
  apply monicPolynomial_injective (p - 1)
  exact congrArg (fun F : ℂ[X] => X ^ (p - 1) + F) heq

theorem coefficientVariation_coefficients {p : ℕ} (F : ℂ[X])
    (hdeg : F.degree < ((p - 1 : ℕ) : WithBot ℕ)) :
    coefficientVariation p (fun j => F.coeff (p - 1 - (j.val + 1))) = F := by
  apply Polynomial.ext
  intro n
  by_cases hn : n < p - 1
  · let j : Fin (p - 1) := ⟨p - 1 - (n + 1), by omega⟩
    have hj : p - 1 - (j.val + 1) = n := by dsimp [j]; omega
    simpa only [hj] using coefficientVariation_coeff p (fun j => F.coeff (p - 1 - (j.val + 1))) j
  · have hle : ((p - 1 : ℕ) : WithBot ℕ) ≤ (n : WithBot ℕ) :=
      WithBot.coe_le_coe.mpr (Nat.le_of_not_gt hn)
    rw [coeff_eq_zero_of_degree_lt ((coefficientVariation_degree_lt p _).trans_le hle),
      coeff_eq_zero_of_degree_lt (hdeg.trans_le hle)]

def discreteConvolutionLinearRight (A : ℂ[X]) : ℂ[X] →ₗ[ℂ] ℂ[X] where
  toFun F := discreteConvolution A F
  map_add' := discreteConvolution_add_right A
  map_smul' c F := by
    simp only [smul_eq_C_mul, discreteConvolution_C_mul_right, RingHom.id_apply]

def matchingTangent (p : ℕ) (a : Coefficients p) : ℂ[X] →ₗ[ℂ] ℂ[X] :=
  (Polynomial.modByMonicHom (coefficientPolynomial p a)).comp
    ((2 : ℂ) • discreteConvolutionLinearRight (coefficientPolynomial p a) -
      matchingQuotient p a • LinearMap.id)

theorem matchingTangent_apply (p : ℕ) (a : Coefficients p) (F : ℂ[X]) :
    matchingTangent p a F =
      (2 * discreteConvolution (coefficientPolynomial p a) F - matchingQuotient p a * F) %ₘ
        coefficientPolynomial p a := by
  change ((2 : ℂ) • discreteConvolution (coefficientPolynomial p a) F - matchingQuotient p a * F) %ₘ
    coefficientPolynomial p a = _
  simp only [smul_eq_C_mul, map_ofNat]

theorem matchingTangent_C_mul (p : ℕ) (a : Coefficients p) (c : ℂ) (F : ℂ[X]) :
    matchingTangent p a (C c * F) = C c * matchingTangent p a F := by
  simpa only [smul_eq_C_mul] using (matchingTangent p a).map_smul c F

theorem matchingJacobian_column_tangent (p : ℕ) (a : Coefficients p) (r j : Fin (p - 1)) :
    matchingJacobian p a r j =
      (matchingTangent p a (X ^ (p - 1 - (j.val + 1)))).coeff r.val := by
  rw [matchingTangent_apply]
  exact matchingJacobian_column p a r j

theorem matchingJacobian_mulVec (p : ℕ) (a h : Coefficients p) (r : Fin (p - 1)) :
    ((matchingJacobian p a).mulVec h) r =
      (matchingTangent p a (coefficientVariation p h)).coeff r.val := by
  simp only [Matrix.mulVec, dotProduct, coefficientVariation_apply, map_sum, finsetSum_coeff,
    matchingTangent_C_mul, coeff_C_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [matchingJacobian_column_tangent]
  ring

theorem matchingJacobian_mulVec_eq_zero_iff (p : ℕ) (a h : Coefficients p) :
    (matchingJacobian p a).mulVec h = 0 ↔ matchingTangent p a (coefficientVariation p h) = 0 := by
  constructor
  · intro hz
    apply Polynomial.ext
    intro n
    rw [coeff_zero]
    by_cases hn : n < p - 1
    · have hr := congrFun hz ⟨n, hn⟩
      simpa only [matchingJacobian_mulVec, Pi.zero_apply] using hr
    · rw [matchingTangent_apply]
      apply coeff_eq_zero_of_degree_lt
      apply (degree_modByMonic_lt _ (coefficientPolynomial_monic p a)).trans_le
      rw [coefficientPolynomial_degree]
      exact WithBot.coe_le_coe.mpr (Nat.le_of_not_gt hn)
  · intro hz
    funext r
    rw [matchingJacobian_mulVec, hz, coeff_zero, Pi.zero_apply]

theorem isSimpleMatchingSolution_iff_kernel (p : ℕ) (a : Coefficients p) :
    IsSimpleMatchingSolution p a ↔
      ∀ h : Coefficients p, (matchingJacobian p a).mulVec h = 0 → h = 0 := by
  constructor
  · intro hdet h hh
    by_contra hne
    exact hdet ((Matrix.exists_mulVec_eq_zero_iff).mp ⟨h, hne, hh⟩)
  · intro hker hdet
    obtain ⟨h, hne, hh⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    exact hne (hker h hh)

def IsTransverseMatching (p : ℕ) (a : Coefficients p) : Prop :=
  ∀ F : ℂ[X], F.degree < (coefficientPolynomial p a).degree →
    coefficientPolynomial p a ∣
      2 * discreteConvolution (coefficientPolynomial p a) F - matchingQuotient p a * F → F = 0

/-- The coefficient Jacobian condition is precisely polynomial transversality. -/
theorem isSimpleMatchingSolution_iff_transverse (p : ℕ) (a : Coefficients p) :
    IsSimpleMatchingSolution p a ↔ IsTransverseMatching p a := by
  rw [isSimpleMatchingSolution_iff_kernel]
  constructor
  · intro hker F hdeg hdiv
    let h : Coefficients p := fun j => F.coeff (p - 1 - (j.val + 1))
    have hrepr : coefficientVariation p h = F :=
      coefficientVariation_coefficients F (by simpa only [coefficientPolynomial_degree] using hdeg)
    have hzero : matchingTangent p a F = 0 := by
      rw [matchingTangent_apply]
      exact (modByMonic_eq_zero_iff_dvd (coefficientPolynomial_monic p a)).mpr hdiv
    have hh := hker h ((matchingJacobian_mulVec_eq_zero_iff p a h).mpr (by rwa [hrepr]))
    rw [← hrepr, hh, map_zero]
  · intro htrans h hh
    have hzero := (matchingJacobian_mulVec_eq_zero_iff p a h).mp hh
    rw [matchingTangent_apply] at hzero
    have hpoly := htrans (coefficientVariation p h)
      (by simpa only [coefficientPolynomial_degree] using coefficientVariation_degree_lt p h)
      ((modByMonic_eq_zero_iff_dvd (coefficientPolynomial_monic p a)).mp hzero)
    apply coefficientVariation_injective p
    simpa only [map_zero] using hpoly

end PolynomialRigidity.Enumeration
