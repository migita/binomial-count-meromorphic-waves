import PolynomialRigidity.Enumeration.Basic
import PolynomialRigidity.Enumeration.Discrete
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Differential operators on rational functions of the exponential

The quotient-rule operation in the fixed statement is a complex-linear
derivation. The proofs first show that its value is independent of the
chosen fractional expression, using equality of cross-products.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

local notation "ι" => toRationalFunction

@[simp] theorem toRationalFunction_zero : ι 0 = 0 := map_zero _
@[simp] theorem toRationalFunction_one : ι 1 = 1 := map_one _
@[simp] theorem toRationalFunction_add (F G : ℂ[X]) : ι (F + G) = ι F + ι G := map_add _ _ _
@[simp] theorem toRationalFunction_sub (F G : ℂ[X]) : ι (F - G) = ι F - ι G := map_sub _ _ _
@[simp] theorem toRationalFunction_mul (F G : ℂ[X]) : ι (F * G) = ι F * ι G := map_mul _ _ _
@[simp] theorem toRationalFunction_pow (F : ℂ[X]) (n : ℕ) : ι (F ^ n) = ι F ^ n := map_pow _ _ _
@[simp] theorem toRationalFunction_C (c : ℂ) : ι (C c) = algebraMap ℂ RationalFunction c := rfl

theorem toRationalFunction_injective : Function.Injective toRationalFunction :=
  RatFunc.algebraMap_injective ℂ

@[simp] theorem toRationalFunction_eq_zero (F : ℂ[X]) : ι F = 0 ↔ F = 0 := by
  rw [← toRationalFunction_zero]
  exact toRationalFunction_injective.eq_iff

private theorem quotient_derivative_congr (A B C D : ℂ[X]) (hB : B ≠ 0) (hD : D ≠ 0)
    (h : A * D = C * B) :
    ι (A.derivative * B - A * B.derivative) / ι B ^ 2 =
      ι (C.derivative * D - C * D.derivative) / ι D ^ 2 := by
  have hd := congrArg Polynomial.derivative h
  simp only [derivative_mul] at hd
  have he : (A.derivative * B - A * B.derivative) * D ^ 2 =
      (C.derivative * D - C * D.derivative) * B ^ 2 := by
    linear_combination B * D * hd - (B.derivative * D + B * D.derivative) * h
  apply (div_eq_div_iff (pow_ne_zero 2 ((toRationalFunction_eq_zero B).not.mpr hB))
    (pow_ne_zero 2 ((toRationalFunction_eq_zero D).not.mpr hD))).mpr
  simpa only [toRationalFunction_mul, toRationalFunction_pow] using congrArg toRationalFunction he

/-- The quotient-rule formula holds for every denominator, not only the reduced one. -/
theorem exponentialDerivative_div (F G : ℂ[X]) (hG : G ≠ 0) :
    exponentialDerivative (ι F / ι G) =
      ι X * (ι (F.derivative * G - F * G.derivative) / ι G ^ 2) := by
  unfold exponentialDerivative
  rw [mul_div_assoc]
  apply congrArg (fun x : RationalFunction => ι X * x)
  apply quotient_derivative_congr _ _ F G (RatFunc.denom_ne_zero _) hG
  exact (RatFunc.num_mul_eq_mul_denom_iff hG).mpr rfl

@[simp]
theorem exponentialDerivative_polynomial (F : ℂ[X]) :
    exponentialDerivative (ι F) = ι X * ι F.derivative := by
  simpa using exponentialDerivative_div F 1 one_ne_zero

@[simp]
theorem exponentialDerivative_constant (c : ℂ) :
    exponentialDerivative (algebraMap ℂ RationalFunction c) = 0 := by
  rw [← toRationalFunction_C, exponentialDerivative_polynomial, derivative_C,
    toRationalFunction_zero, mul_zero]

@[simp]
theorem exponentialDerivative_zero : exponentialDerivative 0 = 0 := by
  simpa using exponentialDerivative_constant 0

@[simp]
theorem exponentialDerivative_one : exponentialDerivative 1 = 0 := by
  simpa using exponentialDerivative_constant 1

@[simp]
theorem exponentialDerivative_X : exponentialDerivative (ι X) = ι X := by simp

theorem exponentialDerivative_add (v w : RationalFunction) :
    exponentialDerivative (v + w) = exponentialDerivative v + exponentialDerivative w := by
  induction v using RatFunc.induction_on with
  | f F G hG =>
    induction w using RatFunc.induction_on with
    | f H J hJ =>
      change exponentialDerivative (ι F / ι G + ι H / ι J) =
        exponentialDerivative (ι F / ι G) + exponentialDerivative (ι H / ι J)
      have hG' : ι G ≠ 0 := (toRationalFunction_eq_zero G).not.mpr hG
      have hJ' : ι J ≠ 0 := (toRationalFunction_eq_zero J).not.mpr hJ
      have hsum : ι F / ι G + ι H / ι J = ι (F * J + G * H) / ι (G * J) := by
        simp only [toRationalFunction_add, toRationalFunction_mul]
        field_simp
      rw [hsum, exponentialDerivative_div _ _ (mul_ne_zero hG hJ),
        exponentialDerivative_div F G hG, exponentialDerivative_div H J hJ]
      simp only [derivative_add, derivative_mul, toRationalFunction_mul,
        toRationalFunction_add, toRationalFunction_sub]
      field_simp
      ring

theorem exponentialDerivative_mul (v w : RationalFunction) :
    exponentialDerivative (v * w) = exponentialDerivative v * w + v * exponentialDerivative w := by
  induction v using RatFunc.induction_on with
  | f F G hG =>
    induction w using RatFunc.induction_on with
    | f H J hJ =>
      change exponentialDerivative ((ι F / ι G) * (ι H / ι J)) =
        exponentialDerivative (ι F / ι G) * (ι H / ι J) +
          (ι F / ι G) * exponentialDerivative (ι H / ι J)
      have hG' : ι G ≠ 0 := (toRationalFunction_eq_zero G).not.mpr hG
      have hJ' : ι J ≠ 0 := (toRationalFunction_eq_zero J).not.mpr hJ
      have hprod : (ι F / ι G) * (ι H / ι J) = ι (F * H) / ι (G * J) := by
        simp only [toRationalFunction_mul, div_mul_div_comm]
      rw [hprod, exponentialDerivative_div _ _ (mul_ne_zero hG hJ),
        exponentialDerivative_div F G hG, exponentialDerivative_div H J hJ]
      simp only [derivative_mul, toRationalFunction_mul,
        toRationalFunction_add, toRationalFunction_sub]
      field_simp
      ring

/-- The specific derivative occurring in the target, bundled as a derivation. -/
def exponentialDerivation : Derivation ℂ RationalFunction RationalFunction where
  toFun := exponentialDerivative
  map_add' := exponentialDerivative_add
  map_smul' c v := by
    simp only [Algebra.smul_def, exponentialDerivative_mul, exponentialDerivative_constant,
      zero_mul, zero_add, RingHom.id_apply]
  map_one_eq_zero' := exponentialDerivative_one
  leibniz' v w := by
    change exponentialDerivative (v * w) = v * exponentialDerivative w + w * exponentialDerivative v
    rw [exponentialDerivative_mul]
    ac_rfl

@[simp] theorem exponentialDerivation_apply (v : RationalFunction) :
    exponentialDerivation v = exponentialDerivative v := rfl

@[simp]
theorem exponentialDerivative_neg (v : RationalFunction) :
    exponentialDerivative (-v) = -exponentialDerivative v :=
  exponentialDerivation.map_neg v

theorem exponentialDerivative_sub (v w : RationalFunction) :
    exponentialDerivative (v - w) = exponentialDerivative v - exponentialDerivative w :=
  exponentialDerivation.map_sub v w

theorem applyOperator_eq_aeval (P : ℂ[X]) (v : RationalFunction) :
    applyOperator P v = (aeval exponentialDerivation.toLinearMap P) v := by
  simp only [aeval_def, eval₂_eq_sum, Polynomial.sum_def, LinearMap.sum_apply,
    Module.End.mul_apply, Module.End.pow_apply, Module.algebraMap_end_apply, Algebra.smul_def]
  rfl

@[simp]
theorem applyOperator_C (c : ℂ) (v : RationalFunction) :
    applyOperator (C c) v = algebraMap ℂ RationalFunction c * v := by
  simp [applyOperator_eq_aeval, Algebra.smul_def]

@[simp]
theorem applyOperator_X (v : RationalFunction) :
    applyOperator X v = exponentialDerivative v := by simp [applyOperator_eq_aeval]

@[simp]
theorem applyOperator_one (v : RationalFunction) : applyOperator 1 v = v := by
  simp [applyOperator_eq_aeval]

@[simp]
theorem applyOperator_zero (v : RationalFunction) : applyOperator 0 v = 0 := by
  simp [applyOperator_eq_aeval]

theorem applyOperator_add (P Q : ℂ[X]) (v : RationalFunction) :
    applyOperator (P + Q) v = applyOperator P v + applyOperator Q v := by
  simp [applyOperator_eq_aeval]

theorem applyOperator_sub (P Q : ℂ[X]) (v : RationalFunction) :
    applyOperator (P - Q) v = applyOperator P v - applyOperator Q v := by
  simp [applyOperator_eq_aeval]

@[simp]
theorem applyOperator_zero_right (P : ℂ[X]) : applyOperator P 0 = 0 := by
  simp [applyOperator_eq_aeval]

theorem applyOperator_mul (P Q : ℂ[X]) (v : RationalFunction) :
    applyOperator (P * Q) v = applyOperator P (applyOperator Q v) := by
  simp [applyOperator_eq_aeval, Module.End.mul_apply]

theorem applyOperator_add_right (P : ℂ[X]) (v w : RationalFunction) :
    applyOperator P (v + w) = applyOperator P v + applyOperator P w := by
  simp [applyOperator_eq_aeval]

theorem applyOperator_smul_right (P : ℂ[X]) (c : ℂ) (v : RationalFunction) :
    applyOperator P (algebraMap ℂ RationalFunction c * v) =
      algebraMap ℂ RationalFunction c * applyOperator P v := by
  simpa only [Algebra.smul_def, applyOperator_eq_aeval] using
    (aeval exponentialDerivation.toLinearMap P).map_smul c v

@[simp]
theorem exponentialDerivative_logistic :
    exponentialDerivative logistic = logistic * (1 - logistic) := by
  have hden : (1 + X : ℂ[X]) ≠ 0 := by
    simpa only [C_1, add_comm] using (monic_X_add_C (1 : ℂ)).ne_zero
  have hden' : ι (1 + X) ≠ 0 := (toRationalFunction_eq_zero _).not.mpr hden
  rw [logistic, exponentialDerivative_div _ _ hden]
  simp only [derivative_X, derivative_add, derivative_one, zero_add,
    one_mul, mul_one, add_sub_cancel_right]
  simp only [toRationalFunction_add, toRationalFunction_one] at hden' ⊢
  field_simp
  ring

end PolynomialRigidity.Enumeration
