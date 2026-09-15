import PolynomialRigidity.Enumeration.RationalCalculus

/-!
# The logistic discrete-convolution identity

The proof is algebraic. It uses the shift relation `D(t*f)=t*(D+1)f`,
the identity `(1+t)Q=t`, and the forward-difference property of discrete
summation. No convergence or analytic continuation is assumed.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

local notation "ι" => toRationalFunction

/-- Multiplication by the exponential variable shifts the differential operator. -/
theorem applyOperator_mul_variable (P : ℂ[X]) (v : RationalFunction) :
    applyOperator P (ι X * v) = ι X * applyOperator (P.comp (X + 1)) v := by
  induction P using Polynomial.induction_on with
  | C c =>
    simp only [C_comp, applyOperator_C]
    ring
  | add P Q hP hQ =>
    simp only [add_comp, applyOperator_add, hP, hQ, mul_add]
  | monomial n c ih =>
    rw [show C c * X ^ (n + 1) = X * (C c * X ^ n) by ring]
    rw [applyOperator_mul, applyOperator_X, ih,
      exponentialDerivative_mul, exponentialDerivative_X]
    conv_rhs =>
      rw [mul_comp, X_comp, applyOperator_mul, applyOperator_add,
        applyOperator_X, applyOperator_one]
    ring

@[simp]
theorem applyOperator_one_right (P : ℂ[X]) :
    applyOperator P 1 = algebraMap ℂ RationalFunction (P.eval 0) := by
  induction P using Polynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [applyOperator_add, hP, hQ, eval_add, map_add]
  | monomial n c ih =>
    rw [show C c * X ^ (n + 1) = X * (C c * X ^ n) by ring]
    rw [applyOperator_mul, applyOperator_X, ih, exponentialDerivative_constant]
    simp

@[simp]
theorem applyOperator_variable (P : ℂ[X]) :
    applyOperator P (ι X) = ι X * algebraMap ℂ RationalFunction (P.eval 1) := by
  simpa only [mul_one, applyOperator_one_right, eval_comp, eval_add, eval_X, eval_one,
    zero_add] using applyOperator_mul_variable P 1

theorem one_add_variable_ne_zero : 1 + ι X ≠ 0 := by
  have h : (1 + X : ℂ[X]) ≠ 0 := by
    simpa only [C_1, add_comm] using (monic_X_add_C (1 : ℂ)).ne_zero
  simpa only [toRationalFunction_add, toRationalFunction_one] using
    (toRationalFunction_eq_zero _).not.mpr h

theorem logistic_add_variable_mul : logistic + ι X * logistic = ι X := by
  unfold logistic
  simp only [toRationalFunction_add, toRationalFunction_one]
  field_simp [one_add_variable_ne_zero]

/-- The operator form of `(1+t)Q=t`. -/
theorem applyOperator_logistic_shift (P : ℂ[X]) :
    applyOperator P logistic + ι X * applyOperator (P.comp (X + 1)) logistic =
      ι X * algebraMap ℂ RationalFunction (P.eval 1) := by
  simpa only [applyOperator_add_right, applyOperator_mul_variable, applyOperator_variable] using
    congrArg (applyOperator P) logistic_add_variable_mul

/-- Multiplying by `Q` corresponds to a negative discrete primitive of the operator. -/
theorem applyOperator_mul_logistic (F : ℂ[X]) :
    applyOperator F logistic * logistic = -applyOperator (discreteConvolution F 1) logistic := by
  have hcomp : (discreteConvolution F 1).comp (X + 1) = discreteConvolution F 1 + F := by
    exact (sub_eq_iff_eq_add.mp (discreteConvolution_one_difference F)).trans (add_comm _ _)
  have hs := applyOperator_logistic_shift (discreteConvolution F 1)
  rw [hcomp, applyOperator_add, discreteConvolution_eval_one, map_zero, mul_zero] at hs
  conv_lhs =>
    rhs
    rw [logistic, toRationalFunction_add, toRationalFunction_one]
  field_simp [one_add_variable_ne_zero]
  linear_combination hs

/-- The bilinear discrete-convolution identity for the actual rational differential operator. -/
theorem applyOperator_discreteConvolution (F G : ℂ[X]) :
    applyOperator F logistic * applyOperator G logistic =
      -applyOperator (discreteConvolution F G) logistic := by
  induction G using Polynomial.induction_on generalizing F with
  | C c =>
    have hc : discreteConvolution F (C c) = C c * discreteConvolution F 1 := by
      simpa only [mul_one] using discreteConvolution_C_mul_right F 1 c
    rw [applyOperator_C, hc, applyOperator_mul, applyOperator_C]
    calc
      _ = algebraMap ℂ RationalFunction c * (applyOperator F logistic * logistic) := by ring
      _ = _ := by rw [applyOperator_mul_logistic]; ring
  | add G H hG hH =>
    rw [applyOperator_add, mul_add, hG F, hH F,
      discreteConvolution_add_right, applyOperator_add]
    ring
  | monomial n c ih =>
    rw [show C c * X ^ (n + 1) = X * (C c * X ^ n) by ring]
    rw [applyOperator_mul, applyOperator_X]
    have hd := congrArg exponentialDerivative (ih F)
    rw [exponentialDerivative_mul, exponentialDerivative_neg] at hd
    have hx := ih (X * F)
    rw [applyOperator_mul, applyOperator_X] at hx
    have hb := congrArg (fun P => applyOperator P logistic)
      (discreteConvolution_mul_X_balance F (C c * X ^ n))
    rw [applyOperator_mul, applyOperator_X, applyOperator_add] at hb
    linear_combination hd - hx - hb

theorem applyOperator_square (A : ℂ[X]) :
    applyOperator A logistic ^ 2 = -applyOperator (discreteConvolution A A) logistic := by
  simpa only [pow_two] using applyOperator_discreteConvolution A A

/-- Matching forces the displayed candidate operator to satisfy its defining product identity. -/
theorem candidateOperator_mul_coefficient (p : ℕ) (a : Coefficients p)
    (ha : IsMatchingSolution p a) :
    candidateOperator p a * coefficientPolynomial p a =
      C ((beta (p - 1) (p - 1) : ℂ)⁻¹) *
        discreteConvolution (coefficientPolynomial p a) (coefficientPolynomial p a) := by
  have hdiv := (matchingDivisibilityAtOrder p a).mp ha
  have hrem := (modByMonic_eq_zero_iff_dvd (coefficientPolynomial_monic p a)).mpr hdiv
  have hquot : coefficientPolynomial p a *
      (discreteConvolution (coefficientPolynomial p a) (coefficientPolynomial p a) /ₘ
        coefficientPolynomial p a) =
      discreteConvolution (coefficientPolynomial p a) (coefficientPolynomial p a) := by
    simpa only [hrem, zero_add] using modByMonic_add_div
      (discreteConvolution (coefficientPolynomial p a) (coefficientPolynomial p a))
      (coefficientPolynomial p a)
  unfold candidateOperator
  rw [mul_assoc, mul_comm _ (coefficientPolynomial p a), hquot]

/-- Every matching point satisfies the exact rational-function ODE. -/
theorem candidateProfile_solvesODE (p : ℕ) (a : Coefficients p)
    (ha : IsMatchingSolution p a) :
    SolvesODE (candidateOperator p a) (candidateProfile p a) := by
  unfold SolvesODE candidateProfile
  rw [applyOperator_smul_right, ← applyOperator_mul,
    candidateOperator_mul_coefficient p a ha, applyOperator_mul, applyOperator_C,
    mul_pow, applyOperator_square]
  have hs : algebraMap ℂ RationalFunction (profileScale p) =
      2 * algebraMap ℂ RationalFunction ((beta (p - 1) (p - 1) : ℂ)⁻¹) := by
    simp only [profileScale, div_eq_mul_inv, map_mul, map_ofNat]
  rw [hs]
  ring

end PolynomialRigidity.Enumeration
