import PolynomialRigidity.Enumeration.MobiusCoordinates

/-!
# Leading coefficients of the polynomial differential equation

The leading coefficient of a nonconstant logistic profile is fixed by the
ODE with a monic operator. This recovers exactly the amplitude normalisation
specified by `profileScale`.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

section GeneralCoefficients

variable {R : Type*} [CommRing R]

theorem logisticDelta_iterate_natDegree_le (B : R[X]) (n : ℕ) :
    ((logisticDelta^[n]) B).natDegree ≤ B.natDegree + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (logisticDelta_natDegree_le _).trans (by omega)

theorem logisticDelta_iterate_top_coeff (B : R[X]) (n : ℕ) :
    ((logisticDelta^[n]) B).coeff (B.natDegree + n) =
      B.leadingCoeff * ((-1 : R) ^ n * (B.natDegree.ascFactorial n : R)) := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero_apply, Nat.add_zero, pow_zero,
      Nat.ascFactorial_zero, Nat.cast_one, mul_one, coeff_natDegree]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← Nat.add_assoc, logisticDelta_coeff_succ,
      coeff_eq_zero_of_natDegree_lt ((logisticDelta_iterate_natDegree_le B n).trans_lt (by omega)), ih]
    simp only [zero_mul, zero_sub, Nat.ascFactorial_succ, Nat.cast_mul,
      Nat.cast_add, pow_succ]
    ring

def polynomialOperator (P B : R[X]) : R[X] := (aeval logisticDelta P) B

theorem polynomialOperator_apply (P B : R[X]) :
    polynomialOperator P B = ∑ i ∈ P.support, C (P.coeff i) * (logisticDelta^[i]) B := by
  simp only [polynomialOperator, aeval_def, eval₂_eq_sum, Polynomial.sum_def, LinearMap.sum_apply,
    Module.End.mul_apply, Module.End.pow_apply, Module.algebraMap_end_apply, smul_eq_C_mul]

theorem polynomialOperator_natDegree_le (P B : R[X]) :
    (polynomialOperator P B).natDegree ≤ B.natDegree + P.natDegree := by
  rw [polynomialOperator_apply]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  calc
    (C (P.coeff i) * (logisticDelta^[i]) B).natDegree ≤ ((logisticDelta^[i]) B).natDegree := by
      simpa only [natDegree_C, zero_add] using
        natDegree_mul_le (p := C (P.coeff i)) (q := (logisticDelta^[i]) B)
    _ ≤ B.natDegree + P.natDegree := (logisticDelta_iterate_natDegree_le B i).trans
      (Nat.add_le_add_left (le_natDegree_of_ne_zero (mem_support_iff.mp hi)) B.natDegree)

theorem polynomialOperator_top_coeff (P B : R[X]) :
    (polynomialOperator P B).coeff (B.natDegree + P.natDegree) =
      P.leadingCoeff * (B.leadingCoeff *
        ((-1 : R) ^ P.natDegree * (B.natDegree.ascFactorial P.natDegree : R))) := by
  rw [polynomialOperator_apply, finsetSum_coeff]
  simp only [coeff_C_mul]
  rw [Finset.sum_eq_single P.natDegree]
  · rw [logisticDelta_iterate_top_coeff]
    rfl
  · intro i hi hine
    have hi' := le_natDegree_of_ne_zero (mem_support_iff.mp hi)
    rw [coeff_eq_zero_of_natDegree_lt
      ((logisticDelta_iterate_natDegree_le B i).trans_lt (by omega)), mul_zero]
  · intro hnot
    have hz : P.coeff P.natDegree = 0 := by simpa only [mem_support_iff, not_not] using hnot
    rw [hz, zero_mul]

end GeneralCoefficients

theorem logisticDelta_iterate_aeval (B : ℂ[X]) (n : ℕ) :
    aeval logistic ((logisticDelta^[n]) B) = (exponentialDerivative^[n]) (aeval logistic B) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', logisticDelta_aeval, ih, Function.iterate_succ_apply']

theorem polynomialOperator_aeval (P B : ℂ[X]) :
    aeval logistic (polynomialOperator P B) = applyOperator P (aeval logistic B) := by
  simp only [polynomialOperator_apply, map_sum, map_mul, aeval_C,
    logisticDelta_iterate_aeval, applyOperator]

theorem polynomialODE_of_rationalODE (P B : ℂ[X]) (hODE : SolvesODE P (aeval logistic B)) :
    polynomialOperator P B + C (1 / 2 : ℂ) * B ^ 2 = 0 := by
  apply logistic_aeval_injective
  unfold SolvesODE at hODE
  simpa only [map_add, map_mul, map_pow, map_zero, aeval_C,
    polynomialOperator_aeval, map_div₀, map_one, map_ofNat] using hODE

/-- Dominant balance fixes the leading coefficient of a logistic profile. -/
theorem logistic_ODE_leadingCoeff {p : ℕ} {P B : ℂ[X]} (hP : P.Monic)
    (hPdeg : P.natDegree = p) (hBdeg : B.natDegree = p) (hB : B ≠ 0)
    (hODE : SolvesODE P (aeval logistic B)) :
    B.leadingCoeff = -2 * ((-1 : ℂ) ^ p * (p.ascFactorial p : ℂ)) := by
  have hpoly := polynomialODE_of_rationalODE P B hODE
  have hop := polynomialOperator_top_coeff P B
  rw [hPdeg, hBdeg, hP.leadingCoeff, one_mul] at hop
  have hsquare : (B ^ 2).coeff (p + p) = B.leadingCoeff ^ 2 := by
    rw [pow_two, coeff_mul_add_eq_of_natDegree_le hBdeg.le hBdeg.le, ← hBdeg]
    simp only [coeff_natDegree, pow_two]
  have hc := congrArg (fun F : ℂ[X] => F.coeff (p + p)) hpoly
  rw [coeff_add, hop, coeff_C_mul, hsquare, coeff_zero] at hc
  apply mul_left_cancel₀ (leadingCoeff_ne_zero.mpr hB)
  linear_combination 2 * hc

/-- The leading coefficient obtained by dominant balance equals the manuscript's scale. -/
theorem profileScale_basisScalar {p : ℕ} (hp : 0 < p) :
    profileScale p * ((-1 : ℂ) ^ (p - 1) * ((p - 1).factorial : ℂ)) =
      -2 * ((-1 : ℂ) ^ p * (p.ascFactorial p : ℂ)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  have hd : (d.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  have hN : ((d + d + 1).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hfac : ((d + d + 1).factorial : ℂ) =
      (d.factorial : ℂ) * ((d + 1).ascFactorial (d + 1) : ℂ) := by
    exact_mod_cast (by simpa only [Nat.add_assoc] using (Nat.factorial_mul_ascFactorial d (d + 1)).symm)
  have ha : ((d + 1).ascFactorial (d + 1) : ℂ) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hfac
    exact hN hfac
  simp only [profileScale, beta, Nat.succ_eq_add_one, Nat.add_sub_cancel]
  rw [hfac, pow_succ]
  field_simp

end PolynomialRigidity.Enumeration
