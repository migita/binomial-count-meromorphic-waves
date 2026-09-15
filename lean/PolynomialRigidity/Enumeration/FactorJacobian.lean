import PolynomialRigidity.Enumeration.UniversalEquations
import PolynomialRigidity.Enumeration.CoefficientDerivation
import PolynomialRigidity.Enumeration.MultivariateHensel
import PolynomialRigidity.Enumeration.FiniteLabels
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Nonsingularity of the fixed-factor remainder system

This calculation works over every field, including the residue field.
The derivatives are taken in the universal monic divisor coordinates.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

section Definitions

variable {R : Type*} [CommRing R]

def factorRemainder (d : ℕ) (F : R[X]) : (MvPolynomial (Fin d) R)[X] :=
  F.map MvPolynomial.C %ₘ universalMonicOver R d

def factorQuotient (d : ℕ) (F : R[X]) : (MvPolynomial (Fin d) R)[X] :=
  F.map MvPolynomial.C /ₘ universalMonicOver R d

def factorEquations (d : ℕ) (F : R[X]) (r : Fin d) : MvPolynomial (Fin d) R :=
  (factorRemainder d F).coeff r.val

theorem factorRemainder_eval (d : ℕ) (F : R[X]) (a : Fin d → R) :
    (factorRemainder d F).map (MvPolynomial.eval a) = F %ₘ monicPolynomial d a := by
  have hc : (MvPolynomial.eval a).comp MvPolynomial.C = RingHom.id R := by ext x; simp
  rw [factorRemainder, map_modByMonic _ (universalMonicOver_monic R d),
    Polynomial.map_map, hc, Polynomial.map_id, universalMonicOver_eval]

theorem factorQuotient_eval (d : ℕ) (F : R[X]) (a : Fin d → R) :
    (factorQuotient d F).map (MvPolynomial.eval a) = F /ₘ monicPolynomial d a := by
  have hc : (MvPolynomial.eval a).comp MvPolynomial.C = RingHom.id R := by ext x; simp
  rw [factorQuotient, map_divByMonic _ (universalMonicOver_monic R d),
    Polynomial.map_map, hc, Polynomial.map_id, universalMonicOver_eval]

theorem factorEquations_zero_of_dvd (d : ℕ) (F : R[X]) (a : Fin d → R)
    (hdiv : monicPolynomial d a ∣ F) : ∀ r, MvPolynomial.eval a (factorEquations d F r) = 0 := by
  intro r
  have hzero := (modByMonic_eq_zero_iff_dvd (monicPolynomial_monic d a)).mpr hdiv
  have he := congrArg (fun P : R[X] => P.coeff r.val) (factorRemainder_eval d F a)
  rw [hzero, coeff_zero, coeff_map] at he
  exact he

def coordinateDirection (d : ℕ) (h : Fin d → R) :
    Derivation R (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R) :=
  ∑ j : Fin d, (MvPolynomial.C (h j) : MvPolynomial (Fin d) R) •
    MvPolynomial.pderiv (R := R) j

theorem coordinateDirection_apply (d : ℕ) (h : Fin d → R) (F : MvPolynomial (Fin d) R) :
    coordinateDirection d h F = ∑ j : Fin d, MvPolynomial.C (h j) * MvPolynomial.pderiv j F := by
  change Derivation.coeFnAddMonoidHom (∑ j : Fin d,
    (MvPolynomial.C (h j) : MvPolynomial (Fin d) R) • MvPolynomial.pderiv (R := R) j) F = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, smul_eq_mul]

@[simp]
theorem coordinateDirection_X (d : ℕ) (h : Fin d → R) (j : Fin d) :
    coordinateDirection d h (MvPolynomial.X j : MvPolynomial (Fin d) R) =
      (MvPolynomial.C (h j) : MvPolynomial (Fin d) R) := by
  classical
  rw [coordinateDirection_apply, Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [MvPolynomial.pderiv_X_of_ne hij.symm]
  · simp

theorem coordinateDirection_universal_eval (d : ℕ) (h a : Fin d → R) :
    (coefficientDerivation (coordinateDirection d h) (universalMonicOver R d)).map (MvPolynomial.eval a) =
      ∑ j : Fin d, C (h j) * X ^ (d - (j.val + 1)) := by
  rw [universalMonicOver, coefficientDerivation_monicPolynomial]
  simp only [coordinateDirection_X, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_pow, map_X, map_C, MvPolynomial.eval_C]

end Definitions

/-- A separable polynomial has a nonsingular divisor remainder system at every monic divisor. -/
theorem factorJacobian_ne_zero {k : Type*} [Field k] (d : ℕ) (F : k[X])
    (hsep : F.Separable) (a : Fin d → k) (hdiv : monicPolynomial d a ∣ F) :
    MvPolynomial.eval a (PolynomialSystem.jacobianPolynomial (factorEquations d F)) ≠ 0 := by
  classical
  intro hdet
  let M := (MvPolynomial.eval a).mapMatrix (PolynomialSystem.jacobianMatrix (factorEquations d F))
  have hM : M.det = 0 := by
    rw [← RingHom.map_det]
    exact hdet
  obtain ⟨h, hne, hker⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hM
  let D := coefficientDerivation (coordinateDirection d h)
  let A := monicPolynomial d a
  let H : k[X] := ∑ j : Fin d, C (h j) * X ^ (d - (j.val + 1))
  let Z := (D (factorQuotient d F)).map (MvPolynomial.eval a)
  let T := (D (factorRemainder d F)).map (MvPolynomial.eval a)
  have hTdeg : T.degree < (d : WithBot ℕ) := by
    apply degree_map_le.trans_lt
    apply (coefficientDerivation_degree_le _ _).trans_lt
    have hd := degree_modByMonic_lt (F.map (MvPolynomial.C : k →+* MvPolynomial (Fin d) k))
      (universalMonicOver_monic k d)
    simpa only [factorRemainder, universalMonicOver, monicPolynomial_degree] using hd
  have hTzero : T = 0 := by
    apply Polynomial.ext
    intro n
    rw [coeff_zero]
    by_cases hn : n < d
    · have hr := congrFun hker ⟨n, hn⟩
      change (∑ j : Fin d, h j * MvPolynomial.eval a
        (MvPolynomial.pderiv j ((factorRemainder d F).coeff n))) = 0 at hr
      change ((D (factorRemainder d F)).map (MvPolynomial.eval a)).coeff n = 0
      rw [coeff_map, coefficientDerivation_coeff, coordinateDirection_apply, map_sum]
      simpa only [map_mul, MvPolynomial.eval_C] using hr
    · exact coeff_eq_zero_of_degree_lt (hTdeg.trans_le (WithBot.coe_le_coe.mpr (Nat.le_of_not_gt hn)))
  have he := congrArg (fun P : (MvPolynomial (Fin d) k)[X] => (D P).map (MvPolynomial.eval a))
    (modByMonic_add_div (F.map (MvPolynomial.C : k →+* MvPolynomial (Fin d) k)) (universalMonicOver k d))
  change (D (factorRemainder d F + universalMonicOver k d * factorQuotient d F)).map
    (MvPolynomial.eval a) = (D (F.map (algebraMap k (MvPolynomial (Fin d) k)))).map (MvPolynomial.eval a) at he
  simp only [D, map_add, Derivation.leibniz, smul_eq_mul, coefficientDerivation_algebraMap,
    Polynomial.map_zero, Polynomial.map_add, Polynomial.map_mul, universalMonicOver_eval,
    factorQuotient_eval, coordinateDirection_universal_eval] at he
  change T + (A * Z + (F /ₘ A) * H) = 0 at he
  rw [hTzero, zero_add] at he
  have hAH : A ∣ (F /ₘ A) * H := by
    refine ⟨-Z, ?_⟩
    linear_combination he
  have hprod : A * (F /ₘ A) = F := by
    have hr : F %ₘ A = 0 := (modByMonic_eq_zero_iff_dvd (monicPolynomial_monic d a)).mpr hdiv
    simpa only [hr, zero_add] using modByMonic_add_div F A
  have hSepProd : (A * (F /ₘ A)).Separable := by rw [hprod]; exact hsep
  have hHdeg : H.degree < A.degree := by
    rw [monicPolynomial_degree]
    exact degree_lowerTerms_lt d h
  have hHzero : H = 0 := separable_factor_tangent_trivial hSepProd hHdeg hAH
  apply hne
  apply monicPolynomial_injective d
  change X ^ d + H = X ^ d + ∑ j : Fin d, C ((0 : Fin d → k) j) * X ^ (d - (j.val + 1))
  simp only [hHzero, Pi.zero_apply, C_0, zero_mul, Finset.sum_const_zero]

end PolynomialRigidity.Enumeration
