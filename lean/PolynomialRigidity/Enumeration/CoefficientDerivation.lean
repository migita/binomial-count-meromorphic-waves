import PolynomialRigidity.Enumeration.Basic
import PolynomialRigidity.Enumeration.LogisticPolynomial
import Mathlib.RingTheory.Derivation.MapCoeffs

/-!
# Differentiating the universal matching equations

The coefficient-wise derivation preserves the spectral variable. In
particular it differentiates the discrete convolution by the bilinear
product rule, and the derivatives of the universal polynomial are exactly
the monomials corresponding to the stated descending coordinates.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

section GeneralDerivation

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

def coefficientDerivation (D : Derivation R S S) : Derivation R S[X] S[X] :=
  PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs

@[simp]
theorem coefficientDerivation_coeff (D : Derivation R S S) (F : S[X]) (n : ℕ) :
    (coefficientDerivation D F).coeff n = D (F.coeff n) := rfl

@[simp]
theorem coefficientDerivation_monomial (D : Derivation R S S) (n : ℕ) (c : S) :
    coefficientDerivation D (monomial n c) = monomial n (D c) := by
  ext k
  by_cases h : n = k <;> simp [coefficientDerivation_coeff, coeff_monomial, h]

@[simp]
theorem coefficientDerivation_C (D : Derivation R S S) (c : S) :
    coefficientDerivation D (C c) = C (D c) := by
  exact coefficientDerivation_monomial D 0 c

@[simp]
theorem coefficientDerivation_X_pow (D : Derivation R S S) (n : ℕ) :
    coefficientDerivation D (X ^ n) = 0 := by
  rw [X_pow_eq_monomial, coefficientDerivation_monomial, D.map_one_eq_zero, monomial_zero_right]

theorem coefficientDerivation_C_mul_X_pow (D : Derivation R S S) (n : ℕ) (c : S) :
    coefficientDerivation D (C c * X ^ n) = C (D c) * X ^ n := by
  rw [C_mul_X_pow_eq_monomial, coefficientDerivation_monomial, C_mul_X_pow_eq_monomial]

theorem coefficientDerivation_support_subset (D : Derivation R S S) (F : S[X]) :
    (coefficientDerivation D F).support ⊆ F.support := by
  intro n hn
  apply mem_support_iff.mpr
  intro hz
  have hne := mem_support_iff.mp hn
  rw [coefficientDerivation_coeff, hz, map_zero] at hne
  exact hne rfl

theorem coefficientDerivation_degree_le (D : Derivation R S S) (F : S[X]) :
    (coefficientDerivation D F).degree ≤ F.degree :=
  Finset.sup_mono (coefficientDerivation_support_subset D F)

@[simp]
theorem coefficientDerivation_algebraMap (D : Derivation R S S) (F : R[X]) :
    coefficientDerivation D (F.map (algebraMap R S)) = 0 := by
  ext n
  rw [coefficientDerivation_coeff, coeff_map, D.map_algebraMap, coeff_zero]

theorem coefficientDerivation_monicPolynomial (D : Derivation R S S) (d : ℕ) (a : Fin d → S) :
    coefficientDerivation D (monicPolynomial d a) =
      ∑ j : Fin d, C (D (a j)) * X ^ (d - (j.val + 1)) := by
  simp only [monicPolynomial, map_add, map_sum, coefficientDerivation_X_pow, zero_add,
    coefficientDerivation_C_mul_X_pow]

end GeneralDerivation

section RationalDerivation

variable {S : Type*} [CommRing S] [Algebra ℚ S]

@[simp]
theorem coefficientDerivation_ratMap (D : Derivation ℚ S S) (F : ℚ[X]) :
    coefficientDerivation D (F.map (algebraMap ℚ S)) = 0 :=
  coefficientDerivation_algebraMap D F

theorem coefficientDerivation_discreteConvolution (D : Derivation ℚ S S) (F G : S[X]) :
    coefficientDerivation D (discreteConvolution F G) =
      discreteConvolution (coefficientDerivation D F) G +
        discreteConvolution F (coefficientDerivation D G) := by
  rw [discreteConvolution_eq_sum_of_support_subset (coefficientDerivation D F) G
    (coefficientDerivation_support_subset D F) (Finset.Subset.refl _)]
  rw [discreteConvolution_eq_sum_of_support_subset F (coefficientDerivation D G)
    (Finset.Subset.refl _) (coefficientDerivation_support_subset D G)]
  simp only [discreteConvolution, map_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Derivation.leibniz, smul_eq_mul, coefficientDerivation_ratMap,
    coefficientDerivation_C, coefficientDerivation_coeff, mul_zero, zero_add,
    map_mul]
  ring

end RationalDerivation

def parameterDerivation (p : ℕ) (j : Fin (p - 1)) :
    Derivation ℚ (ParameterRing p) (ParameterRing p) :=
  (MvPolynomial.pderiv j).restrictScalars ℚ

@[simp]
theorem parameterDerivation_apply (p : ℕ) (j : Fin (p - 1)) (F : ParameterRing p) :
    parameterDerivation p j F = MvPolynomial.pderiv j F := rfl

theorem coefficientDerivation_universalPolynomial (p : ℕ) (j : Fin (p - 1)) :
    coefficientDerivation (parameterDerivation p j) (universalPolynomial p) =
      X ^ (p - 1 - (j.val + 1)) := by
  classical
  rw [universalPolynomial, coefficientDerivation_monicPolynomial]
  simp only [parameterDerivation_apply, MvPolynomial.pderiv_X]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [hij]
  · simp

/-- These coefficients are exactly the entries of the Jacobian named in the goal. -/
theorem coefficientDerivation_remainder_eval_coeff (p : ℕ) (a : Coefficients p)
    (r j : Fin (p - 1)) :
    ((coefficientDerivation (parameterDerivation p j) (universalRemainder p)).map
      (MvPolynomial.eval a)).coeff r.val = matchingJacobian p a r j := by
  rw [coeff_map, coefficientDerivation_coeff, parameterDerivation_apply]
  rfl

theorem discreteConvolution_comm (A B : ℂ[X]) : discreteConvolution A B = discreteConvolution B A := by
  apply logisticTransform_injective
  rw [logisticTransform_discreteConvolution, logisticTransform_discreteConvolution]
  ring

end PolynomialRigidity.Enumeration
