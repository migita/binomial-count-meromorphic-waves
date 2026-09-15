import PolynomialRigidity.EnumerationStatement

/-!
# Specialisation of the matching equations

The statements in `EnumerationStatement` remain unchanged. This file proves
that their universal monic polynomial and remainder specialise to the intended
complex polynomial and its discrete-convolution remainder.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

section MonicCoordinates

variable {R S : Type*} [CommRing R] [CommRing S]

theorem degree_lowerTerms_lt (d : ℕ) (a : Fin d → R) :
    (∑ j : Fin d, C (a j) * X ^ (d - (j.val + 1))).degree < (d : WithBot ℕ) := by
  apply (degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe d)).mpr
  intro j hj
  apply (degree_C_mul_X_pow_le (d - (j.val + 1)) (a j)).trans_lt
  exact WithBot.coe_lt_coe.mpr
    (show d - (j.val + 1) < d from by have := j.is_lt; omega)

theorem monicPolynomial_monic (d : ℕ) (a : Fin d → R) :
    (monicPolynomial d a).Monic :=
  monic_X_pow_add (degree_lowerTerms_lt d a)

@[simp]
theorem monicPolynomial_degree [Nontrivial R] (d : ℕ) (a : Fin d → R) :
    (monicPolynomial d a).degree = (d : WithBot ℕ) := by
  rw [monicPolynomial, degree_add_eq_left_of_degree_lt]
  · exact degree_X_pow d
  · simpa only [degree_X_pow] using degree_lowerTerms_lt d a

@[simp]
theorem monicPolynomial_natDegree [Nontrivial R] (d : ℕ) (a : Fin d → R) :
    (monicPolynomial d a).natDegree = d :=
  natDegree_eq_of_degree_eq_some (monicPolynomial_degree d a)

@[simp]
theorem monicPolynomial_map (f : R →+* S) (d : ℕ) (a : Fin d → R) :
    (monicPolynomial d a).map f = monicPolynomial d (fun j => f (a j)) := by
  simp only [monicPolynomial, Polynomial.map_add, Polynomial.map_pow, map_X,
    Polynomial.map_sum, Polynomial.map_mul, map_C]

theorem monicPolynomial_coeff (d : ℕ) (a : Fin d → R) (j : Fin d) :
    (monicPolynomial d a).coeff (d - (j.val + 1)) = a j := by
  have hj : d - (j.val + 1) ≠ d := by have := j.is_lt; omega
  simp only [monicPolynomial, C_mul_X_pow_eq_monomial, coeff_add, coeff_X_pow,
    if_neg hj, zero_add, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    have hne : d - (k.val + 1) ≠ d - (j.val + 1) := by
      intro heq
      apply hkj
      apply Fin.ext
      have := k.is_lt
      have := j.is_lt
      omega
    simp [hne]
  · simp

theorem monicPolynomial_injective (d : ℕ) :
    Function.Injective (monicPolynomial (R := R) d) := by
  intro a b hab
  funext j
  simpa only [monicPolynomial_coeff] using
    congrArg (fun F : R[X] => F.coeff (d - (j.val + 1))) hab

theorem monicPolynomial_eq_of_monic [Nontrivial R] {d : ℕ} (A : R[X]) (hA : A.Monic)
    (hdeg : A.natDegree = d) :
    monicPolynomial d (fun j => A.coeff (d - (j.val + 1))) = A := by
  apply Polynomial.ext
  intro n
  rcases lt_trichotomy n d with hn | hnd | hn
  · let j : Fin d := ⟨d - (n + 1), by omega⟩
    have hj : d - (j.val + 1) = n := by dsimp [j]; omega
    simpa only [hj] using monicPolynomial_coeff d (fun j => A.coeff (d - (j.val + 1))) j
  · subst n
    have hleft := (monicPolynomial_monic d (fun j => A.coeff (d - (j.val + 1)))).coeff_natDegree
    have hright := hA.coeff_natDegree
    simpa only [monicPolynomial_natDegree, hdeg] using hleft.trans hright.symm
  · rw [coeff_eq_zero_of_natDegree_lt (by simpa only [monicPolynomial_natDegree] using hn),
      coeff_eq_zero_of_natDegree_lt (by simpa only [hdeg] using hn)]

end MonicCoordinates

section ConvolutionMaps

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]

theorem discreteConvolution_eq_sum_of_support_subset (F G : R[X])
    {s t : Finset ℕ} (hF : F.support ⊆ s) (hG : G.support ⊆ t) :
    discreteConvolution F G = ∑ i ∈ s, ∑ j ∈ t,
      C (F.coeff i * G.coeff j) * (discreteMonomial i j).map (algebraMap ℚ R) := by
  change F.sum (fun i a => G.sum (fun j b =>
    C (a * b) * (discreteMonomial i j).map (algebraMap ℚ R))) = _
  rw [Polynomial.sum_eq_of_subset _ (fun i => by simp [Polynomial.sum_def]) hF]
  apply Finset.sum_congr rfl
  intro i hi
  exact Polynomial.sum_eq_of_subset _ (fun j => by simp) hG

theorem discreteConvolution_map (f : R →ₐ[ℚ] S) (F G : R[X]) :
    (discreteConvolution F G).map f.toRingHom =
      discreteConvolution (F.map f.toRingHom) (G.map f.toRingHom) := by
  rw [discreteConvolution_eq_sum_of_support_subset (F.map f.toRingHom)
    (G.map f.toRingHom) (support_map_subset _ _) (support_map_subset _ _)]
  have hcomp : f.toRingHom.comp (algebraMap ℚ R) = algebraMap ℚ S :=
    RingHom.ext f.commutes
  simp only [discreteConvolution, Polynomial.map_sum, Polynomial.map_mul, map_C,
    Polynomial.map_map, hcomp, coeff_map, map_mul]

end ConvolutionMaps

@[simp]
theorem coefficientPolynomial_monic (p : ℕ) (a : Coefficients p) :
    (coefficientPolynomial p a).Monic :=
  monicPolynomial_monic _ _

@[simp]
theorem coefficientPolynomial_natDegree (p : ℕ) (a : Coefficients p) :
    (coefficientPolynomial p a).natDegree = p - 1 :=
  monicPolynomial_natDegree _ _

@[simp]
theorem coefficientPolynomial_degree (p : ℕ) (a : Coefficients p) :
    (coefficientPolynomial p a).degree = ((p - 1 : ℕ) : WithBot ℕ) :=
  monicPolynomial_degree _ _

theorem universalPolynomial_monic (p : ℕ) : (universalPolynomial p).Monic :=
  monicPolynomial_monic _ _

@[simp]
theorem universalPolynomial_map_eval (p : ℕ) (a : Coefficients p) :
    (universalPolynomial p).map (MvPolynomial.eval a) = coefficientPolynomial p a := by
  simp only [universalPolynomial, monicPolynomial_map, MvPolynomial.eval_X,
    coefficientPolynomial]

theorem universalRemainder_map_eval (p : ℕ) (a : Coefficients p) :
    (universalRemainder p).map (MvPolynomial.eval a) =
      discreteConvolution (coefficientPolynomial p a) (coefficientPolynomial p a) %ₘ
        coefficientPolynomial p a := by
  let f : ParameterRing p →ₐ[ℚ] ℂ :=
    { MvPolynomial.eval a with
      commutes' := fun r => by simp }
  have hmap := discreteConvolution_map f (universalPolynomial p) (universalPolynomial p)
  rw [universalRemainder, map_modByMonic _ (universalPolynomial_monic p), hmap]
  simp only [f, universalPolynomial_map_eval]

theorem remainderEquation_eval (p : ℕ) (a : Coefficients p) (r : Fin (p - 1)) :
    MvPolynomial.eval a (remainderEquation p r) =
      (discreteConvolution (coefficientPolynomial p a) (coefficientPolynomial p a) %ₘ
        coefficientPolynomial p a).coeff r.val := by
  rw [← universalRemainder_map_eval]
  exact (coeff_map _ _).symm

/-- The universal equations in the stated goal are exactly `A ∣ A ⋆ A`. -/
theorem matchingDivisibilityAtOrder (p : ℕ) : MatchingDivisibilityAtOrder p := by
  intro a
  rw [← modByMonic_eq_zero_iff_dvd (coefficientPolynomial_monic p a)]
  constructor
  · intro ha
    apply Polynomial.ext
    intro n
    rw [coeff_zero]
    by_cases hn : n < p - 1
    · exact (remainderEquation_eval p a ⟨n, hn⟩).symm.trans (ha ⟨n, hn⟩)
    · apply coeff_eq_zero_of_degree_lt
      apply (degree_modByMonic_lt _ (coefficientPolynomial_monic p a)).trans_le
      rw [coefficientPolynomial_degree]
      exact WithBot.coe_le_coe.mpr (Nat.le_of_not_gt hn)
  · intro hzero r
    rw [remainderEquation_eval, hzero, coeff_zero]

end PolynomialRigidity.Enumeration
