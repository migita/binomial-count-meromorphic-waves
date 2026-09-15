import PolynomialRigidity.Enumeration.UniversalEquations
import PolynomialRigidity.Enumeration.UniversalKernel
import PolynomialRigidity.Enumeration.FactorJacobian
import PolynomialRigidity.Enumeration.PrimeReduction

/-!
# The integral universal matching system

The falling-factorial formula uses only factorials below the prime index.
Its reduction is a fixed-factor remainder system, and its characteristic-zero
points satisfy the rational matching equations from the fixed specification.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

def integralKernelLeading (R : Type*) [CommRing R] (d : ℕ) : R :=
  (d.factorial : R) ^ 2 * Ring.inverse ((2 * d).factorial : R)

def integralKernelInverse (R : Type*) [CommRing R] (n : ℕ) : R :=
  Ring.inverse ((-1 : R) ^ n * (n.factorial : R))

def integralNormalizedKernel (R : Type*) [CommRing R] (d : ℕ) :
    (MvPolynomial (Fin d) R)[X] :=
  C (MvPolynomial.C (integralKernelLeading R d)) * spectralBasis (2 * d + 1) +
    C ((2 * d + 1 : ℕ) : MvPolynomial (Fin d) R) *
      ∑ n ∈ range (2 * d + 1),
        C ((-logisticTransform (universalMonicOver R d) *
          logisticTransform (universalMonicOver R d)).coeff (n + 1) *
          MvPolynomial.C (integralKernelInverse R n)) * spectralBasis n

def integralMatchingEquations (R : Type*) [CommRing R] (d : ℕ) (r : Fin d) :
    MvPolynomial (Fin d) R :=
  (integralNormalizedKernel R d %ₘ universalMonicOver R d).coeff r.val

theorem map_ringInverse_of_isUnit {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) {x : R} (hx : IsUnit x) :
    f (Ring.inverse x) = (f x)⁻¹ := by
  have hfx : f x ≠ 0 := (hx.map f).ne_zero
  apply mul_right_cancel₀ hfx
  rw [inv_mul_cancel₀ hfx, ← map_mul, Ring.inverse_mul_cancel _ hx, map_one]

theorem integralKernelLeading_map {R K : Type*} [CommRing R] [Field K] [CharZero K]
    (f : R →+* K) (d : ℕ) (hu : IsUnit ((2 * d).factorial : R)) :
    f (integralKernelLeading R d) =
      algebraMap ℚ K ((d.factorial : ℚ) ^ 2 / ((2 * d).factorial : ℚ)) := by
  rw [integralKernelLeading, map_mul, map_pow, map_natCast,
    map_ringInverse_of_isUnit f hu, map_natCast]
  simp only [div_eq_mul_inv, map_mul, map_pow, map_inv₀, map_natCast]

theorem integralKernelInverse_map {R K : Type*} [CommRing R] [Field K] [CharZero K]
    (f : R →+* K) (n : ℕ) (hu : IsUnit (n.factorial : R)) :
    f (integralKernelInverse R n) = inverseLogisticScalar (R := K) n := by
  have hs : IsUnit (-1 : R) := isUnit_one.neg
  rw [integralKernelInverse, map_ringInverse_of_isUnit f ((hs.pow n).mul hu)]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast,
    inverseLogisticScalar, map_inv₀]

theorem integralNormalizedKernel_eval₂ {R K : Type*} [CommRing R] [Field K] [CharZero K]
    (f : R →+* K) (d : ℕ)
    (hu : ∀ n < 2 * d + 1, IsUnit (n.factorial : R)) (a : Fin d → K) :
    (integralNormalizedKernel R d).map (MvPolynomial.eval₂Hom f a) =
      C ((2 * d + 1 : ℕ) : K) *
        discreteConvolution (monicPolynomial d a) (monicPolynomial d a) := by
  let e := MvPolynomial.eval₂Hom f a
  have hU := universalMonicOver_eval₂ f d a
  have hB : (-logisticTransform (universalMonicOver R d) *
      logisticTransform (universalMonicOver R d)).map e =
      -logisticTransform (monicPolynomial d a) * logisticTransform (monicPolynomial d a) := by
    simp only [Polynomial.map_mul, Polynomial.map_neg, logisticTransform_map, e, hU]
  have hnorm := normalizedConvolution_universal_formula (monicPolynomial_monic d a)
  simp only [monicPolynomial_natDegree] at hnorm
  rw [hnorm]
  simp only [integralNormalizedKernel, Polynomial.map_add, Polynomial.map_mul, map_C,
    spectralBasis_map, MvPolynomial.eval₂Hom_C, map_natCast, Polynomial.map_natCast, Polynomial.map_sum]
  rw [integralKernelLeading_map f d (hu _ (by omega))]
  apply congrArg (fun P : K[X] =>
    C (algebraMap ℚ K ((d.factorial : ℚ) ^ 2 / ((2 * d).factorial : ℚ))) *
      spectralBasis (2 * d + 1) + ((2 * d + 1 : ℕ) : K[X]) * P)
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul, MvPolynomial.eval₂Hom_C, integralKernelInverse_map f n (hu n (mem_range.mp hn))]
  have hc := congrArg (fun P : K[X] => P.coeff (n + 1)) hB
  rw [coeff_map] at hc
  rw [show MvPolynomial.eval₂Hom f a
      ((-logisticTransform (universalMonicOver R d) *
        logisticTransform (universalMonicOver R d)).coeff (n + 1)) =
      (-logisticTransform (monicPolynomial d a) *
        logisticTransform (monicPolynomial d a)).coeff (n + 1) from hc]

theorem integralMatchingEquations_eval₂ {R K : Type*} [CommRing R] [Field K] [CharZero K]
    (f : R →+* K) (d : ℕ)
    (hu : ∀ n < 2 * d + 1, IsUnit (n.factorial : R)) (a : Fin d → K) (r : Fin d) :
    MvPolynomial.eval₂Hom f a (integralMatchingEquations R d r) =
      ((2 * d + 1 : ℕ) : K) * MvPolynomial.aeval a (matchingEquationsOver ℚ d r) := by
  have hp : (integralNormalizedKernel R d %ₘ universalMonicOver R d).map
      (MvPolynomial.eval₂Hom f a) =
      ((2 * d + 1 : ℕ) : K) •
        (discreteConvolution (monicPolynomial d a) (monicPolynomial d a) %ₘ monicPolynomial d a) := by
    rw [map_modByMonic _ (universalMonicOver_monic R d),
      integralNormalizedKernel_eval₂ f d hu a, universalMonicOver_eval₂,
      ← smul_eq_C_mul, smul_modByMonic]
  have hc := congrArg (fun P : K[X] => P.coeff r.val) hp
  simpa only [coeff_map, coeff_smul, smul_eq_mul, integralMatchingEquations,
    rational_equation_eval] using hc

theorem integralNormalizedKernel_reduction {R k : Type*} [CommRing R] [Field k]
    (ρ : R →+* k) (d : ℕ) [Fact (2 * d + 1).Prime] [CharP k (2 * d + 1)] :
    (integralNormalizedKernel R d).map (MvPolynomial.map ρ) =
      (C (ρ (integralKernelLeading R d)) * (X ^ (2 * d + 1) - X)).map
        (MvPolynomial.C : k →+* MvPolynomial (Fin d) k) := by
  have hz : ((2 * d + 1 : ℕ) : (MvPolynomial (Fin d) k)[X]) = 0 := CharP.cast_eq_zero _ _
  have hs : spectralBasis (R := MvPolynomial (Fin d) k) (2 * d + 1) = X ^ (2 * d + 1) - X := by
    rw [← spectralBasis_map (MvPolynomial.C : k →+* MvPolynomial (Fin d) k), spectralBasis_prime]
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X]
  simp only [integralNormalizedKernel, Polynomial.map_add, Polynomial.map_mul, map_C,
    spectralBasis_map, MvPolynomial.map_C, map_natCast, Polynomial.map_natCast, hz, zero_mul, add_zero, hs,
    Polynomial.map_sub, Polynomial.map_pow, map_X]

theorem integralMatchingEquations_reduction {R k : Type*} [CommRing R] [Field k]
    (ρ : R →+* k) (d : ℕ) [Fact (2 * d + 1).Prime] [CharP k (2 * d + 1)] (r : Fin d) :
    MvPolynomial.map ρ (integralMatchingEquations R d r) =
      factorEquations d (C (ρ (integralKernelLeading R d)) * (X ^ (2 * d + 1) - X)) r := by
  have hp : (integralNormalizedKernel R d %ₘ universalMonicOver R d).map (MvPolynomial.map ρ) =
      factorRemainder d (C (ρ (integralKernelLeading R d)) * (X ^ (2 * d + 1) - X)) := by
    rw [map_modByMonic _ (universalMonicOver_monic R d), integralNormalizedKernel_reduction,
      universalMonicOver_map]
    rfl
  have hc := congrArg (fun P : (MvPolynomial (Fin d) k)[X] => P.coeff r.val) hp
  change MvPolynomial.map ρ ((integralNormalizedKernel R d %ₘ universalMonicOver R d).coeff r.val) = _
  exact (coeff_map _ _).symm.trans hc

theorem PolynomialSystem.jacobianPolynomial_map {R S σ : Type*} [CommRing R] [CommRing S]
    [Fintype σ] [DecidableEq σ] (φ : R →+* S) (f : σ → MvPolynomial σ R) :
    MvPolynomial.map φ (jacobianPolynomial f) =
      jacobianPolynomial (fun i => MvPolynomial.map φ (f i)) := by
  rw [jacobianPolynomial, RingHom.map_det]
  apply congrArg Matrix.det
  ext i j : 1
  exact MvPolynomial.pderiv_map.symm

theorem integralMatching_special_fibre {R k : Type*} [CommRing R] [Field k]
    (ρ : R →+* k) (d : ℕ) [Fact (2 * d + 1).Prime] [CharP k (2 * d + 1)]
    (hc : ρ (integralKernelLeading R d) ≠ 0) (a : Fin d → k)
    (ha : monicPolynomial d a ∣ X ^ (2 * d + 1) - X) :
    (∀ r, MvPolynomial.eval₂Hom ρ a (integralMatchingEquations R d r) = 0) ∧
      MvPolynomial.eval₂Hom ρ a
        (PolynomialSystem.jacobianPolynomial (integralMatchingEquations R d)) ≠ 0 := by
  have hdiv : monicPolynomial d a ∣ C (ρ (integralKernelLeading R d)) * (X ^ (2 * d + 1) - X) :=
    dvd_mul_of_dvd_right ha _
  have heq : (fun r => MvPolynomial.map ρ (integralMatchingEquations R d r)) =
      factorEquations d (C (ρ (integralKernelLeading R d)) * (X ^ (2 * d + 1) - X)) := by
    funext r
    exact integralMatchingEquations_reduction ρ d r
  constructor
  · intro r
    change MvPolynomial.eval₂ ρ a (integralMatchingEquations R d r) = 0
    rw [MvPolynomial.eval₂_eq_eval_map, integralMatchingEquations_reduction]
    exact factorEquations_zero_of_dvd d _ a hdiv r
  · change MvPolynomial.eval₂ ρ a
      (PolynomialSystem.jacobianPolynomial (integralMatchingEquations R d)) ≠ 0
    rw [MvPolynomial.eval₂_eq_eval_map, PolynomialSystem.jacobianPolynomial_map, heq]
    apply factorJacobian_ne_zero d _ _ a hdiv
    exact Separable.unit_mul ((isUnit_iff_ne_zero.mpr hc).map C)
      (galois_poly_separable (2 * d + 1) (2 * d + 1) (dvd_refl _))

theorem factorial_isUnit_of_residue_char {R : Type*} [CommRing R] [IsLocalRing R]
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [CharP (IsLocalRing.ResidueField R) ℓ]
    (n : ℕ) (hn : n < ℓ) : IsUnit (n.factorial : R) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  rw [map_natCast, ne_eq, CharP.cast_eq_zero_iff _ ℓ, hℓ.out.dvd_factorial]
  exact Nat.not_le.mpr hn

theorem integralKernelLeading_isUnit {R : Type*} [CommRing R] (d : ℕ)
    (hu : ∀ n < 2 * d + 1, IsUnit (n.factorial : R)) : IsUnit (integralKernelLeading R d) := by
  exact ((hu d (by omega)).pow 2).mul (hu (2 * d) (by omega)).ringInverse

end PolynomialRigidity.Enumeration
