import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic

/-!
# Valuations used in the prime-index argument

Every characteristic-zero field has a valuation whose residue characteristic
is any prescribed prime. Normalising at a root of maximal valuation then
makes all the coefficients of a monic split polynomial integral.
-/

noncomputable section

open Polynomial

namespace PolynomialRigidity

variable {K : Type*} [Field K]

/-- A valuation above a prescribed rational prime, even for transcendental fields. -/
theorem exists_prime_valuation [CharZero K] {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ V : ValuationSubring K, V.valuation (ℓ : K) < 1 := by
  let ZK : Subring K := (Int.castRingHom K).range
  have hn : ¬ IsUnit (ℓ : ZK) := by
    intro hu
    obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp hu
    obtain ⟨a, ha⟩ := z.property
    have he : (ℓ : K) * (a : K) = 1 := by
      simpa [← ha] using congrArg (fun x : ZK => (x : K)) hz
    have he' : (ℓ : ℤ) * a = 1 := by exact_mod_cast he
    have hu' : IsUnit (ℓ : ℤ) := IsUnit.of_mul_eq_one a he'
    have h1 : ℓ = 1 := by simpa only [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] using hu'
    exact hℓ.ne_one h1
  obtain ⟨V, _, hV⟩ :=
    (Ideal.span ({(ℓ : ZK)} : Set ZK)).image_subset_nonunits_valuationSubring
      (Ideal.span_singleton_ne_top hn)
  refine ⟨V, V.mem_nonunits_iff.mp (hV ?_)⟩
  exact ⟨(ℓ : ZK), Ideal.subset_span (by simp), by simp⟩

/-- Factorials below the residue characteristic are valuation units. -/
theorem valuation_factorial_eq_one (V : ValuationSubring K) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hvℓ : V.valuation (ℓ : K) < 1) {n : ℕ} (hn : n < ℓ) :
    V.valuation (n.factorial : K) = 1 := by
  have hp : (ℓ : V) ∈ IsLocalRing.maximalIdeal V :=
    (V.valuation_lt_one_iff (ℓ : V)).mpr (by simpa using hvℓ)
  have hp0 : (ℓ : IsLocalRing.ResidueField V) = 0 := by
    simpa only [map_natCast] using (IsLocalRing.residue_eq_zero_iff (ℓ : V)).mpr hp
  let : CharP (IsLocalRing.ResidueField V) ℓ := (CharP.charP_iff_prime_eq_zero hℓ).mpr hp0
  have hf : (n.factorial : IsLocalRing.ResidueField V) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff, hℓ.dvd_factorial]
    exact hn.not_ge
  have hu : IsUnit (n.factorial : V) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by simpa only [map_natCast] using hf)
  simpa using (V.valuation_eq_one_iff (n.factorial : V)).mp hu

/-- If every root is integral, so is every coefficient of a monic polynomial. -/
theorem valuation_coeff_le_one (V : ValuationSubring K) {A : K[X]} (hA : A.Monic)
    (hsplit : A.Splits) (hr : ∀ r ∈ A.roots, V.valuation r ≤ 1) (i : ℕ) :
    V.valuation (A.coeff i) ≤ 1 := by
  have hl := hsplit.mem_lift_of_roots_mem_range hA V.subtype (fun r hr' =>
    ⟨⟨r, (V.valuation_le_one_iff r).mp (hr r hr')⟩, rfl⟩)
  obtain ⟨a, ha⟩ := (Polynomial.lifts_iff_coeff_lifts A).mp hl i
  rw [← ha]
  exact V.valuation_le_one a

/-- Scaling by the inverse of a largest root makes all coefficients integral. -/
theorem valuation_coeff_scaleRoots_le_one (V : ValuationSubring K) {A : K[X]}
    (hA : A.Monic) (hsplit : A.Splits) {r : K} (hr : r ≠ 0)
    (hmax : ∀ z ∈ A.roots, V.valuation z ≤ V.valuation r) (i : ℕ) :
    V.valuation ((A.scaleRoots r⁻¹).coeff i) ≤ 1 := by
  apply valuation_coeff_le_one V ((A.monic_scaleRoots_iff _).mpr hA)
    (hsplit.scaleRoots _)
  intro z hz
  rw [roots_scaleRoots A (isUnit_iff_ne_zero.mpr (inv_ne_zero hr))] at hz
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
  rw [map_mul, map_inv₀, mul_comm, ← div_eq_mul_inv]
  exact (div_le_one₀ (by simpa using (V.valuation.pos_iff.mpr hr))).mpr (hmax y hy)

end PolynomialRigidity
