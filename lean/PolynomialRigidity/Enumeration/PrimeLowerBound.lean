import PolynomialRigidity.Enumeration.IntegralMatchingSystem
import PolynomialRigidity.Enumeration.PrimeUpperBound
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Lifting every prime label and the binomial lower bound

Every monic divisor in the special fibre lifts through the integral matching
system. Distinct residue labels give distinct characteristic-zero solutions.
A finite rational polynomial-system transfer then gives the required family
in the actual complex matching solution type.
-/

noncomputable section

open Polynomial

namespace PolynomialRigidity.Enumeration

theorem integralMatching_lift {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (d : ℕ) [Fact (2 * d + 1).Prime] [CharP (IsLocalRing.ResidueField R) (2 * d + 1)]
    (a₀ : Fin d → IsLocalRing.ResidueField R)
    (ha₀ : monicPolynomial d a₀ ∣ X ^ (2 * d + 1) - X) :
    ∃ a : Fin d → R, (∀ r, MvPolynomial.eval a (integralMatchingEquations R d r) = 0) ∧
      ∀ j, IsLocalRing.residue R (a j) = a₀ j := by
  have hu : ∀ n < 2 * d + 1, IsUnit (n.factorial : R) :=
    factorial_isUnit_of_residue_char (2 * d + 1)
  have hc : IsLocalRing.residue R (integralKernelLeading R d) ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (integralKernelLeading_isUnit d hu)
  have hsys := integralMatching_special_fibre (IsLocalRing.residue R) d hc a₀ ha₀
  exact PolynomialSystem.hensel_simple_system (integralMatchingEquations R d) a₀ hsys.1 hsys.2

theorem integralMatching_maps_to_rational {R K : Type*} [CommRing R] [Field K] [CharZero K]
    (f : R →+* K) (d : ℕ) (hu : ∀ n < 2 * d + 1, IsUnit (n.factorial : R))
    (a : Fin d → R) (ha : ∀ r, MvPolynomial.eval a (integralMatchingEquations R d r) = 0) :
    RationalMatching d (fun j => f (a j)) := by
  intro r
  have heval : MvPolynomial.eval₂Hom f (fun j => f (a j)) (integralMatchingEquations R d r) =
      f (MvPolynomial.eval a (integralMatchingEquations R d r)) := by
    rw [MvPolynomial.map_eval, MvPolynomial.eval_map]
    rfl
  have he := integralMatchingEquations_eval₂ f d hu (fun j => f (a j)) r
  rw [heval, ha r, map_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (by exact_mod_cast (by omega : 2 * d + 1 ≠ 0))

theorem exists_injective_lifted_matching_family {R K : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field K] [CharZero K]
    (f : R →+* K) (hf : Function.Injective f) (d : ℕ)
    [Fact (2 * d + 1).Prime] [CharP (IsLocalRing.ResidueField R) (2 * d + 1)] :
    ∃ a : MonicDivisorsOfDegree (X ^ (2 * d + 1) - X : (IsLocalRing.ResidueField R)[X]) d →
        Fin d → K,
      Function.Injective a ∧ ∀ A, RationalMatching d (a A) := by
  let L := MonicDivisorsOfDegree (X ^ (2 * d + 1) - X : (IsLocalRing.ResidueField R)[X]) d
  let a₀ : L → Fin d → IsLocalRing.ResidueField R := fun A j => A.val.coeff (d - (j.val + 1))
  have hA₀ (A : L) : monicPolynomial d (a₀ A) = A.val :=
    monicPolynomial_eq_of_monic A.val A.property.1 A.property.2.1
  have hdiv (A : L) : monicPolynomial d (a₀ A) ∣ X ^ (2 * d + 1) - X := by
    rw [hA₀]
    exact A.property.2.2
  have hlift (A : L) := integralMatching_lift d (a₀ A) (hdiv A)
  choose a ha hres using hlift
  refine ⟨fun A j => f (a A j), ?_, ?_⟩
  · intro A B he
    have hab : a₀ A = a₀ B := by
      funext j
      rw [← hres A j, ← hres B j]
      exact congrArg (IsLocalRing.residue R) (hf (congrFun he j))
    apply Subtype.ext
    rw [← hA₀ A, ← hA₀ B, hab]
  · intro A
    exact integralMatching_maps_to_rational f d
      (factorial_isUnit_of_residue_char (2 * d + 1)) (a A) (ha A)

theorem padicResidueField_charP (ℓ : ℕ) [hℓ : Fact ℓ.Prime] :
    CharP (IsLocalRing.ResidueField ℤ_[ℓ]) ℓ := by
  apply (CharP.charP_iff_prime_eq_zero hℓ.out).mpr
  have hz : IsLocalRing.residue ℤ_[ℓ] (ℓ : ℤ_[ℓ]) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr PadicInt.p_nonunit
  simpa only [map_natCast] using hz

/-- Every finite-field label supplies a distinct complex solution of the fixed rational equations. -/
theorem prime_index_card_ge {p : ℕ} (hp : 2 ≤ p) (hprime : (2 * p - 1).Prime) :
    expectedCount p ≤ Nat.card (MatchingSolutions p) := by
  let d := p - 1
  have he : 2 * d + 1 = 2 * p - 1 := by dsimp [d]; omega
  let : Fact (2 * d + 1).Prime := ⟨by simpa only [he] using hprime⟩
  let R := ℤ_[2 * d + 1]
  let K := ℚ_[2 * d + 1]
  let : CharP (IsLocalRing.ResidueField R) (2 * d + 1) := padicResidueField_charP (2 * d + 1)
  let L := MonicDivisorsOfDegree (X ^ (2 * d + 1) - X : (IsLocalRing.ResidueField R)[X]) d
  have hlabels := prime_special_fibre_count (K := IsLocalRing.ResidueField R) (2 * d + 1) d
  let : Finite L := hlabels.1
  have hf : Function.Injective (algebraMap R K) := by
    intro a b hab
    exact Subtype.ext hab
  obtain ⟨a, ha, hmatch⟩ := exists_injective_lifted_matching_family (algebraMap R K) hf d
  obtain ⟨b, hb⟩ := matching_family_in_complex p a ha hmatch
  let : Finite (MatchingSolutions p) := (prime_index_finite_and_card_le hp hprime).1
  have hcard := Nat.card_le_card_of_injective b hb
  rw [hlabels.2] at hcard
  simpa only [expectedCount, d, he] using hcard

end PolynomialRigidity.Enumeration
