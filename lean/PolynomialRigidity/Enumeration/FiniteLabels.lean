import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Data.Finset.Powerset
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# Finite-field labels for prime enumeration

Monic degree-`d` divisors of a split separable polynomial are exactly its
`d`-element root subsets. In particular, the prime special fibre has the
required binomial number of labels. This is only the special-fibre step;
the characteristic-zero lifting and exhaustion argument is separate.
-/

noncomputable section

open Polynomial Finset
open scoped Classical

namespace PolynomialRigidity.Enumeration

variable {K : Type*} [Field K]

def MonicDivisorsOfDegree (F : K[X]) (d : ℕ) :=
  {A : K[X] // A.Monic ∧ A.natDegree = d ∧ A ∣ F}

/-- Divisors correspond to subsets of roots with the prescribed cardinality. -/
def monicDivisorsRootEquiv (F : K[X]) (d : ℕ) (hF : F ≠ 0)
    (hsplit : F.Splits) (hsep : F.Separable) :
    MonicDivisorsOfDegree F d ≃ ↥(F.roots.toFinset.powersetCard d) where
  toFun A := ⟨A.val.roots.toFinset, Finset.mem_powersetCard.mpr ⟨by
    intro x hx
    exact Multiset.mem_toFinset.mpr
      (Multiset.mem_of_le (Polynomial.roots.le_of_dvd hF A.property.2.2)
        (Multiset.mem_toFinset.mp hx)), by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots (hsep.of_dvd A.property.2.2)),
      ← (hsplit.of_dvd hF A.property.2.2).natDegree_eq_card_roots]
    exact A.property.2.1⟩⟩
  invFun s := ⟨∏ x ∈ s.val, (X - C x),
    monic_prod_X_sub_C (fun x : K => x) s.val,
    (natDegree_finsetProd_X_sub_C_eq_card s.val (fun x : K => x)).trans
      (Finset.mem_powersetCard.mp s.property).2, by
    change (s.val.val.map (fun x : K => X - C x)).prod ∣ F
    apply (Multiset.prod_X_sub_C_dvd_iff_le_roots hF _).mpr
    apply (Multiset.le_iff_subset s.val.nodup).mpr
    intro x hx
    exact Multiset.mem_toFinset.mp ((Finset.mem_powersetCard.mp s.property).1 hx)⟩
  left_inv A := by
    apply Subtype.ext
    change (∏ x ∈ A.val.roots.toFinset, (X - C x)) = A.val
    rw [Finset.prod, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr (Polynomial.nodup_roots (hsep.of_dvd A.property.2.2))]
    exact ((hsplit.of_dvd hF A.property.2.2).eq_prod_roots_of_monic A.property.1).symm
  right_inv s := by
    apply Subtype.ext
    change (∏ x ∈ s.val, (X - C x)).roots.toFinset = s.val
    rw [roots_prod_X_sub_C, Finset.val_toFinset]

theorem monicDivisors_finite_and_card (F : K[X]) (d : ℕ) (hF : F ≠ 0)
    (hsplit : F.Splits) (hsep : F.Separable) :
    Finite (MonicDivisorsOfDegree F d) ∧
      Nat.card (MonicDivisorsOfDegree F d) = F.natDegree.choose d := by
  let e := monicDivisorsRootEquiv F d hF hsplit hsep
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  calc
    Nat.card (MonicDivisorsOfDegree F d) = Nat.card ↥(F.roots.toFinset.powersetCard d) :=
      Nat.card_congr e
    _ = (F.roots.toFinset.powersetCard d).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = F.natDegree.choose d := by
      rw [Finset.card_powersetCard, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
        ← hsplit.natDegree_eq_card_roots]

/-- The reduced equations have no nonzero infinitesimal deformation. -/
theorem separable_factor_tangent_trivial {A C h : K[X]}
    (hsep : (A * C).Separable) (hdeg : h.degree < A.degree) (hdiv : A ∣ C * h) : h = 0 :=
  eq_zero_of_dvd_of_degree_lt (hsep.isCoprime.dvd_of_dvd_mul_left hdiv) hdeg

/-- Uniform binomial count for the special fibre over any field of characteristic `ℓ`. -/
theorem prime_special_fibre_count (ℓ d : ℕ) [hℓ : Fact ℓ.Prime] [CharP K ℓ] :
    Finite (MonicDivisorsOfDegree (X ^ ℓ - X : K[X]) d) ∧
      Nat.card (MonicDivisorsOfDegree (X ^ ℓ - X : K[X]) d) = ℓ.choose d := by
  have hsplit : (X ^ ℓ - X : K[X]).Splits := by
    simpa only [Polynomial.map_sub, Polynomial.map_pow, map_X] using
      (Subfield.splits_bot K ℓ).map (Subfield.subtype (⊥ : Subfield K))
  have hsep : (X ^ ℓ - X : K[X]).Separable := galois_poly_separable ℓ ℓ (dvd_refl ℓ)
  simpa only [FiniteField.X_pow_card_sub_X_natDegree_eq K hℓ.out.one_lt] using
    monicDivisors_finite_and_card (X ^ ℓ - X : K[X]) d
      (FiniteField.X_pow_card_sub_X_ne_zero K hℓ.out.one_lt) hsplit hsep

end PolynomialRigidity.Enumeration
