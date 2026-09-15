import PolynomialRigidity.Enumeration.PrimeConvolutionKernel
import PolynomialRigidity.Enumeration.FiniteLabels

/-!
# The prime collapse of the discrete convolution

The integral normalised convolution reduces to a nonzero scalar multiple of
`X^ℓ-X`, independently of the nonleading coefficients of the monic input.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

theorem spectralBasis_prime_zmod (ℓ : ℕ) [hℓ : Fact ℓ.Prime] :
    spectralBasis (R := ZMod ℓ) ℓ = X ^ ℓ - X := by
  classical
  let : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have heval : ∀ a : ZMod ℓ, (spectralBasis (R := ZMod ℓ) ℓ).eval a = 0 := by
    intro a
    rw [spectralBasis, eval_prod]
    apply Finset.prod_eq_zero_iff.mpr
    by_cases ha : a = 0
    · refine ⟨ℓ, Finset.mem_Ico.mpr ⟨by have := hℓ.out.two_le; omega, by omega⟩, ?_⟩
      simp [ha]
    · refine ⟨a.val, Finset.mem_Ico.mpr ⟨ZMod.val_pos.mpr ha, (ZMod.val_lt a).trans (by omega)⟩, ?_⟩
      simp
  have hsplit : (X ^ ℓ - X : (ZMod ℓ)[X]).Splits := by
    simpa only [Nat.card_zmod] using
      (Polynomial.splits_X_pow_nat_card_sub_X (K := ZMod ℓ))
  have hmonic : (X ^ ℓ - X : (ZMod ℓ)[X]).Monic := by
    have hdeg : (-X : (ZMod ℓ)[X]).degree < (ℓ : WithBot ℕ) := by
      rw [degree_neg, degree_X]
      exact WithBot.coe_lt_coe.mpr hℓ.out.one_lt
    simpa only [sub_eq_add_neg] using monic_X_pow_add hdeg
  have hsep : (X ^ ℓ - X : (ZMod ℓ)[X]).Separable := galois_poly_separable ℓ ℓ (dvd_refl ℓ)
  have hdiv : (X ^ ℓ - X : (ZMod ℓ)[X]) ∣ spectralBasis ℓ := by
    rw [hsplit.eq_prod_roots_of_monic hmonic]
    apply (Multiset.prod_X_sub_C_dvd_iff_le_roots (spectralBasis_monic ℓ).ne_zero _).mpr
    apply (Multiset.le_iff_subset (Polynomial.nodup_roots hsep)).mpr
    intro a ha
    exact (Polynomial.mem_roots (spectralBasis_monic ℓ).ne_zero).mpr (heval a)
  apply eq_of_monic_of_dvd_of_natDegree_le hmonic (spectralBasis_monic ℓ) hdiv
  rw [spectralBasis_natDegree, FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod ℓ) hℓ.out.one_lt]

theorem spectralBasis_prime {K : Type*} [Field K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] :
    spectralBasis (R := K) ℓ = X ^ ℓ - X := by
  have h := congrArg (Polynomial.map (ZMod.castHom (m := ℓ) dvd_rfl K)) (spectralBasis_prime_zmod ℓ)
  simpa only [spectralBasis_map, Polynomial.map_sub, Polynomial.map_pow, map_X] using h

theorem polynomialReduction_spectralBasis {K : Type*} [Field K] (V : ValuationSubring K) (n : ℕ) :
    polynomialReduction V (spectralBasis n) (IntegralCoefficients.spectralBasis n) =
      spectralBasis (R := IsLocalRing.ResidueField V) n := by
  have hl := integralLift_unique V (spectralBasis n) (IntegralCoefficients.spectralBasis n)
    (spectralBasis (R := V) n) (spectralBasis_map V.subtype n)
  rw [polynomialReduction, hl, spectralBasis_map]

/-- The full discrete prime congruence, with the surviving scalar explicitly nonzero. -/
theorem normalizedConvolution_reduction {K : Type*} [Field K] [CharZero K]
    (V : ValuationSubring K) {A : K[X]} (hA : A.Monic) (hAI : IntegralCoefficients V A)
    (hℓ : (2 * A.natDegree + 1).Prime)
    (hv : V.valuation ((2 * A.natDegree + 1 : ℕ) : K) < 1) :
    ∃ c : IsLocalRing.ResidueField V, c ≠ 0 ∧
      polynomialReduction V (C ((2 * A.natDegree + 1 : ℕ) : K) * discreteConvolution A A)
        (normalizedConvolution_integral V hA hAI hℓ hv) =
      C c * (X ^ (2 * A.natDegree + 1) - X) := by
  let ℓ := 2 * A.natDegree + 1
  let : Fact ℓ.Prime := ⟨hℓ⟩
  let : CharP (IsLocalRing.ResidueField V) ℓ := residueField_charP V hℓ hv
  let u : K := (ℓ : K) * beta A.natDegree A.natDegree
  have hu : V.valuation u = 1 := PolynomialRigidity.valuation_prime_mul_beta_self V hℓ hv
  have huV : u ∈ V := (V.valuation_le_one_iff _).mp hu.le
  let u₀ : V := ⟨u, huV⟩
  let c := IsLocalRing.residue V u₀
  have hc : c ≠ 0 := by
    intro hz
    have hsmall := (V.valuation_lt_one_iff u₀).mp ((IsLocalRing.residue_eq_zero_iff u₀).mp hz)
    change V.valuation u < 1 at hsmall
    rw [hu] at hsmall
    exact lt_irrefl _ hsmall
  let hTail := convolutionTail_integral V hAI hℓ hv
  let T₀ := integralLift V (convolutionTail A) hTail
  let F₀ : V[X] := C u₀ * spectralBasis ℓ + C (ℓ : V) * T₀
  have hF₀ : F₀.map V.subtype = C (ℓ : K) * discreteConvolution A A := by
    rw [normalizedConvolution_eq hA]
    simp only [F₀, T₀, Polynomial.map_add, Polynomial.map_mul, map_C, spectralBasis_map,
      integralLift_map, ValuationSubring.subtype_apply, map_natCast, Polynomial.map_natCast,
      u₀, u, ℓ]
  have hl := integralLift_unique V (C (ℓ : K) * discreteConvolution A A)
    (normalizedConvolution_integral V hA hAI hℓ hv) F₀ hF₀
  refine ⟨c, hc, ?_⟩
  change (integralLift V (C (ℓ : K) * discreteConvolution A A) _).map (IsLocalRing.residue V) = _
  rw [hl]
  simp only [F₀, Polynomial.map_add, Polynomial.map_mul, map_C, spectralBasis_map,
    map_natCast, Polynomial.map_natCast, CharP.cast_eq_zero, zero_mul, add_zero,
    spectralBasis_prime ℓ, c, ℓ]

end PolynomialRigidity.Enumeration
