import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Transfer of polynomial solutions to the complex numbers

A finite-variable system over a field that has a point in some extension
also has a point in an algebraically closed extension. This will let us use
residue-field lifts without identifying the p-adic and complex fields.
-/

noncomputable section

namespace PolynomialRigidity.Enumeration

open MvPolynomial

theorem exists_common_zero_in_algClosed
    {k K L σ : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [IsAlgClosed L] [Finite σ] (equations : Set (MvPolynomial σ k))
    (a : σ → K) (ha : ∀ f ∈ equations, aeval a f = 0) :
    ∃ b : σ → L, ∀ f ∈ equations, aeval b f = 0 := by
  let I : Ideal (MvPolynomial σ k) := Ideal.span equations
  have hle : I ≤ RingHom.ker (aeval a) := Ideal.span_le.mpr ha
  have hne : I ≠ ⊤ := by
    intro he
    have h := hle (show (1 : MvPolynomial σ k) ∈ I by simp [he])
    have hz : (1 : K) = 0 := by simpa only [RingHom.mem_ker, map_one] using h
    exact one_ne_zero hz
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
  obtain ⟨b, hb⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal L hM
  refine ⟨b, fun f hf => ?_⟩
  have hm := hIM (Ideal.subset_span hf)
  rw [hb] at hm
  exact (MvPolynomial.mem_vanishingIdeal_singleton_iff b f).mp hm

theorem exists_common_zero_in_complex
    {K σ : Type*} [Field K] [CharZero K] [Finite σ]
    (equations : Set (MvPolynomial σ ℚ)) (a : σ → K)
    (ha : ∀ f ∈ equations, aeval a f = 0) :
    ∃ b : σ → ℂ, ∀ f ∈ equations, aeval b f = 0 :=
  exists_common_zero_in_algClosed equations a ha

/-- A finite family of distinct solutions transfers as a distinct family.
Inverse variables record a nonzero coordinate difference for every pair. -/
theorem exists_injective_family_in_complex
    {K ι σ : Type*} [Field K] [CharZero K] [Finite ι] [Finite σ]
    (equations : Set (MvPolynomial σ ℚ)) (a : ι → σ → K)
    (hinj : Function.Injective a) (ha : ∀ i, ∀ f ∈ equations, aeval (a i) f = 0) :
    ∃ b : ι → σ → ℂ, Function.Injective b ∧ ∀ i, ∀ f ∈ equations, aeval (b i) f = 0 := by
  classical
  let Pairs := {ij : ι × ι // ij.1 ≠ ij.2}
  let Vars := (ι × σ) ⊕ Pairs
  have hcoord : ∀ z : Pairs, ∃ s : σ, a z.val.1 s ≠ a z.val.2 s := by
    intro z
    by_contra h
    push Not at h
    exact z.property (hinj (funext h))
  choose c hc using hcoord
  let invEquation : Pairs → MvPolynomial Vars ℚ := fun z =>
    X (Sum.inr z) * (X (Sum.inl (z.val.1, c z)) - X (Sum.inl (z.val.2, c z))) - 1
  let expanded : Set (MvPolynomial Vars ℚ) := {f |
    (∃ i : ι, ∃ g : MvPolynomial σ ℚ, g ∈ equations ∧
      f = rename (fun s => Sum.inl (i, s)) g) ∨ ∃ z : Pairs, f = invEquation z}
  let av : Vars → K := fun x => match x with
    | Sum.inl (i, s) => a i s
    | Sum.inr z => (a z.val.1 (c z) - a z.val.2 (c z))⁻¹
  have hExpanded : ∀ f ∈ expanded, aeval av f = 0 := by
    intro f hf
    rcases hf with ⟨i, g, hg, rfl⟩ | ⟨z, rfl⟩
    · simpa only [aeval_rename, Function.comp_def, av] using ha i g hg
    · simp only [invEquation, map_sub, map_mul, map_one, aeval_X, av]
      rw [inv_mul_cancel₀ (sub_ne_zero.mpr (hc z)), sub_self]
  obtain ⟨bv, hb⟩ := exists_common_zero_in_complex expanded av hExpanded
  let b : ι → σ → ℂ := fun i s => bv (Sum.inl (i, s))
  refine ⟨b, ?_, ?_⟩
  · intro i j hij
    by_contra hne
    let z : Pairs := ⟨(i, j), hne⟩
    have hz := hb (invEquation z) (Or.inr ⟨z, rfl⟩)
    have he : bv (Sum.inl (z.val.1, c z)) = bv (Sum.inl (z.val.2, c z)) := congrFun hij (c z)
    simp only [invEquation, map_sub, map_mul, map_one, aeval_X, he,
      sub_self, mul_zero, zero_sub] at hz
    exact (neg_ne_zero.mpr (one_ne_zero : (1 : ℂ) ≠ 0)) hz
  · intro i f hf
    have hz := hb (rename (fun s => Sum.inl (i, s)) f) (Or.inl ⟨i, f, hf, rfl⟩)
    simpa only [aeval_rename, Function.comp_def, b] using hz

end PolynomialRigidity.Enumeration
