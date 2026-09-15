import PolynomialRigidity.Enumeration.InverseLogistic
import PolynomialRigidity.Valuation

/-!
# Integral polynomials and reduction at a valuation

This file supplies coefficient-level integrality and a reduction map with
the ordinary ring laws. All uses of reduction retain a proof that the
complex coefficients lie in the specified valuation subring.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

variable {K : Type*} [Field K]

def IntegralCoefficients (V : ValuationSubring K) (F : K[X]) : Prop :=
  ∀ n : ℕ, F.coeff n ∈ V

theorem integralCoefficients_iff_valuation (V : ValuationSubring K) (F : K[X]) :
    IntegralCoefficients V F ↔ ∀ n, V.valuation (F.coeff n) ≤ 1 := by
  simp only [IntegralCoefficients, V.valuation_le_one_iff]

theorem integralCoefficients_iff_lifts (V : ValuationSubring K) (F : K[X]) :
    IntegralCoefficients V F ↔ F ∈ Polynomial.lifts V.subtype := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  constructor
  · intro h n
    exact ⟨⟨F.coeff n, h n⟩, rfl⟩
  · intro h n
    obtain ⟨a, ha⟩ := h n
    rw [← ha]
    exact a.property

namespace IntegralCoefficients

variable {V : ValuationSubring K} {F G : K[X]}

theorem zero : IntegralCoefficients V (0 : K[X]) := by intro n; simp

theorem monomial (n : ℕ) {c : K} (hc : c ∈ V) : IntegralCoefficients V (Polynomial.monomial n c) := by
  intro k
  rw [coeff_monomial]
  split_ifs
  · exact hc
  · exact V.zero_mem

theorem C {c : K} (hc : c ∈ V) : IntegralCoefficients V (Polynomial.C c) := monomial 0 hc

theorem one : IntegralCoefficients V (1 : K[X]) := by simpa only [C_1] using C V.one_mem

theorem X : IntegralCoefficients V (Polynomial.X : K[X]) := monomial 1 V.one_mem

theorem add (hF : IntegralCoefficients V F) (hG : IntegralCoefficients V G) :
    IntegralCoefficients V (F + G) := by
  intro n
  rw [coeff_add]
  exact V.toSubring.add_mem (hF n) (hG n)

theorem neg (hF : IntegralCoefficients V F) : IntegralCoefficients V (-F) := by
  intro n
  rw [coeff_neg]
  exact V.toSubring.neg_mem (hF n)

theorem sub (hF : IntegralCoefficients V F) (hG : IntegralCoefficients V G) :
    IntegralCoefficients V (F - G) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem mul (hF : IntegralCoefficients V F) (hG : IntegralCoefficients V G) :
    IntegralCoefficients V (F * G) := by
  intro n
  rw [coeff_mul]
  exact V.toSubring.sum_mem (fun ij hij => V.toSubring.mul_mem (hF ij.1) (hG ij.2))

theorem pow (hF : IntegralCoefficients V F) (n : ℕ) : IntegralCoefficients V (F ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using (one (V := V))
  | succ n ih => simpa only [pow_succ] using ih.mul hF

theorem sum {α : Type*} (s : Finset α) (F : α → K[X])
    (hF : ∀ i ∈ s, IntegralCoefficients V (F i)) : IntegralCoefficients V (∑ i ∈ s, F i) := by
  intro n
  rw [finsetSum_coeff]
  exact V.toSubring.sum_mem (fun i hi => hF i hi n)

theorem derivative (hF : IntegralCoefficients V F) : IntegralCoefficients V F.derivative := by
  intro n
  rw [coeff_derivative]
  exact V.toSubring.mul_mem (hF (n + 1))
    (by simpa only [Nat.cast_add, Nat.cast_one] using natCast_mem V.toSubring (n + 1))

theorem scaleRoots (hF : IntegralCoefficients V F) {s : K} (hs : s ∈ V) :
    IntegralCoefficients V (F.scaleRoots s) := by
  intro n
  rw [coeff_scaleRoots]
  exact V.toSubring.mul_mem (hF n) (V.toSubring.pow_mem hs _)

theorem logisticDelta (hF : IntegralCoefficients V F) :
    IntegralCoefficients V (Enumeration.logisticDelta F) := by
  exact (X.mul (one.sub X)).mul hF.derivative

theorem logisticBasis (n : ℕ) : IntegralCoefficients V (Enumeration.logisticBasis (R := K) n) := by
  induction n with
  | zero => exact X
  | succ n ih => rw [logisticBasis_succ]; exact ih.logisticDelta

theorem logisticTransform (hF : IntegralCoefficients V F) :
    IntegralCoefficients V (Enumeration.logisticTransform F) := by
  rw [logisticTransform_apply]
  exact sum F.support _ (fun i hi => (C (hF i)).mul (logisticBasis i))

theorem spectralBasis (n : ℕ) : IntegralCoefficients V (Enumeration.spectralBasis (R := K) n) := by
  apply (integralCoefficients_iff_lifts V _).mpr
  apply (Polynomial.mem_lifts _).mpr
  exact ⟨Enumeration.spectralBasis (R := V) n, spectralBasis_map V.subtype n⟩

theorem eval (hF : IntegralCoefficients V F) {x : K} (hx : x ∈ V) : F.eval x ∈ V := by
  rw [eval_eq_sum, Polynomial.sum_def]
  exact V.toSubring.sum_mem (fun n hn => V.toSubring.mul_mem (hF n) (V.toSubring.pow_mem hx n))

end IntegralCoefficients

def integralLift (V : ValuationSubring K) (F : K[X]) (hF : IntegralCoefficients V F) : V[X] :=
  ((Polynomial.mem_lifts F).mp ((integralCoefficients_iff_lifts V F).mp hF)).choose

@[simp]
theorem integralLift_map (V : ValuationSubring K) (F : K[X]) (hF : IntegralCoefficients V F) :
    (integralLift V F hF).map V.subtype = F :=
  ((Polynomial.mem_lifts F).mp ((integralCoefficients_iff_lifts V F).mp hF)).choose_spec

@[simp]
theorem integralLift_coeff (V : ValuationSubring K) (F : K[X]) (hF : IntegralCoefficients V F) (n : ℕ) :
    ((integralLift V F hF).coeff n : K) = F.coeff n := by
  simpa only [coeff_map, ValuationSubring.subtype_apply] using
    congrArg (fun P : K[X] => P.coeff n) (integralLift_map V F hF)

theorem integralLift_unique (V : ValuationSubring K) (F : K[X]) (hF : IntegralCoefficients V F)
    (F₀ : V[X]) (hF₀ : F₀.map V.subtype = F) : integralLift V F hF = F₀ :=
  Polynomial.map_injective V.subtype V.subtype_injective ((integralLift_map V F hF).trans hF₀.symm)

theorem integralLift_monic (V : ValuationSubring K) (F : K[X]) (hF : IntegralCoefficients V F)
    (hmonic : F.Monic) : (integralLift V F hF).Monic :=
  Polynomial.monic_of_injective V.subtype_injective (by simpa only [integralLift_map] using hmonic)

theorem integralLift_natDegree (V : ValuationSubring K) (F : K[X]) (hF : IntegralCoefficients V F) :
    (integralLift V F hF).natDegree = F.natDegree := by
  rw [← natDegree_map_eq_of_injective V.subtype_injective, integralLift_map]

def polynomialReduction (V : ValuationSubring K) (F : K[X]) (hF : IntegralCoefficients V F) :
    (IsLocalRing.ResidueField V)[X] :=
  (integralLift V F hF).map (IsLocalRing.residue V)

theorem polynomialReduction_monic (V : ValuationSubring K) (F : K[X])
    (hF : IntegralCoefficients V F) (hmonic : F.Monic) : (polynomialReduction V F hF).Monic :=
  (integralLift_monic V F hF hmonic).map _

theorem polynomialReduction_natDegree (V : ValuationSubring K) (F : K[X])
    (hF : IntegralCoefficients V F) (hmonic : F.Monic) :
    (polynomialReduction V F hF).natDegree = F.natDegree := by
  rw [polynomialReduction, (integralLift_monic V F hF hmonic).natDegree_map, integralLift_natDegree]

theorem polynomialReduction_eq_zero_iff (V : ValuationSubring K) (F : K[X])
    (hF : IntegralCoefficients V F) :
    polynomialReduction V F hF = 0 ↔ ∀ n, V.valuation (F.coeff n) < 1 := by
  rw [Polynomial.ext_iff]
  simp only [polynomialReduction, coeff_map, coeff_zero,
    IsLocalRing.residue_eq_zero_iff, V.valuation_lt_one_iff, integralLift_coeff]

theorem polynomialReduction_mul (V : ValuationSubring K) (F G : K[X])
    (hF : IntegralCoefficients V F) (hG : IntegralCoefficients V G) :
    polynomialReduction V (F * G) (hF.mul hG) =
      polynomialReduction V F hF * polynomialReduction V G hG := by
  have hl := integralLift_unique V (F * G) (hF.mul hG)
    (integralLift V F hF * integralLift V G hG) (by simp only [Polynomial.map_mul, integralLift_map])
  simp only [polynomialReduction, hl, Polynomial.map_mul]

theorem polynomialReduction_add (V : ValuationSubring K) (F G : K[X])
    (hF : IntegralCoefficients V F) (hG : IntegralCoefficients V G) :
    polynomialReduction V (F + G) (hF.add hG) =
      polynomialReduction V F hF + polynomialReduction V G hG := by
  have hl := integralLift_unique V (F + G) (hF.add hG)
    (integralLift V F hF + integralLift V G hG) (by simp only [Polynomial.map_add, integralLift_map])
  simp only [polynomialReduction, hl, Polynomial.map_add]

theorem polynomialReduction_C (V : ValuationSubring K) (c : K) (hc : c ∈ V) :
    polynomialReduction V (C c) (IntegralCoefficients.C hc) =
      C (IsLocalRing.residue V ⟨c, hc⟩) := by
  have hl := integralLift_unique V (C c) (IntegralCoefficients.C hc) (C ⟨c, hc⟩) (by simp)
  simp only [polynomialReduction, hl, map_C]

theorem polynomialReduction_congr (V : ValuationSubring K) {F G : K[X]} (he : F = G)
    (hF : IntegralCoefficients V F) (hG : IntegralCoefficients V G) :
    polynomialReduction V F hF = polynomialReduction V G hG := by
  subst G
  rfl

theorem polynomialReduction_sub (V : ValuationSubring K) (F G : K[X])
    (hF : IntegralCoefficients V F) (hG : IntegralCoefficients V G) :
    polynomialReduction V (F - G) (hF.sub hG) =
      polynomialReduction V F hF - polynomialReduction V G hG := by
  have hl := integralLift_unique V (F - G) (hF.sub hG)
    (integralLift V F hF - integralLift V G hG) (by simp only [Polynomial.map_sub, integralLift_map])
  simp only [polynomialReduction, hl, Polynomial.map_sub]

theorem polynomialReduction_degree_le (V : ValuationSubring K) (F : K[X])
    (hF : IntegralCoefficients V F) : (polynomialReduction V F hF).degree ≤ F.degree := by
  apply degree_map_le.trans_eq
  rw [← degree_map_eq_of_injective V.subtype_injective, integralLift_map]

theorem polynomialReduction_degree (V : ValuationSubring K) (F : K[X])
    (hF : IntegralCoefficients V F) (hmonic : F.Monic) :
    (polynomialReduction V F hF).degree = F.degree := by
  rw [degree_eq_natDegree (polynomialReduction_monic V F hF hmonic).ne_zero,
    polynomialReduction_natDegree V F hF hmonic, degree_eq_natDegree hmonic.ne_zero]

theorem polynomialReduction_C_mul_eq_zero (V : ValuationSubring K) (c : K) (F : K[X])
    (hc : c ∈ V) (hsmall : V.valuation c < 1) (hF : IntegralCoefficients V F) :
    polynomialReduction V (C c * F) ((IntegralCoefficients.C hc).mul hF) = 0 := by
  apply (polynomialReduction_eq_zero_iff _ _ _).mpr
  intro n
  rw [coeff_C_mul, map_mul]
  have hn : V.valuation (F.coeff n) ≤ 1 := (V.valuation_le_one_iff _).mpr (hF n)
  exact (mul_le_mul_of_nonneg_left hn zero_le).trans_lt (by simpa only [mul_one] using hsmall)

theorem IntegralCoefficients.divByMonic {V : ValuationSubring K} {F A : K[X]}
    (hF : IntegralCoefficients V F) (hA : IntegralCoefficients V A) (hmonic : A.Monic) :
    IntegralCoefficients V (F /ₘ A) := by
  apply (integralCoefficients_iff_lifts V _).mpr
  apply (Polynomial.mem_lifts _).mpr
  refine ⟨integralLift V F hF /ₘ integralLift V A hA, ?_⟩
  rw [map_divByMonic _ (integralLift_monic V A hA hmonic), integralLift_map, integralLift_map]

theorem IntegralCoefficients.of_monic_mul {V : ValuationSubring K} {A Q : K[X]}
    (hAQ : IntegralCoefficients V (A * Q)) (hA : IntegralCoefficients V A) (hmonic : A.Monic) :
    IntegralCoefficients V Q := by
  have h := hAQ.divByMonic hA hmonic
  have hz : (A * Q) %ₘ A = 0 := (modByMonic_eq_zero_iff_dvd hmonic).mpr (dvd_mul_right _ _)
  have he := modByMonic_add_div (A * Q) A
  rw [hz, zero_add] at he
  rw [mul_left_cancel₀ hmonic.ne_zero he] at h
  exact h

theorem polynomialReduction_dvd (V : ValuationSubring K) {A F : K[X]}
    (hA : IntegralCoefficients V A) (hF : IntegralCoefficients V F) (hmonic : A.Monic) (hdiv : A ∣ F) :
    polynomialReduction V A hA ∣ polynomialReduction V F hF := by
  obtain ⟨Q, rfl⟩ := hdiv
  have hQ := hF.of_monic_mul hA hmonic
  exact ⟨polynomialReduction V Q hQ, polynomialReduction_mul V A Q hA hQ⟩

end PolynomialRigidity.Enumeration
