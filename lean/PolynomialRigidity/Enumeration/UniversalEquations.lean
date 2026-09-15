import PolynomialRigidity.Enumeration.Basic
import PolynomialRigidity.Enumeration.ComplexTransfer

/-!
# Universal matching equations over rational coefficient rings

The rational equations specialise to the fixed complex equations in the
statement. They will also describe the p-adic points obtained by lifting.
-/

noncomputable section

open Polynomial

namespace PolynomialRigidity.Enumeration

def universalMonicOver (R : Type*) [CommRing R] (d : ℕ) : (MvPolynomial (Fin d) R)[X] :=
  monicPolynomial d MvPolynomial.X

theorem universalMonicOver_monic (R : Type*) [CommRing R] (d : ℕ) :
    (universalMonicOver R d).Monic := monicPolynomial_monic _ _

@[simp]
theorem universalMonicOver_natDegree (R : Type*) [CommRing R] [Nontrivial R] (d : ℕ) :
    (universalMonicOver R d).natDegree = d := monicPolynomial_natDegree _ _

theorem universalMonicOver_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (d : ℕ) :
    (universalMonicOver R d).map (MvPolynomial.map f) = universalMonicOver S d := by
  simp only [universalMonicOver, monicPolynomial_map, MvPolynomial.map_X]

theorem universalMonicOver_eval₂ {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (d : ℕ) (a : Fin d → S) :
    (universalMonicOver R d).map (MvPolynomial.eval₂Hom f a) = monicPolynomial d a := by
  simp only [universalMonicOver, monicPolynomial_map, MvPolynomial.eval₂Hom_X']

theorem universalMonicOver_eval {R : Type*} [CommRing R] (d : ℕ) (a : Fin d → R) :
    (universalMonicOver R d).map (MvPolynomial.eval a) = monicPolynomial d a := by
  simp only [universalMonicOver, monicPolynomial_map, MvPolynomial.eval_X]

def universalRemainderOver (R : Type*) [CommRing R] [Algebra ℚ R] (d : ℕ) :
    (MvPolynomial (Fin d) R)[X] :=
  discreteConvolution (universalMonicOver R d) (universalMonicOver R d) %ₘ universalMonicOver R d

def matchingEquationsOver (R : Type*) [CommRing R] [Algebra ℚ R] (d : ℕ) (r : Fin d) :
    MvPolynomial (Fin d) R := (universalRemainderOver R d).coeff r.val

def rationalParameterMap (R : Type*) [CommRing R] [Algebra ℚ R] (d : ℕ) :
    MvPolynomial (Fin d) ℚ →ₐ[ℚ] MvPolynomial (Fin d) R :=
  { MvPolynomial.map (algebraMap ℚ R) with
    commutes' := fun q => by
      change MvPolynomial.map (algebraMap ℚ R) (MvPolynomial.C q) =
        MvPolynomial.C (algebraMap ℚ R q)
      simp only [MvPolynomial.map_C] }

def coefficientEvaluation (R : Type*) [CommRing R] [Algebra ℚ R] {d : ℕ} (a : Fin d → R) :
    MvPolynomial (Fin d) R →ₐ[ℚ] R :=
  { MvPolynomial.eval a with
    commutes' := fun q => by
      change MvPolynomial.eval a (MvPolynomial.C (algebraMap ℚ R q)) = algebraMap ℚ R q
      simp only [MvPolynomial.eval_C] }

theorem coefficientEvaluation_comp (R : Type*) [CommRing R] [Algebra ℚ R]
    {d : ℕ} (a : Fin d → R) :
    (coefficientEvaluation R a).comp (rationalParameterMap R d) = MvPolynomial.aeval a := by
  ext j
  simp [coefficientEvaluation, rationalParameterMap]

theorem eval_rationalParameterMap (R : Type*) [CommRing R] [Algebra ℚ R]
    {d : ℕ} (a : Fin d → R) (F : MvPolynomial (Fin d) ℚ) :
    MvPolynomial.eval a (rationalParameterMap R d F) = MvPolynomial.aeval a F := by
  exact congrArg (fun f : MvPolynomial (Fin d) ℚ →ₐ[ℚ] R => f F) (coefficientEvaluation_comp R a)

theorem universalRemainderOver_rat_map (R : Type*) [CommRing R] [Algebra ℚ R] (d : ℕ) :
    (universalRemainderOver ℚ d).map (rationalParameterMap R d).toRingHom = universalRemainderOver R d := by
  rw [universalRemainderOver, map_modByMonic _ (universalMonicOver_monic ℚ d),
    discreteConvolution_map (rationalParameterMap R d)]
  simp only [rationalParameterMap, universalMonicOver_map, universalRemainderOver]

theorem matchingEquationsOver_rat_map (R : Type*) [CommRing R] [Algebra ℚ R]
    (d : ℕ) (r : Fin d) :
    rationalParameterMap R d (matchingEquationsOver ℚ d r) = matchingEquationsOver R d r := by
  have h := congrArg (fun P : (MvPolynomial (Fin d) R)[X] => P.coeff r.val)
    (universalRemainderOver_rat_map R d)
  change (rationalParameterMap R d).toRingHom ((universalRemainderOver ℚ d).coeff r.val) =
    (universalRemainderOver R d).coeff r.val
  exact (coeff_map _ _).symm.trans h

theorem rational_equation_eval {K : Type*} [CommRing K] [Algebra ℚ K]
    (d : ℕ) (a : Fin d → K) (r : Fin d) :
    MvPolynomial.aeval a (matchingEquationsOver ℚ d r) =
      (discreteConvolution (monicPolynomial d a) (monicPolynomial d a) %ₘ
        monicPolynomial d a).coeff r.val := by
  have hU : (universalMonicOver ℚ d).map (MvPolynomial.aeval a).toRingHom =
      monicPolynomial d a := universalMonicOver_eval₂ (algebraMap ℚ K) d a
  have he : (universalRemainderOver ℚ d).map (MvPolynomial.aeval a).toRingHom =
      discreteConvolution (monicPolynomial d a) (monicPolynomial d a) %ₘ monicPolynomial d a := by
    rw [universalRemainderOver, map_modByMonic _ (universalMonicOver_monic ℚ d),
      discreteConvolution_map (MvPolynomial.aeval a), hU]
  have hc := congrArg (fun P : K[X] => P.coeff r.val) he
  change (MvPolynomial.aeval a).toRingHom ((universalRemainderOver ℚ d).coeff r.val) = _
  exact (coeff_map _ _).symm.trans hc

theorem rational_equation_eval_complex (p : ℕ) (a : Coefficients p) (r : Fin (p - 1)) :
    MvPolynomial.aeval a (matchingEquationsOver ℚ (p - 1) r) =
      MvPolynomial.eval a (remainderEquation p r) := by
  rw [← eval_rationalParameterMap ℂ a, matchingEquationsOver_rat_map]
  rfl

def RationalMatching {K : Type*} [CommRing K] [Algebra ℚ K] (d : ℕ) (a : Fin d → K) : Prop :=
  ∀ r : Fin d, MvPolynomial.aeval a (matchingEquationsOver ℚ d r) = 0

theorem rationalMatching_complex_iff (p : ℕ) (a : Coefficients p) :
    RationalMatching (p - 1) a ↔ IsMatchingSolution p a := by
  simp only [RationalMatching, IsMatchingSolution, rational_equation_eval_complex]

/-- A finite distinct family of p-adic or other characteristic-zero matching vectors
produces the same number of distinct points in the actual complex solution type. -/
theorem matching_family_in_complex {K ι : Type*} [Field K] [CharZero K] [Finite ι]
    (p : ℕ) (a : ι → Fin (p - 1) → K) (hinj : Function.Injective a)
    (ha : ∀ i, RationalMatching (p - 1) (a i)) :
    ∃ b : ι → MatchingSolutions p, Function.Injective b := by
  have hz : ∀ i, ∀ f ∈ Set.range (matchingEquationsOver ℚ (p - 1)), MvPolynomial.aeval (a i) f = 0 := by
    rintro i f ⟨r, rfl⟩
    exact ha i r
  obtain ⟨b, hb, hbeq⟩ := exists_injective_family_in_complex
    (Set.range (matchingEquationsOver ℚ (p - 1))) a hinj hz
  have hbm (i : ι) : IsMatchingSolution p (b i) :=
    (rationalMatching_complex_iff p (b i)).mp (fun r => hbeq i _ ⟨r, rfl⟩)
  refine ⟨fun i => ⟨b i, hbm i⟩, ?_⟩
  intro i j he
  exact hb (congrArg Subtype.val he)

end PolynomialRigidity.Enumeration
