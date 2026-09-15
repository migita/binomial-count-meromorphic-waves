import PolynomialRigidity.Enumeration.OperatorLeading

/-!
# Matching points and normalised rational equation-profile pairs

This proves the correspondence required by the fixed enumeration target.
Both directions use the actual rational-function ODE and the exact reduced
denominator condition from `EnumerationStatement.lean`.
-/

noncomputable section

open Polynomial

namespace PolynomialRigidity.Enumeration

theorem profileScale_image_ne_zero (p : ℕ) :
    algebraMap ℂ RationalFunction (profileScale p) ≠ 0 := by
  simpa only [map_zero] using (algebraMap ℂ RationalFunction).injective.ne (profileScale_ne_zero p)

theorem candidateProfile_injective (p : ℕ) : Function.Injective (candidateProfile p) := by
  intro a b hab
  apply monicPolynomial_injective (p - 1)
  apply applyOperator_logistic_injective
  exact mul_left_cancel₀ (profileScale_image_ne_zero p) hab

theorem candidateProfile_normalized {p : ℕ} (hp : 2 ≤ p) (a : Coefficients p) :
    IsNormalizedProfile p (candidateProfile p a) := by
  let B := C (profileScale p) * logisticTransform (coefficientPolynomial p a)
  have hdegree : B.natDegree = p := by
    dsimp only [B]
    rw [natDegree_C_mul (profileScale_ne_zero p),
      logisticTransform_natDegree (coefficientPolynomial_monic p a).ne_zero,
      coefficientPolynomial_natDegree]
    omega
  have hB : B ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hdegree
    omega
  have hzero : B.coeff 0 = 0 := by simp only [B, coeff_C_mul, logisticTransform_coeff_zero, mul_zero]
  have he : aeval logistic B = candidateProfile p a := by
    simp only [B, map_mul, aeval_C, logisticTransform_aeval, candidateProfile]
  simpa only [he] using normalizedProfile_of_logistic B hdegree hB hzero

theorem candidatePair_normalized {p : ℕ} (hp : 2 ≤ p) (a : Coefficients p)
    (ha : IsMatchingSolution p a) : IsNormalizedODEPair p (candidatePair p a) :=
  ⟨candidateOperator_monic p a, candidateOperator_natDegree hp a,
    candidateProfile_normalized hp a, candidateProfile_solvesODE p a ha⟩

/-- The ODE for a candidate profile forces the spectral polynomial product identity. -/
theorem operator_mul_of_solves_profile (p : ℕ) (a : Coefficients p) (P : ℂ[X])
    (hODE : SolvesODE P (candidateProfile p a)) :
    P * coefficientPolynomial p a =
      C ((beta (p - 1) (p - 1) : ℂ)⁻¹) *
        discreteConvolution (coefficientPolynomial p a) (coefficientPolynomial p a) := by
  apply applyOperator_logistic_injective
  change applyOperator (P * coefficientPolynomial p a) logistic =
    applyOperator (C ((beta (p - 1) (p - 1) : ℂ)⁻¹) *
      discreteConvolution (coefficientPolynomial p a) (coefficientPolynomial p a)) logistic
  conv_rhs => rw [applyOperator_mul, applyOperator_C]
  apply mul_left_cancel₀ (profileScale_image_ne_zero p)
  unfold SolvesODE candidateProfile at hODE
  rw [applyOperator_smul_right, ← applyOperator_mul, mul_pow, applyOperator_square] at hODE
  have hs : algebraMap ℂ RationalFunction (profileScale p) =
      2 * algebraMap ℂ RationalFunction ((beta (p - 1) (p - 1) : ℂ)⁻¹) := by
    simp only [profileScale, div_eq_mul_inv, map_mul, map_ofNat]
  rw [hs] at hODE ⊢
  linear_combination hODE

theorem matching_of_profile_solvesODE (p : ℕ) (a : Coefficients p) (P : ℂ[X])
    (hODE : SolvesODE P (candidateProfile p a)) : IsMatchingSolution p a := by
  apply (matchingDivisibilityAtOrder p a).mpr
  have he := operator_mul_of_solves_profile p a P hODE
  have hprod : C (beta (p - 1) (p - 1) : ℂ) * (P * coefficientPolynomial p a) =
      discreteConvolution (coefficientPolynomial p a) (coefficientPolynomial p a) := by
    rw [he, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (beta_ne_zero _ _), C_1, one_mul]
  refine ⟨C (beta (p - 1) (p - 1) : ℂ) * P, ?_⟩
  rw [← hprod]
  ring

/-- Dominant balance recovers the monic singular-part operator of every normalised solution. -/
theorem normalizedSolution_has_monic_profile {p : ℕ} (hp : 2 ≤ p) (P : ℂ[X])
    (v : RationalFunction) (hP : P.Monic) (hPdeg : P.natDegree = p)
    (hv : IsNormalizedProfile p v) (hODE : SolvesODE P v) :
    ∃ A : ℂ[X], A.Monic ∧ A.natDegree = p - 1 ∧
      v = algebraMap ℂ RationalFunction (profileScale p) * applyOperator A logistic := by
  obtain ⟨B, ⟨hBdeg, hBzero, hBv⟩, _⟩ := normalizedProfile_exists_logistic (by omega) v hv
  have hB : B ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hBdeg
    omega
  have hODEB : SolvesODE P (aeval logistic B) := by simpa only [hBv] using hODE
  have hlead : B.leadingCoeff =
      profileScale p * ((-1 : ℂ) ^ (p - 1) * ((p - 1).factorial : ℂ)) := by
    rw [logistic_ODE_leadingCoeff hP hPdeg hBdeg hB hODEB,
      profileScale_basisScalar (by omega)]
  let A := C ((profileScale p)⁻¹) * inverseLogisticTransform B
  have hs := profileScale_ne_zero p
  have hA : A ≠ 0 := by
    exact mul_ne_zero (by simpa only [map_zero] using Polynomial.C_injective.ne (inv_ne_zero hs))
      (inverseLogisticTransform_ne_zero hBzero hB)
  have hAdeg : A.natDegree = p - 1 := by
    have hi := inverseLogisticTransform_natDegree hBzero hB
    rw [hBdeg] at hi
    dsimp only [A]
    rw [natDegree_C_mul (inv_ne_zero hs)]
    omega
  have hTA : logisticTransform A = C ((profileScale p)⁻¹) * B := by
    dsimp only [A]
    rw [logisticTransform_C_mul, logisticTransform_inverseLogisticTransform B hBzero]
  have hmonic : A.Monic := by
    have ht := congrArg Polynomial.leadingCoeff hTA
    rw [logisticTransform_leadingCoeff hA, hAdeg] at ht
    have hright : (C ((profileScale p)⁻¹) * B).leadingCoeff =
        (-1 : ℂ) ^ (p - 1) * ((p - 1).factorial : ℂ) := by
      rw [leadingCoeff_mul, leadingCoeff_C, hlead, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
    rw [hright] at ht
    change A.leadingCoeff = 1
    apply mul_right_cancel₀ (logisticBasisScalar_ne_zero (K := ℂ) (p - 1))
    simpa only [one_mul] using ht
  refine ⟨A, hmonic, hAdeg, ?_⟩
  symm
  rw [← logisticTransform_aeval A, hTA, map_mul, aeval_C, hBv,
    ← mul_assoc, ← map_mul, mul_inv_cancel₀ hs, map_one, one_mul]

/-- Every pair in the original rational-function target has exactly one matching vector. -/
theorem existsUnique_matching_of_normalizedPair {p : ℕ} (hp : 2 ≤ p)
    (s : ℂ[X] × RationalFunction) (hs : IsNormalizedODEPair p s) :
    ∃! a : Coefficients p, IsMatchingSolution p a ∧ candidatePair p a = s := by
  rcases s with ⟨P, v⟩
  rcases hs with ⟨hP, hPdeg, hv, hODE⟩
  obtain ⟨A, hA, hAdeg, hAv⟩ := normalizedSolution_has_monic_profile hp P v hP hPdeg hv hODE
  let a : Coefficients p := fun j => A.coeff (p - 1 - (j.val + 1))
  have haA : coefficientPolynomial p a = A := monicPolynomial_eq_of_monic A hA hAdeg
  have hap : candidateProfile p a = v := by
    unfold candidateProfile
    rw [haA]
    exact hAv.symm
  have hODEa : SolvesODE P (candidateProfile p a) := by simpa only [hap] using hODE
  have ha := matching_of_profile_solvesODE p a P hODEa
  have hop : candidateOperator p a = P := by
    apply mul_right_cancel₀ (coefficientPolynomial_monic p a).ne_zero
    rw [candidateOperator_mul_coefficient p a ha]
    exact (operator_mul_of_solves_profile p a P hODEa).symm
  refine ⟨a, ⟨ha, Prod.ext hop hap⟩, ?_⟩
  intro b hb
  apply candidateProfile_injective p
  rw [hap]
  exact congrArg Prod.snd hb.2

/-- The full matching correspondence, for every order in the statement. -/
theorem matchingCorrespondenceAtOrder {p : ℕ} (hp : 2 ≤ p) : MatchingCorrespondenceAtOrder p := by
  refine ⟨fun a => ⟨candidatePair_normalized hp a, ?_⟩,
    existsUnique_matching_of_normalizedPair hp⟩
  intro ha
  exact matching_of_profile_solvesODE p a (candidateOperator p a) ha.2.2.2

/-- The explicit equivalence used to transport the final finite count. -/
def matchingODEEquiv {p : ℕ} (hp : 2 ≤ p) : MatchingSolutions p ≃ NormalizedODEPairs p where
  toFun a := ⟨candidatePair p a.val, candidatePair_normalized hp a.val a.property⟩
  invFun s := ⟨(existsUnique_matching_of_normalizedPair hp s.val s.property).choose,
    (existsUnique_matching_of_normalizedPair hp s.val s.property).choose_spec.1.1⟩
  left_inv a := by
    apply Subtype.ext
    apply candidateProfile_injective p
    exact congrArg Prod.snd
      (existsUnique_matching_of_normalizedPair hp (candidatePair p a.val)
        (candidatePair_normalized hp a.val a.property)).choose_spec.1.2
  right_inv s := by
    apply Subtype.ext
    exact (existsUnique_matching_of_normalizedPair hp s.val s.property).choose_spec.1.2

/-- Transfer the two remaining algebraic assertions to the original equation-profile statement. -/
theorem rationalCountAndSimplicity_of_matching {p : ℕ} (hp : 2 ≤ p)
    (hcount : CountAndSimplicityAtOrder p) (hsimple : SimplicityCorrespondenceAtOrder p) :
    RationalExponentialCountAndSimplicityAtOrder p := by
  let e := matchingODEEquiv hp
  let : Finite (MatchingSolutions p) := hcount.1
  refine ⟨Finite.of_equiv (MatchingSolutions p) e, ?_, ?_⟩
  · exact (Nat.card_congr e).symm.trans hcount.2.1
  · intro s
    let a := e.symm s
    have ha := (hsimple a.val a.property).mp (hcount.2.2 a)
    have he : candidatePair p a.val = s.val := congrArg Subtype.val (e.apply_symm_apply s)
    simpa only [he] using ha

end PolynomialRigidity.Enumeration
