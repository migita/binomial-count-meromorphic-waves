import PolynomialRigidity.Enumeration.PrimeTransversality

/-!
# Injectivity of prime reduction

The difference of two monic matching polynomials has lower degree. After
normalising this difference, monic division makes its cofactor variation
integral. Coprimality in the common residue class forces a contradiction.
-/

noncomputable section

open Polynomial

namespace PolynomialRigidity.Enumeration

theorem integral_matching_reduction_injective {K : Type*} [Field K] [CharZero K]
    (V : ValuationSubring K) {A B : K[X]} (hA : A.Monic) (hB : B.Monic)
    (hAI : IntegralCoefficients V A) (hBI : IntegralCoefficients V B)
    (hdegree : A.natDegree = B.natDegree) (hℓ : (2 * A.natDegree + 1).Prime)
    (hv : V.valuation ((2 * A.natDegree + 1 : ℕ) : K) < 1)
    (hdivA : A ∣ discreteConvolution A A) (hdivB : B ∣ discreteConvolution B B)
    (hred : polynomialReduction V A hAI = polynomialReduction V B hBI) : A = B := by
  by_contra hne
  have hF0 : A - B ≠ 0 := sub_ne_zero.mpr hne
  have hd : A.degree = B.degree := by
    rw [degree_eq_natDegree hA.ne_zero, degree_eq_natDegree hB.ne_zero, hdegree]
  have hFdegree : (A - B).degree < A.degree :=
    degree_sub_lt_left hd hA.ne_zero (by rw [hA.leadingCoeff, hB.leadingCoeff])
  obtain ⟨c, hc, hHI, hHred, hHdegree⟩ := exists_integral_normalization V (A - B) hF0
  let H := C c * (A - B)
  let ℓ := 2 * A.natDegree + 1
  let CA := normalizedMatchingQuotient A
  let CB := normalizedMatchingQuotient B
  have hH0 : H ≠ 0 :=
    mul_ne_zero (by simpa only [map_zero] using Polynomial.C_injective.ne hc) hF0
  have hHdeg : H.degree < A.degree := hHdegree.trans_lt hFdegree
  have hHnat : H.natDegree < A.natDegree := natDegree_lt_natDegree hH0 hHdeg
  have hSI₁ := discreteConvolution_integral_of_degree_lt V hℓ hv (F := H) (G := A) hHI hAI (by omega)
  have hSI₂ := discreteConvolution_integral_of_degree_lt V hℓ hv (F := B) (G := H) hBI hHI (by omega)
  have hSI := hSI₁.add hSI₂
  have hCAI := normalizedMatchingQuotient_integral V hA hAI hℓ hv hdivA
  let U := C (ℓ : K) * (discreteConvolution H A + discreteConvolution B H) - H * CA
  have hUI : IntegralCoefficients V U :=
    ((IntegralCoefficients.C (natCast_mem V ℓ)).mul hSI).sub (hHI.mul hCAI)
  have hdiff : discreteConvolution A A - discreteConvolution B B =
      discreteConvolution (A - B) A + discreteConvolution B (A - B) := by
    rw [discreteConvolution_sub_left, discreteConvolution_sub_right]
    ring
  have hscaled : discreteConvolution H A + discreteConvolution B H =
      C c * (discreteConvolution A A - discreteConvolution B B) := by
    dsimp only [H]
    rw [discreteConvolution_C_mul_left, discreteConvolution_C_mul_right, hdiff]
    ring
  have hnormA : A * CA = C (ℓ : K) * discreteConvolution A A :=
    normalizedMatchingQuotient_mul hA hdivA
  have hnormB : B * CB = C (ℓ : K) * discreteConvolution B B := by
    have h := normalizedMatchingQuotient_mul hB hdivB
    rw [← hdegree] at h
    exact h
  have hnormDiff : C (ℓ : K) * (discreteConvolution A A - discreteConvolution B B) =
      A * CA - B * CB := by rw [mul_sub, ← hnormA, ← hnormB]
  have hdivU : B ∣ U := by
    refine ⟨C c * (CA - CB), ?_⟩
    change C (ℓ : K) * (discreteConvolution H A + discreteConvolution B H) - H * CA = _
    rw [hscaled]
    calc
      _ = C c * (C (ℓ : K) * (discreteConvolution A A - discreteConvolution B B) - (A - B) * CA) := by
        dsimp only [H]
        ring
      _ = _ := by rw [hnormDiff]; ring
  let Abar := polynomialReduction V A hAI
  let Hbar := polynomialReduction V H hHI
  let Cbar := polynomialReduction V CA hCAI
  have hUred : polynomialReduction V U hUI = -(Hbar * Cbar) := by
    rw [polynomialReduction_sub V _ _ ((IntegralCoefficients.C (natCast_mem V ℓ)).mul hSI)
      (hHI.mul hCAI), polynomialReduction_C_mul_eq_zero V (ℓ : K) _ (natCast_mem V ℓ) hv hSI,
      polynomialReduction_mul V _ _ hHI hCAI, zero_sub]
  have hredDiv := polynomialReduction_dvd V hBI hUI hB hdivU
  rw [hUred, dvd_neg, ← hred] at hredDiv
  have hcop : IsCoprime Abar Cbar := (reduced_matching_data V hA hAI hℓ hv hdivA).2
  have hAH : Abar ∣ Hbar := hcop.dvd_of_dvd_mul_right hredDiv
  have hdegBar : Hbar.degree < Abar.degree := by
    rw [polynomialReduction_degree V A hAI hA]
    exact (polynomialReduction_degree_le V H hHI).trans_lt hHdeg
  exact hHred (eq_zero_of_dvd_of_degree_lt hAH hdegBar)

end PolynomialRigidity.Enumeration
