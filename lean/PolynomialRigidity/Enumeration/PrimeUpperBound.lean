import PolynomialRigidity.Enumeration.PrimeUniqueness

/-!
# Finiteness and the prime binomial upper bound

The reduction map is defined on every complex matching point and is
injective. Its target is the finite set of monic divisors of `X^ℓ-X`.
Together with the already proved simplicity theorem, only existence of all
labels remains for the requested exact count.
-/

noncomputable section

open Polynomial

namespace PolynomialRigidity.Enumeration

theorem matchingPoint_integral {p : ℕ} (hp : 2 ≤ p) (hprime : (2 * p - 1).Prime)
    (V : ValuationSubring ℂ) (hv : V.valuation ((2 * p - 1 : ℕ) : ℂ) < 1)
    (a : MatchingSolutions p) : IntegralCoefficients V (coefficientPolynomial p a.val) := by
  have he : 2 * (coefficientPolynomial p a.val).natDegree + 1 = 2 * p - 1 := by
    rw [coefficientPolynomial_natDegree]
    omega
  exact monic_matching_integral V (coefficientPolynomial_monic p a.val)
    (by simpa only [he] using hprime) (by simpa only [he] using hv)
    ((matchingDivisibilityAtOrder p a.val).mp a.property)

def matchingPointReduction {p : ℕ} (hp : 2 ≤ p) (hprime : (2 * p - 1).Prime)
    (V : ValuationSubring ℂ) (hv : V.valuation ((2 * p - 1 : ℕ) : ℂ) < 1) :
    MatchingSolutions p →
      MonicDivisorsOfDegree (X ^ (2 * p - 1) - X : (IsLocalRing.ResidueField V)[X]) (p - 1) := by
  intro a
  let hAI := matchingPoint_integral hp hprime V hv a
  refine ⟨polynomialReduction V (coefficientPolynomial p a.val) hAI,
    polynomialReduction_monic V _ hAI (coefficientPolynomial_monic p a.val), ?_, ?_⟩
  · rw [polynomialReduction_natDegree V _ hAI (coefficientPolynomial_monic p a.val),
      coefficientPolynomial_natDegree]
  · have he : 2 * (coefficientPolynomial p a.val).natDegree + 1 = 2 * p - 1 := by
      rw [coefficientPolynomial_natDegree]
      omega
    have h := (reduced_matching_data V (coefficientPolynomial_monic p a.val) hAI
      (by simpa only [he] using hprime) (by simpa only [he] using hv)
      ((matchingDivisibilityAtOrder p a.val).mp a.property)).1
    simpa only [he] using h

theorem matchingPointReduction_injective {p : ℕ} (hp : 2 ≤ p) (hprime : (2 * p - 1).Prime)
    (V : ValuationSubring ℂ) (hv : V.valuation ((2 * p - 1 : ℕ) : ℂ) < 1) :
    Function.Injective (matchingPointReduction hp hprime V hv) := by
  intro a b hab
  have he : 2 * (coefficientPolynomial p a.val).natDegree + 1 = 2 * p - 1 := by
    rw [coefficientPolynomial_natDegree]
    omega
  have hpoly : coefficientPolynomial p a.val = coefficientPolynomial p b.val := integral_matching_reduction_injective V
    (coefficientPolynomial_monic p a.val) (coefficientPolynomial_monic p b.val)
    (matchingPoint_integral hp hprime V hv a) (matchingPoint_integral hp hprime V hv b)
    (by rw [coefficientPolynomial_natDegree, coefficientPolynomial_natDegree])
    (by simpa only [he] using hprime) (by simpa only [he] using hv)
    ((matchingDivisibilityAtOrder p a.val).mp a.property)
    ((matchingDivisibilityAtOrder p b.val).mp b.property)
    (congrArg Subtype.val hab)
  apply Subtype.ext
  exact monicPolynomial_injective (p - 1) hpoly

/-- Finiteness and the upper bound for every prime index, over all complex matching points. -/
theorem prime_index_finite_and_card_le {p : ℕ} (hp : 2 ≤ p) (hprime : (2 * p - 1).Prime) :
    Finite (MatchingSolutions p) ∧ Nat.card (MatchingSolutions p) ≤ expectedCount p := by
  obtain ⟨V, hv⟩ := exists_prime_valuation (K := ℂ) hprime
  let : Fact (2 * p - 1).Prime := ⟨hprime⟩
  let : CharP (IsLocalRing.ResidueField V) (2 * p - 1) := residueField_charP V hprime hv
  let f := matchingPointReduction hp hprime V hv
  have hf := matchingPointReduction_injective hp hprime V hv
  have hlabels := prime_special_fibre_count (K := IsLocalRing.ResidueField V) (2 * p - 1) (p - 1)
  let : Finite (MonicDivisorsOfDegree
      (X ^ (2 * p - 1) - X : (IsLocalRing.ResidueField V)[X]) (p - 1)) := hlabels.1
  have hfinite : Finite (MatchingSolutions p) := Finite.of_injective f hf
  refine ⟨hfinite, ?_⟩
  exact (Nat.card_le_card_of_injective f hf).trans_eq hlabels.2

end PolynomialRigidity.Enumeration
