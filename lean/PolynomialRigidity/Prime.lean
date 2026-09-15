import PolynomialRigidity.Convolution
import PolynomialRigidity.Valuation
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Polynomial rigidity when `2 * d + 1` is prime

For a monic polynomial integral at the prime `ℓ = 2 * d + 1`, the term
`ℓ * beta d d` is a unit and every other term of `ℓ * H_A(1)` lies in
the maximal ideal. A root of maximal valuation lets us reduce any
hypothetical nonmonomial solution to this situation.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity

variable {K : Type*} [Field K] [CharZero K]

theorem prime_mul_beta_self (d : ℕ) :
    ((2 * d + 1 : ℕ) : K) * beta (K := K) d d =
      (d.factorial : K) * (d.factorial : K) / ((2 * d).factorial : K) := by
  have hf : ((2 * d).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * d)
  have hp : ((2 * d + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast (by omega : 2 * d + 1 ≠ 0)
  unfold beta
  rw [show d + d + 1 = (2 * d) + 1 by omega, Nat.factorial_succ, Nat.cast_mul]
  field_simp

/-- The unique surviving term of the normalised convolution is a unit. -/
theorem valuation_prime_mul_beta_self (V : ValuationSubring K) {d : ℕ}
    (hp : (2 * d + 1).Prime) (hv : V.valuation ((2 * d + 1 : ℕ) : K) < 1) :
    V.valuation (((2 * d + 1 : ℕ) : K) * beta (K := K) d d) = 1 := by
  rw [prime_mul_beta_self, map_div₀, map_mul,
    valuation_factorial_eq_one V hp hv (by omega : d < 2 * d + 1),
    valuation_factorial_eq_one V hp hv (by omega : 2 * d < 2 * d + 1)]
  simp

omit [CharZero K] in
/-- Every other factorial ratio has unit denominator at the prime. -/
theorem valuation_beta_eq_one (V : ValuationSubring K) {ℓ i j : ℕ}
    (hp : ℓ.Prime) (hv : V.valuation (ℓ : K) < 1) (hij : i + j + 1 < ℓ) :
    V.valuation (beta (K := K) i j) = 1 := by
  simp only [beta, map_div₀, map_mul,
    valuation_factorial_eq_one V hp hv (by omega : i < ℓ),
    valuation_factorial_eq_one V hp hv (by omega : j < ℓ),
    valuation_factorial_eq_one V hp hv hij, mul_one, div_one]

/-- The prime reduction prevents the convolution from vanishing at `1`. -/
theorem eval_convolution_one_ne_zero (V : ValuationSubring K) {A : K[X]} (hA : A.Monic)
    (hp : (2 * A.natDegree + 1).Prime)
    (hv : V.valuation ((2 * A.natDegree + 1 : ℕ) : K) < 1)
    (hc : ∀ i, V.valuation (A.coeff i) ≤ 1) :
    (convolution A).eval 1 ≠ 0 := by
  let d := A.natDegree
  let s := (range (d + 1)).product (range (d + 1))
  let f : ℕ × ℕ → K := fun ij =>
    ((2 * d + 1 : ℕ) : K) * (A.coeff ij.1 * A.coeff ij.2 * beta ij.1 ij.2)
  have htop : V.valuation (f (d, d)) = 1 := by
    simp only [f, hA.coeff_natDegree, one_mul, d]
    exact valuation_prime_mul_beta_self V hp hv
  have hmem : (d, d) ∈ s := by simp [s]
  have hsmall : ∀ ij ∈ s \ {(d, d)}, V.valuation (f ij) < V.valuation (f (d, d)) := by
    intro ij hij
    obtain ⟨hi, hj, hne⟩ : ij.1 ≤ d ∧ ij.2 ≤ d ∧ ij ≠ (d, d) := by
      simpa [s, Finset.mem_sdiff, Finset.mem_product, and_assoc] using hij
    have hsum : ij.1 + ij.2 + 1 < 2 * d + 1 := by
      have : ij.1 ≠ d ∨ ij.2 ≠ d := by
        by_contra h
        push Not at h
        exact hne (Prod.ext h.1 h.2)
      omega
    rw [htop]
    calc
      V.valuation (f ij) = V.valuation ((2 * d + 1 : ℕ) : K) *
          (V.valuation (A.coeff ij.1) * V.valuation (A.coeff ij.2)) := by
        simp only [f, map_mul, valuation_beta_eq_one V hp hv hsum, mul_one]
      _ ≤ V.valuation ((2 * d + 1 : ℕ) : K) * 1 := by
        exact mul_le_mul_of_nonneg_left (mul_le_one₀ (hc ij.1) zero_le (hc ij.2)) zero_le
      _ < 1 := by simpa using hv
  have hval : V.valuation (∑ ij ∈ s, f ij) = 1 :=
    (V.valuation.map_sum_eq_of_lt hmem hsmall).trans htop
  have heval : ((2 * d + 1 : ℕ) : K) * (convolution A).eval 1 = ∑ ij ∈ s, f ij := by
    dsimp only [s, f, d]
    simp only [eval_convolution, one_pow, mul_one, Finset.mul_sum]
    exact (Finset.sum_product (range (d + 1)) (range (d + 1)) f).symm
  intro hz
  rw [← heval, hz, mul_zero, map_zero] at hval
  exact zero_ne_one hval

/-- Prime-index rigidity for any split monic polynomial in characteristic zero. -/
theorem monic_eq_X_pow_of_prime_of_splits {A : K[X]} (hA : A.Monic) (hsplit : A.Splits)
    (hp : (2 * A.natDegree + 1).Prime) (hdiv : A ∣ convolution A) :
    A = X ^ A.natDegree := by
  classical
  obtain ⟨V, hv⟩ := exists_prime_valuation (K := K) hp
  have hroots : ∀ r ∈ A.roots, r = 0 := by
    intro r hr
    by_contra hr0
    have hne : A.roots ≠ 0 := by
      intro hz
      simp [hz] at hr
    obtain ⟨m, hm, hmax⟩ := Multiset.exists_max_image V.valuation hne
    have hm0 : m ≠ 0 := by
      intro hz
      have hle := hmax r hr
      rw [hz, map_zero] at hle
      exact (not_le_of_gt (V.valuation.pos_iff.mpr hr0)) hle
    have hmroot : A.eval m = 0 := (Polynomial.mem_roots hA.ne_zero).mp hm
    have hHm : (convolution A).eval m = 0 := by
      obtain ⟨B, hB⟩ := hdiv
      rw [hB, eval_mul, hmroot, zero_mul]
    have hzero : (convolution (A.scaleRoots m⁻¹)).eval 1 = 0 := by
      simpa only [inv_mul_cancel₀ hm0, hHm, mul_zero] using
        eval_convolution_scaleRoots A m m⁻¹
    have hnonzero := eval_convolution_one_ne_zero V ((A.monic_scaleRoots_iff _).mpr hA)
      (by simpa only [natDegree_scaleRoots] using hp)
      (by simpa only [natDegree_scaleRoots] using hv)
      (valuation_coeff_scaleRoots_le_one V hA hsplit hm0 hmax)
    exact hnonzero hzero
  calc
    A = (A.roots.map (fun r => (X : K[X]) - C r)).prod := hsplit.eq_prod_roots_of_monic hA
    _ = (A.roots.map (fun _ => (X : K[X]))).prod := by
      congr 1
      apply Multiset.map_congr rfl
      intro r hr
      simp only [hroots r hr, C_0, sub_zero]
    _ = X ^ A.natDegree := by simp [← hsplit.natDegree_eq_card_roots]

/-- The monic rigidity theorem over any algebraically closed field of characteristic zero. -/
theorem monic_eq_X_pow_of_prime [IsAlgClosed K] {A : K[X]} (hA : A.Monic)
    (hp : (2 * A.natDegree + 1).Prime) (hdiv : A ∣ convolution A) :
    A = X ^ A.natDegree :=
  monic_eq_X_pow_of_prime_of_splits hA (IsAlgClosed.splits A) hp hdiv

/-- The unnormalised version: the only solutions are scalar monomials. -/
theorem eq_monomial_of_prime [IsAlgClosed K] {A : K[X]} (hA : A ≠ 0)
    (hp : (2 * A.natDegree + 1).Prime) (hdiv : A ∣ convolution A) :
    A = monomial A.natDegree A.leadingCoeff := by
  let c := A.leadingCoeff⁻¹
  have hlc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have hc : c ≠ 0 := inv_ne_zero hlc
  let B := C c * A
  have hB : B.Monic := by
    simpa only [B, c, mul_comm] using monic_mul_leadingCoeff_inv hA
  have hdeg : B.natDegree = A.natDegree := natDegree_C_mul hc
  have hBdiv : B ∣ convolution B := by
    obtain ⟨T, hT⟩ := hdiv
    refine ⟨C c * T, ?_⟩
    change convolution (C c * A) = (C c * A) * (C c * T)
    rw [convolution_C_mul A hc, hT, map_pow]
    ring
  have heq : B = X ^ A.natDegree := by
    simpa only [hdeg] using monic_eq_X_pow_of_prime hB (by rwa [hdeg]) hBdiv
  calc
    A = C A.leadingCoeff * B := by
      dsimp only [B, c]
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, one_mul]
    _ = C A.leadingCoeff * X ^ A.natDegree := by rw [heq]
    _ = monomial A.natDegree A.leadingCoeff := C_mul_X_pow_eq_monomial

/-- The degree-indexed statement `(R_d)` from the manuscript in the prime case. -/
theorem rigidityAtDegree_of_prime [IsAlgClosed K] {d : ℕ} (hp : (2 * d + 1).Prime) :
    RigidityAtDegree K d := by
  intro A hA hdeg hdiv
  simpa only [hdeg] using monic_eq_X_pow_of_prime hA (by rwa [hdeg]) hdiv

/-- The requested `2p - 1` prime case, with `deg A = p - 1`. -/
theorem rigidity_prime_index {p : ℕ} (hp : 2 ≤ p) (hprime : (2 * p - 1).Prime) :
    RigidityAtDegree ℂ (p - 1) := by
  apply rigidityAtDegree_of_prime
  have heq : 2 * (p - 1) + 1 = 2 * p - 1 := by omega
  simpa only [heq] using hprime

/-- The explicit complex-polynomial theorem, without a monic normalisation. -/
theorem polynomial_rigidity_prime_index {p : ℕ} {A : ℂ[X]}
    (hp : 2 ≤ p) (hprime : (2 * p - 1).Prime) (hdegree : A.natDegree = p - 1)
    (hA : A ≠ 0) (hdiv : A ∣ convolution A) :
    A = C A.leadingCoeff * X ^ (p - 1) := by
  have hp' : (2 * A.natDegree + 1).Prime := by
    have heq : 2 * A.natDegree + 1 = 2 * p - 1 := by omega
    simpa only [heq] using hprime
  simpa only [hdegree, C_mul_X_pow_eq_monomial] using eq_monomial_of_prime hA hp' hdiv

end PolynomialRigidity
