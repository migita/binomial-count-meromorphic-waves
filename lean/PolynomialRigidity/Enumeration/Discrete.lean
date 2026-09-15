import PolynomialRigidity.EnumerationStatement

/-!
# Evaluation of the discrete convolution

The Bernoulli-polynomial definition is proved to equal the original finite
sum over positive integers. This supplies the specification used by the
enumeration and the differential-operator correspondence.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

theorem powerSum_eval (m n : ℕ) (hn : 1 ≤ n) :
    (powerSum m).eval (n : ℚ) = ∑ j ∈ Finset.Ico 1 n, (j : ℚ) ^ m := by
  have hm : (m + 1 : ℚ) ≠ 0 := by positivity
  simp only [powerSum, eval_sub, eval_mul, eval_C, Nat.cast_add, Nat.cast_one]
  rw [← Polynomial.sum_range_pow_eq_bernoulli_sub n m]
  rw [← mul_assoc, inv_mul_cancel₀ hm, one_mul,
    ← Finset.sum_range_add_sum_Ico (fun j => (j : ℚ) ^ m) hn]
  simp [zero_pow_eq]

theorem powerSum_eval₂ {R : Type*} [CommRing R] [Algebra ℚ R]
    (m n : ℕ) (hn : 1 ≤ n) :
    (powerSum m).eval₂ (algebraMap ℚ R) (n : R) =
      ∑ j ∈ Finset.Ico 1 n, (j : R) ^ m := by
  rw [← map_natCast (algebraMap ℚ R) n, eval₂_at_apply, powerSum_eval m n hn]
  simp only [map_sum, map_pow, map_natCast]

theorem discreteMonomial_eval (i j n : ℕ) (hn : 1 ≤ n) :
    (discreteMonomial i j).eval (n : ℚ) =
      ∑ t ∈ Finset.Ico 1 n, (t : ℚ) ^ i * ((n : ℚ) - (t : ℚ)) ^ j := by
  simp only [discreteMonomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  simp_rw [powerSum_eval _ n hn, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  calc
    _ = (t : ℚ) ^ i * (-(t : ℚ) + (n : ℚ)) ^ j := by
      rw [add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [neg_pow, pow_add]
      ring
    _ = _ := by congr 2; ring

theorem discreteMonomial_eval₂ {R : Type*} [CommRing R] [Algebra ℚ R]
    (i j n : ℕ) (hn : 1 ≤ n) :
    (discreteMonomial i j).eval₂ (algebraMap ℚ R) (n : R) =
      ∑ t ∈ Finset.Ico 1 n, (t : R) ^ i * ((n : R) - (t : R)) ^ j := by
  rw [← map_natCast (algebraMap ℚ R) n, eval₂_at_apply, discreteMonomial_eval i j n hn]
  simp only [map_sum, map_mul, map_pow, map_sub, map_natCast]

/-- The polynomial definition equals the finite discrete convolution at every positive integer. -/
theorem discreteConvolution_eval {R : Type*} [CommRing R] [Algebra ℚ R]
    (F G : R[X]) (n : ℕ) (hn : 1 ≤ n) :
    (discreteConvolution F G).eval (n : R) =
      ∑ t ∈ Finset.Ico 1 n, F.eval (t : R) * G.eval ((n : R) - (t : R)) := by
  simp only [discreteConvolution, eval_finsetSum, eval_mul, eval_C, eval_map]
  simp_rw [discreteMonomial_eval₂ _ _ n hn, Finset.mul_sum]
  calc
    _ = ∑ i ∈ F.support, ∑ t ∈ Finset.Ico 1 n, ∑ j ∈ G.support,
        (F.coeff i * G.coeff j) * ((t : R) ^ i * ((n : R) - (t : R)) ^ j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ t ∈ Finset.Ico 1 n, ∑ i ∈ F.support, ∑ j ∈ G.support,
        (F.coeff i * G.coeff j) * ((t : R) ^ i * ((n : R) - (t : R)) ^ j) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [eval_eq_sum, Polynomial.sum_def, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem discreteConvolutionSpecification : DiscreteConvolutionSpecification :=
  fun F G n hn => discreteConvolution_eval F G n hn

@[simp]
theorem discreteConvolution_zero_right {R : Type*} [CommRing R] [Algebra ℚ R] (F : R[X]) :
    discreteConvolution F 0 = 0 := by simp [discreteConvolution]

@[simp]
theorem discreteConvolution_zero_left {R : Type*} [CommRing R] [Algebra ℚ R] (F : R[X]) :
    discreteConvolution 0 F = 0 := by simp [discreteConvolution]

theorem discreteConvolution_monomial_monomial {R : Type*} [CommRing R] [Algebra ℚ R]
    (i j : ℕ) (a b : R) :
    discreteConvolution (monomial i a) (monomial j b) =
      C (a * b) * (discreteMonomial i j).map (algebraMap ℚ R) := by
  change (monomial i a).sum (fun n c => (monomial j b).sum (fun m d =>
    C (c * d) * (discreteMonomial n m).map (algebraMap ℚ R))) = _
  rw [Polynomial.sum_monomial_index a _ (by simp [Polynomial.sum_def]),
    Polynomial.sum_monomial_index b _ (by simp)]

section Identities

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R] [Algebra ℚ R]

omit [Algebra ℚ R] in
theorem polynomial_eq_of_posNat_eval (F G : R[X])
    (h : ∀ n : ℕ, 1 ≤ n → F.eval (n : R) = G.eval (n : R)) : F = G := by
  have hinj : Function.Injective (fun n : ℕ => ((n + 1 : ℕ) : R)) := by
    intro m n hmn
    exact Nat.add_right_cancel (Nat.cast_injective hmn)
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective hinj).mono
  rintro x ⟨n, rfl⟩
  exact h (n + 1) (by omega)

theorem discreteConvolution_add_left (F G H : R[X]) :
    discreteConvolution (F + G) H = discreteConvolution F H + discreteConvolution G H := by
  apply polynomial_eq_of_posNat_eval
  intro n hn
  simp only [discreteConvolution_eval _ _ n hn, eval_add, add_mul, Finset.sum_add_distrib]

theorem discreteConvolution_add_right (F G H : R[X]) :
    discreteConvolution F (G + H) = discreteConvolution F G + discreteConvolution F H := by
  apply polynomial_eq_of_posNat_eval
  intro n hn
  simp only [discreteConvolution_eval _ _ n hn, eval_add, mul_add, Finset.sum_add_distrib]

theorem discreteConvolution_sub_left (F G H : R[X]) :
    discreteConvolution (F - G) H = discreteConvolution F H - discreteConvolution G H := by
  apply polynomial_eq_of_posNat_eval
  intro n hn
  simp only [discreteConvolution_eval _ _ n hn, eval_sub, sub_mul, Finset.sum_sub_distrib]

theorem discreteConvolution_sub_right (F G H : R[X]) :
    discreteConvolution F (G - H) = discreteConvolution F G - discreteConvolution F H := by
  apply polynomial_eq_of_posNat_eval
  intro n hn
  simp only [discreteConvolution_eval _ _ n hn, eval_sub, mul_sub, Finset.sum_sub_distrib]

theorem discreteConvolution_C_mul_right (F G : R[X]) (c : R) :
    discreteConvolution F (C c * G) = C c * discreteConvolution F G := by
  apply polynomial_eq_of_posNat_eval
  intro n hn
  simp only [discreteConvolution_eval _ _ n hn, eval_mul, eval_C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem discreteConvolution_mul_X_balance (F G : R[X]) :
    X * discreteConvolution F G =
      discreteConvolution (X * F) G + discreteConvolution F (X * G) := by
  apply polynomial_eq_of_posNat_eval
  intro n hn
  simp only [eval_mul, eval_X, eval_add, discreteConvolution_eval _ _ n hn]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

omit [IsDomain R] [CharZero R] in
@[simp]
theorem discreteConvolution_eval_one (F G : R[X]) :
    (discreteConvolution F G).eval 1 = 0 := by
  simpa using discreteConvolution_eval F G 1 (by decide)

/-- The discrete primitive of `F` has forward difference `F`. -/
theorem discreteConvolution_one_difference (F : R[X]) :
    (discreteConvolution F 1).comp (X + 1) - discreteConvolution F 1 = F := by
  apply polynomial_eq_of_posNat_eval
  intro n hn
  simp only [eval_sub, eval_comp, eval_add, eval_X, eval_one]
  rw [show (n : R) + 1 = ((n + 1 : ℕ) : R) by simp,
    discreteConvolution_eval _ _ (n + 1) (by omega), discreteConvolution_eval _ _ n hn]
  simp only [eval_one, mul_one, Finset.sum_Ico_succ_top hn, add_sub_cancel_left]

end Identities

end PolynomialRigidity.Enumeration
