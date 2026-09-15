import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Tactic

/-!
# Continuous convolution of a polynomial with itself

The integral is defined algebraically by its factorial coefficient formula.
Thus the definition applies to every field of characteristic zero without
choosing a path of integration.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity

variable {K : Type*} [Field K]

/-- The coefficient of the convolution of `X^i` and `X^j`. -/
def beta (i j : ℕ) : K :=
  (i.factorial : K) * (j.factorial : K) / ((i + j + 1).factorial : K)

/-- `H_A(x) = ∫₀ˣ A(t) A(x-t) dt`, expressed by its polynomial coefficients. -/
def convolution (A : K[X]) : K[X] :=
  ∑ i ∈ range (A.natDegree + 1), ∑ j ∈ range (A.natDegree + 1),
    monomial (i + j + 1) (A.coeff i * A.coeff j * beta i j)

theorem eval_convolution (A : K[X]) (x : K) :
    (convolution A).eval x =
      ∑ i ∈ range (A.natDegree + 1), ∑ j ∈ range (A.natDegree + 1),
        A.coeff i * A.coeff j * beta i j * x ^ (i + j + 1) := by
  simp only [convolution, eval_finsetSum, eval_monomial]

/-- Scaling all roots scales the convolution with weight `2 * deg A + 1`. -/
theorem eval_convolution_scaleRoots (A : K[X]) (r s : K) :
    (convolution (A.scaleRoots s)).eval (s * r) =
      s ^ (2 * A.natDegree + 1) * (convolution A).eval r := by
  simp only [eval_convolution, natDegree_scaleRoots, coeff_scaleRoots]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hi' : i ≤ A.natDegree := by simpa using hi
  have hj' : j ≤ A.natDegree := by simpa using hj
  have hp : s ^ (A.natDegree - i) * s ^ (A.natDegree - j) * s ^ (i + j + 1) =
      s ^ (2 * A.natDegree + 1) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [mul_pow]
  calc
    _ = (s ^ (A.natDegree - i) * s ^ (A.natDegree - j) * s ^ (i + j + 1)) *
        (A.coeff i * A.coeff j * beta i j * r ^ (i + j + 1)) := by ring
    _ = _ := by rw [hp]

theorem eval_convolution_C_mul (A : K[X]) {c : K} (hc : c ≠ 0) (x : K) :
    (convolution (C c * A)).eval x = c ^ 2 * (convolution A).eval x := by
  simp only [eval_convolution, natDegree_C_mul hc, coeff_C_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem convolution_C_mul (A : K[X]) {c : K} (hc : c ≠ 0) :
    convolution (C c * A) = C (c ^ 2) * convolution A := by
  simp only [convolution, natDegree_C_mul hc, coeff_C_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [C_mul_monomial]
  congr 1
  ring

/-- The rigidity statement at one degree, without asserting it in every degree. -/
def RigidityAtDegree (K : Type*) [Field K] (d : ℕ) : Prop :=
  ∀ A : K[X], A.Monic → A.natDegree = d → A ∣ convolution A → A = X ^ d

/-- The full polynomial rigidity statement. The prime case is proved in `Prime.lean`;
this definition does not assert a proof in all degrees. -/
def Rigidity (K : Type*) [Field K] : Prop :=
  ∀ A : K[X], A ≠ 0 → A ∣ convolution A → A = monomial A.natDegree A.leadingCoeff

end PolynomialRigidity
