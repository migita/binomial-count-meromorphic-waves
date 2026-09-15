import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Lifting a simple polynomial system over a complete local ring

Adjoining the inverse of the Jacobian determinant gives a standard smooth
presentation. Formal smoothness then lifts its residue-field point through
the adic completion. The augmented Jacobian is triangular with determinant
the square of the original determinant.
-/

noncomputable section

open MvPolynomial

namespace PolynomialRigidity.Enumeration.PolynomialSystem

variable {R σ ι : Type*} [CommRing R]

abbrev EquationAlgebra (f : ι → MvPolynomial σ R) :=
  MvPolynomial σ R ⧸ Ideal.span (Set.range f)

theorem lift_of_formallySmooth [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (f : ι → MvPolynomial σ R)
    [Algebra.FormallySmooth R (EquationAlgebra f)]
    (a₀ : σ → IsLocalRing.ResidueField R) (ha₀ : ∀ i, aeval a₀ (f i) = 0) :
    ∃ a : σ → R, (∀ i, eval a (f i) = 0) ∧ ∀ j, IsLocalRing.residue R (a j) = a₀ j := by
  let I := Ideal.span (Set.range f)
  let φ : EquationAlgebra f →ₐ[R] IsLocalRing.ResidueField R :=
    Ideal.Quotient.liftₐ I (aeval a₀) (by
      change Ideal.span (Set.range f) ≤ RingHom.ker (aeval a₀)
      apply Ideal.span_le.mpr
      rintro g ⟨i, rfl⟩
      exact ha₀ i)
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
    (R := R) (A := EquationAlgebra f) (S := R) (I := IsLocalRing.maximalIdeal R) φ
  let a : σ → R := fun j => g (Ideal.Quotient.mk I (X j))
  have heval : (aeval a : MvPolynomial σ R →ₐ[R] R) = g.comp (Ideal.Quotient.mkₐ R I) := by
    ext j
    simp [a]
  refine ⟨a, ?_, ?_⟩
  · intro i
    change aeval a (f i) = 0
    rw [heval]
    change g (Ideal.Quotient.mk I (f i)) = 0
    have hi : Ideal.Quotient.mk I (f i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    rw [hi, map_zero]
  · intro j
    have hφ : φ (Ideal.Quotient.mk I (X j)) = a₀ j := by
      change aeval a₀ (X j) = a₀ j
      exact aeval_X a₀ j
    have h := congrArg (fun h : EquationAlgebra f →ₐ[R] IsLocalRing.ResidueField R =>
      h (Ideal.Quotient.mk I (X j))) hg
    change IsLocalRing.residue R (g (Ideal.Quotient.mk I (X j))) = φ (Ideal.Quotient.mk I (X j)) at h
    exact h.trans hφ

section SquareSystem

variable [Fintype σ] [DecidableEq σ]

/-- Variables index the rows, as in mathlib's submersive presentations. -/
def jacobianMatrix (f : σ → MvPolynomial σ R) : Matrix σ σ (MvPolynomial σ R) :=
  fun i j => pderiv i (f j)

def jacobianPolynomial (f : σ → MvPolynomial σ R) : MvPolynomial σ R :=
  (jacobianMatrix f).det

def augmentedSystem (f : σ → MvPolynomial σ R) : (σ ⊕ Unit) → MvPolynomial (σ ⊕ Unit) R
  | Sum.inl j => rename Sum.inl (f j)
  | Sum.inr _ => X (Sum.inr ()) * rename Sum.inl (jacobianPolynomial f) - 1

omit [Fintype σ] in
theorem pderiv_extra_rename (u : Unit) (F : MvPolynomial σ R) :
    pderiv (Sum.inr u) (rename (Sum.inl : σ → σ ⊕ Unit) F) = 0 := by
  induction F using MvPolynomial.induction_on with
  | C r => simp
  | add F G hF hG => simp [hF, hG]
  | mul_X F j hF => simp [hF]

theorem augmented_jacobianMatrix (f : σ → MvPolynomial σ R) :
    jacobianMatrix (augmentedSystem f) = Matrix.fromBlocks
      ((rename (Sum.inl : σ → σ ⊕ Unit)).mapMatrix (jacobianMatrix f))
      (fun i (_ : Unit) => X (Sum.inr ()) * rename Sum.inl (pderiv i (jacobianPolynomial f)))
      0 (fun (_ _ : Unit) => rename Sum.inl (jacobianPolynomial f)) := by
  ext i j : 1
  rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;>
    simp [jacobianMatrix, augmentedSystem, Matrix.fromBlocks,
      pderiv_rename Sum.inl_injective, pderiv_extra_rename]

theorem augmented_jacobianPolynomial (f : σ → MvPolynomial σ R) :
    jacobianPolynomial (augmentedSystem f) = (rename Sum.inl (jacobianPolynomial f)) ^ 2 := by
  let ρ := rename (R := R) (Sum.inl : σ → σ ⊕ Unit)
  let B : Matrix σ Unit (MvPolynomial (σ ⊕ Unit) R) :=
    fun i _ => X (Sum.inr ()) * ρ (pderiv i (jacobianPolynomial f))
  let D : Matrix Unit Unit (MvPolynomial (σ ⊕ Unit) R) := fun _ _ => ρ (jacobianPolynomial f)
  have hA : (ρ.mapMatrix (jacobianMatrix f)).det = ρ (jacobianPolynomial f) := (ρ.map_det _).symm
  have hD : D.det = ρ (jacobianPolynomial f) := Matrix.det_unique D
  calc
    jacobianPolynomial (augmentedSystem f) = (Matrix.fromBlocks (ρ.mapMatrix (jacobianMatrix f)) B 0 D).det :=
      congrArg Matrix.det (augmented_jacobianMatrix f)
    _ = (ρ.mapMatrix (jacobianMatrix f)).det * D.det := Matrix.det_fromBlocks_zero₂₁ _ _ _
    _ = _ := by rw [hA, hD, pow_two]

theorem augmented_formallySmooth (f : σ → MvPolynomial σ R) :
    Algebra.FormallySmooth R (EquationAlgebra (augmentedSystem f)) := by
  let I := Ideal.span (Set.range (augmentedSystem f))
  let S := EquationAlgebra (augmentedSystem f)
  let μ : MvPolynomial (σ ⊕ Unit) R →+* S := Ideal.Quotient.mk I
  let P : Algebra.PreSubmersivePresentation R S (σ ⊕ Unit) (σ ⊕ Unit) :=
    Algebra.PreSubmersivePresentation.naive (v := augmentedSystem f) id Function.injective_id
  have hrel : μ (X (Sum.inr ())) * μ (rename Sum.inl (jacobianPolynomial f)) - 1 = 0 := by
    have h : μ (augmentedSystem f (Sum.inr ())) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨Sum.inr (), rfl⟩)
    simpa only [augmentedSystem, map_sub, map_mul, map_one] using h
  have hu : IsUnit (μ (rename Sum.inl (jacobianPolynomial f))) := by
    apply IsUnit.of_mul_eq_one (μ (X (Sum.inr ())))
    rw [mul_comm]
    exact sub_eq_zero.mp hrel
  have hmatrix : P.jacobiMatrix = jacobianMatrix (augmentedSystem f) := by
    ext i j : 1
    rw [P.jacobiMatrix_apply]
    rfl
  have hJac : IsUnit P.jacobian := by
    rw [P.jacobian_eq_jacobiMatrix_det, hmatrix]
    change IsUnit (μ (jacobianPolynomial (augmentedSystem f)))
    rw [augmented_jacobianPolynomial, map_pow]
    exact hu.pow 2
  let PS : Algebra.SubmersivePresentation R S (σ ⊕ Unit) (σ ⊕ Unit) :=
    { P with jacobian_isUnit := hJac }
  let : Algebra.IsStandardSmooth R S := PS.isStandardSmooth
  infer_instance

/-- Multivariable simple-root lifting, stated directly in residue-field coordinates. -/
theorem hensel_simple_system [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (f : σ → MvPolynomial σ R)
    (a₀ : σ → IsLocalRing.ResidueField R) (ha₀ : ∀ i, aeval a₀ (f i) = 0)
    (hJ : aeval a₀ (jacobianPolynomial f) ≠ 0) :
    ∃ a : σ → R, (∀ i, eval a (f i) = 0) ∧ ∀ j, IsLocalRing.residue R (a j) = a₀ j := by
  let : Algebra.FormallySmooth R (EquationAlgebra (augmentedSystem f)) := augmented_formallySmooth f
  let b₀ : (σ ⊕ Unit) → IsLocalRing.ResidueField R := Sum.elim a₀ (fun _ => (aeval a₀ (jacobianPolynomial f))⁻¹)
  have hb₀ : ∀ i, aeval b₀ (augmentedSystem f i) = 0 := by
    intro i
    cases i with
    | inl i => simpa only [augmentedSystem, aeval_rename, Function.comp_def, b₀, Sum.elim_inl] using ha₀ i
    | inr i =>
      simp only [augmentedSystem, map_sub, map_mul, map_one, aeval_X, aeval_rename,
        Function.comp_def, b₀, Sum.elim_inr, Sum.elim_inl]
      rw [inv_mul_cancel₀ hJ, sub_self]
  obtain ⟨b, hb, hres⟩ := lift_of_formallySmooth (augmentedSystem f) b₀ hb₀
  refine ⟨fun j => b (Sum.inl j), ?_, ?_⟩
  · intro i
    simpa only [augmentedSystem, eval_rename, Function.comp_def] using hb (Sum.inl i)
  · intro j
    exact hres (Sum.inl j)

end SquareSystem

end PolynomialRigidity.Enumeration.PolynomialSystem
