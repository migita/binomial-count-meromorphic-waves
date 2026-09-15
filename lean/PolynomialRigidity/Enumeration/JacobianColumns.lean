import PolynomialRigidity.Enumeration.CoefficientDerivation

/-!
# The actual remainder Jacobian as a polynomial tangent map

Each column is the remainder of `2(A ⋆ h) - C_A h` for the corresponding
coefficient monomial. The derivation is applied to the universal monic
division identity before specialisation.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

def parameterEvaluation (p : ℕ) (a : Coefficients p) : ParameterRing p →ₐ[ℚ] ℂ :=
  { MvPolynomial.eval a with commutes' := fun r => by simp }

def universalQuotient (p : ℕ) : (ParameterRing p)[X] :=
  discreteConvolution (universalPolynomial p) (universalPolynomial p) /ₘ universalPolynomial p

def matchingQuotient (p : ℕ) (a : Coefficients p) : ℂ[X] :=
  discreteConvolution (coefficientPolynomial p a) (coefficientPolynomial p a) /ₘ
    coefficientPolynomial p a

theorem discreteConvolution_map_eval (p : ℕ) (a : Coefficients p) (F G : (ParameterRing p)[X]) :
    (discreteConvolution F G).map (MvPolynomial.eval a) =
      discreteConvolution (F.map (MvPolynomial.eval a)) (G.map (MvPolynomial.eval a)) :=
  discreteConvolution_map (parameterEvaluation p a) F G

theorem universalConvolution_map_eval (p : ℕ) (a : Coefficients p) :
    (discreteConvolution (universalPolynomial p) (universalPolynomial p)).map
      (MvPolynomial.eval a) =
      discreteConvolution (coefficientPolynomial p a) (coefficientPolynomial p a) := by
  have h := discreteConvolution_map (parameterEvaluation p a)
    (universalPolynomial p) (universalPolynomial p)
  simpa only [parameterEvaluation, universalPolynomial_map_eval] using h

theorem universalQuotient_map_eval (p : ℕ) (a : Coefficients p) :
    (universalQuotient p).map (MvPolynomial.eval a) = matchingQuotient p a := by
  rw [universalQuotient, map_divByMonic _ (universalPolynomial_monic p),
    universalConvolution_map_eval, universalPolynomial_map_eval]
  rfl

theorem remainder_derivative_degree_lt (p : ℕ) (a : Coefficients p) (j : Fin (p - 1)) :
    ((coefficientDerivation (parameterDerivation p j) (universalRemainder p)).map
      (MvPolynomial.eval a)).degree < (coefficientPolynomial p a).degree := by
  apply degree_map_le.trans_lt
  apply (coefficientDerivation_degree_le _ _).trans_lt
  rw [coefficientPolynomial_degree]
  have h := degree_modByMonic_lt
    (discreteConvolution (universalPolynomial p) (universalPolynomial p))
    (universalPolynomial_monic p)
  simpa only [universalRemainder, universalPolynomial, monicPolynomial_degree] using h

theorem matchingJacobian_column (p : ℕ) (a : Coefficients p) (r j : Fin (p - 1)) :
    matchingJacobian p a r j =
      ((2 * discreteConvolution (coefficientPolynomial p a) (X ^ (p - 1 - (j.val + 1))) -
        matchingQuotient p a * X ^ (p - 1 - (j.val + 1))) %ₘ coefficientPolynomial p a).coeff r.val := by
  let D := coefficientDerivation (parameterDerivation p j)
  let e : ℂ[X] := X ^ (p - 1 - (j.val + 1))
  let A := coefficientPolynomial p a
  let Q := matchingQuotient p a
  let Z := (D (universalQuotient p)).map (MvPolynomial.eval a)
  let H := (D (universalRemainder p)).map (MvPolynomial.eval a)
  have h := congrArg (fun F : (ParameterRing p)[X] => (D F).map (MvPolynomial.eval a))
    (modByMonic_add_div (discreteConvolution (universalPolynomial p) (universalPolynomial p))
      (universalPolynomial p))
  change (D (universalRemainder p + universalPolynomial p * universalQuotient p)).map
      (MvPolynomial.eval a) =
    (D (discreteConvolution (universalPolynomial p) (universalPolynomial p))).map
      (MvPolynomial.eval a) at h
  simp only [D, map_add, Derivation.leibniz, smul_eq_mul,
    coefficientDerivation_universalPolynomial, coefficientDerivation_discreteConvolution,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X,
    universalPolynomial_map_eval, universalQuotient_map_eval,
    discreteConvolution_map_eval p a] at h
  change H + (A * Z + Q * e) = discreteConvolution e A + discreteConvolution A e at h
  rw [discreteConvolution_comm e A] at h
  have he : 2 * discreteConvolution A e - Q * e = A * Z + H := by
    linear_combination -h
  have hmul : (A * Z) %ₘ A = 0 :=
    (modByMonic_eq_zero_iff_dvd (coefficientPolynomial_monic p a)).mpr (dvd_mul_right _ _)
  have hH : H %ₘ A = H :=
    (modByMonic_eq_self_iff (coefficientPolynomial_monic p a)).mpr
      (remainder_derivative_degree_lt p a j)
  have hrem : (2 * discreteConvolution A e - Q * e) %ₘ A = H := by
    rw [he, add_modByMonic, hmul, zero_add, hH]
  change matchingJacobian p a r j = ((2 * discreteConvolution A e - Q * e) %ₘ A).coeff r.val
  rw [hrem]
  exact (coefficientDerivation_remainder_eval_coeff p a r j).symm

end PolynomialRigidity.Enumeration
