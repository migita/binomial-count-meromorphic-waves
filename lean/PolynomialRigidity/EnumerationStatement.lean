import PolynomialRigidity.Convolution
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Statements of rational-exponential enumeration and simplicity

This file only defines the propositions; it proves nothing about them. The
prime-index propositions and every correspondence statement below are proved
in the `Enumeration` directory, see `Enumeration/PrimeEnumeration.lean`. The
unrestricted propositions remain conjectures.

The counted objects are normalised one-pole equation-profile pairs, over `ℂ`,
as the monic operator of order `p` varies. The exponential rate is one, the
pole is at `exp z = -1`, and the value at `exp z = 0` is zero. Reflection is
counted separately. Both the manuscript's remainder equations and a direct
rational-function ODE formulation are given below.
-/

noncomputable section

open Polynomial Finset

namespace PolynomialRigidity.Enumeration

/-! ## The discrete convolution, with both endpoints excluded -/

/-- The polynomial continuing `∑ t = 1, ..., n-1, t^m` for positive integers `n`.
The subtraction for `m = 0` removes the endpoint `t = 0`. -/
def powerSum (m : ℕ) : ℚ[X] :=
  C (((m + 1 : ℕ) : ℚ)⁻¹) *
    (Polynomial.bernoulli (m + 1) - C (_root_.bernoulli (m + 1))) -
    C (if m = 0 then 1 else 0)

/-- The discrete convolution of `X^i` and `X^j`, expanded by the binomial theorem. -/
def discreteMonomial (i j : ℕ) : ℚ[X] :=
  ∑ k ∈ range (j + 1),
    C ((-1 : ℚ) ^ k * (j.choose k : ℚ)) * X ^ (j - k) * powerSum (i + k)

/-- An explicit bilinear polynomial operation, valid also over the parameter ring. -/
def discreteConvolution {R : Type*} [CommRing R] [Algebra ℚ R]
    (F G : R[X]) : R[X] :=
  ∑ i ∈ F.support, ∑ j ∈ G.support,
    C (F.coeff i * G.coeff j) * (discreteMonomial i j).map (algebraMap ℚ R)

/-- The specification of the displayed discrete-convolution formula, proved as
`discreteConvolutionSpecification` in `Enumeration/Discrete.lean`. -/
def DiscreteConvolutionSpecification : Prop :=
  ∀ (F G : ℂ[X]) (n : ℕ), 1 ≤ n →
    (discreteConvolution F G).eval (n : ℂ) =
      ∑ j ∈ Finset.Ico 1 n, F.eval (j : ℂ) * G.eval ((n : ℂ) - (j : ℂ))

/-! ## The manuscript's square system in the coefficients of a monic polynomial -/

abbrev Coefficients (p : ℕ) := Fin (p - 1) → ℂ

abbrev ParameterRing (p : ℕ) := MvPolynomial (Fin (p - 1)) ℂ

/-- Descending coefficients: index `j : Fin d` represents `a_(j+1)`. -/
def monicPolynomial {R : Type*} [CommRing R] (d : ℕ) (a : Fin d → R) : R[X] :=
  X ^ d + ∑ j : Fin d, C (a j) * X ^ (d - (j.val + 1))

def coefficientPolynomial (p : ℕ) (a : Coefficients p) : ℂ[X] :=
  monicPolynomial (p - 1) a

def universalPolynomial (p : ℕ) : (ParameterRing p)[X] :=
  monicPolynomial (p - 1) MvPolynomial.X

/-- The universal remainder of `S_A = A ⋆ A` on division by monic `A`. -/
def universalRemainder (p : ℕ) : (ParameterRing p)[X] :=
  discreteConvolution (universalPolynomial p) (universalPolynomial p) %ₘ
    universalPolynomial p

/-- Rows are coefficients `X^r`, for `0 ≤ r < p-1`. -/
def remainderEquation (p : ℕ) (r : Fin (p - 1)) : ParameterRing p :=
  (universalRemainder p).coeff r.val

def IsMatchingSolution (p : ℕ) (a : Coefficients p) : Prop :=
  ∀ r : Fin (p - 1), MvPolynomial.eval a (remainderEquation p r) = 0

def MatchingSolutions (p : ℕ) :=
  {a : Coefficients p // IsMatchingSolution p a}

/-- The Jacobian of the actual remainder equations, with no change of equations. -/
def matchingJacobian (p : ℕ) (a : Coefficients p) :
    Matrix (Fin (p - 1)) (Fin (p - 1)) ℂ :=
  fun r j => MvPolynomial.eval a (MvPolynomial.pderiv j (remainderEquation p r))

/-- Simplicity is nonsingularity of the coefficient Jacobian. -/
def IsSimpleMatchingSolution (p : ℕ) (a : Coefficients p) : Prop :=
  (matchingJacobian p a).det ≠ 0

def expectedCount (p : ℕ) : ℕ :=
  (2 * p - 1).choose (p - 1)

/-- Finiteness is part of the assertion, not a hypothesis. The count is of distinct points. -/
def CountAndSimplicityAtOrder (p : ℕ) : Prop :=
  Finite (MatchingSolutions p) ∧
  Nat.card (MatchingSolutions p) = expectedCount p ∧
  ∀ a : MatchingSolutions p, IsSimpleMatchingSolution p a.val

/-- The unrestricted conjecture, stated without a proof. -/
def UniversalCountAndSimplicity : Prop :=
  ∀ p : ℕ, 2 ≤ p → CountAndSimplicityAtOrder p

/-- The prime-index theorem from the manuscript, proved as
`primeIndexCountAndSimplicity` in `Enumeration/PrimeEnumeration.lean`. -/
def PrimeIndexCountAndSimplicity : Prop :=
  ∀ p : ℕ, 2 ≤ p → (2 * p - 1).Prime → CountAndSimplicityAtOrder p

/-! ## A direct formulation using rational functions of the exponential -/

abbrev RationalFunction := RatFunc ℂ

/-- Embed polynomials in the exponential variable `t` into `ℂ(t)`. -/
def toRationalFunction (F : ℂ[X]) : RationalFunction :=
  algebraMap ℂ[X] RationalFunction F

/-- `d/dz = t d/dt` for `t = exp z`, using the usual quotient rule on reduced fractions. -/
def exponentialDerivative (v : RationalFunction) : RationalFunction :=
  toRationalFunction X *
    toRationalFunction (v.num.derivative * v.denom - v.num * v.denom.derivative) /
      toRationalFunction v.denom ^ 2

/-- Apply the constant-coefficient differential operator `P(D)` to a rational profile. -/
def applyOperator (P : ℂ[X]) (v : RationalFunction) : RationalFunction :=
  ∑ j ∈ P.support,
    algebraMap ℂ RationalFunction (P.coeff j) * (exponentialDerivative^[j]) v

/-- The exact identity `P(D)v + v²/2 = 0` in the rational function field. -/
def SolvesODE (P : ℂ[X]) (v : RationalFunction) : Prop :=
  applyOperator P v + (1 / 2 : RationalFunction) * v ^ 2 = 0

/-- The reduced denominator specifies the unique pole and its exact order.
The numerator conditions impose finite endpoint values and the selected zero equilibrium. -/
def IsNormalizedProfile (p : ℕ) (v : RationalFunction) : Prop :=
  v.denom = (X + 1) ^ p ∧ v.num.natDegree ≤ p ∧ v.num.eval 0 = 0

def IsNormalizedODEPair (p : ℕ) (s : ℂ[X] × RationalFunction) : Prop :=
  s.1.Monic ∧ s.1.natDegree = p ∧ IsNormalizedProfile p s.2 ∧ SolvesODE s.1 s.2

def NormalizedODEPairs (p : ℕ) :=
  {s : ℂ[X] × RationalFunction // IsNormalizedODEPair p s}

/-- No nonzero infinitesimal deformation of a normalised equation-profile pair.
The perturbation `hP` preserves the monic operator; `hN/(X+1)^p` preserves the
pole location and the chosen endpoint. The equation is the linearised ODE. -/
def IsSimpleODEPair (p : ℕ) (s : ℂ[X] × RationalFunction) : Prop :=
  ∀ (hP hN : ℂ[X]), hP.degree < (p : WithBot ℕ) → hN.natDegree ≤ p → hN.eval 0 = 0 →
    let hV := toRationalFunction hN / toRationalFunction ((X + 1) ^ p)
    applyOperator s.1 hV + applyOperator hP s.2 + s.2 * hV = 0 → hP = 0 ∧ hN = 0

/-- The same intended enumeration stated directly for rational equation-profile pairs. -/
def RationalExponentialCountAndSimplicityAtOrder (p : ℕ) : Prop :=
  Finite (NormalizedODEPairs p) ∧
  Nat.card (NormalizedODEPairs p) = expectedCount p ∧
  ∀ s : NormalizedODEPairs p, IsSimpleODEPair p s.val

def UniversalRationalExponentialCountAndSimplicity : Prop :=
  ∀ p : ℕ, 2 ≤ p → RationalExponentialCountAndSimplicityAtOrder p

def PrimeIndexRationalExponentialCountAndSimplicity : Prop :=
  ∀ p : ℕ, 2 ≤ p → (2 * p - 1).Prime → RationalExponentialCountAndSimplicityAtOrder p

/-! ## Explicit correspondence statements, proved in `Enumeration/Basic.lean`,
`Enumeration/Correspondence.lean` and `Enumeration/SimplicityCorrespondence.lean` -/

def logistic : RationalFunction :=
  toRationalFunction X / toRationalFunction (1 + X)

/-- The amplitude scale for a monic differential operator. -/
def profileScale (p : ℕ) : ℂ :=
  2 / beta (p - 1) (p - 1)

def candidateProfile (p : ℕ) (a : Coefficients p) : RationalFunction :=
  algebraMap ℂ RationalFunction (profileScale p) *
    applyOperator (coefficientPolynomial p a) logistic

/-- `P_A = S_A/(beta_d * A)`, with polynomial monic division. -/
def candidateOperator (p : ℕ) (a : Coefficients p) : ℂ[X] :=
  C ((beta (p - 1) (p - 1) : ℂ)⁻¹) *
    (discreteConvolution (coefficientPolynomial p a) (coefficientPolynomial p a) /ₘ
      coefficientPolynomial p a)

def candidatePair (p : ℕ) (a : Coefficients p) : ℂ[X] × RationalFunction :=
  (candidateOperator p a, candidateProfile p a)

/-- Evaluation of the universal remainder agrees with the divisibility formulation. -/
def MatchingDivisibilityAtOrder (p : ℕ) : Prop :=
  ∀ a : Coefficients p, IsMatchingSolution p a ↔
    coefficientPolynomial p a ∣
      discreteConvolution (coefficientPolynomial p a) (coefficientPolynomial p a)

/-- Each matching point gives an ODE pair, and every normalised ODE pair has
exactly one matching parameter vector. This is not assumed by the count statement. -/
def MatchingCorrespondenceAtOrder (p : ℕ) : Prop :=
  (∀ a : Coefficients p,
    IsMatchingSolution p a ↔ IsNormalizedODEPair p (candidatePair p a)) ∧
  ∀ s : ℂ[X] × RationalFunction, IsNormalizedODEPair p s →
    ∃! a : Coefficients p, IsMatchingSolution p a ∧ candidatePair p a = s

/-- The remainder Jacobian and the direct linearised ODE give the same simplicity condition. -/
def SimplicityCorrespondenceAtOrder (p : ℕ) : Prop :=
  ∀ a : Coefficients p, IsMatchingSolution p a →
    (IsSimpleMatchingSolution p a ↔ IsSimpleODEPair p (candidatePair p a))

end PolynomialRigidity.Enumeration
