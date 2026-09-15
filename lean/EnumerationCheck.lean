import PolynomialRigidity.Enumeration.Basic
import PolynomialRigidity.Enumeration.Discrete
import PolynomialRigidity.Enumeration.SimplicityCorrespondence
import PolynomialRigidity.Enumeration.PrimeUpperBound
import PolynomialRigidity.Enumeration.MultivariateHensel
import PolynomialRigidity.Enumeration.PrimeEnumeration

open Polynomial PolynomialRigidity.Enumeration

-- These check the discrete endpoint convention, not any enumeration theorem.
example : powerSum 0 = (X - 1 : ℚ[X]) := by
  norm_num [powerSum]

example : discreteMonomial 0 0 = (X - 1 : ℚ[X]) := by
  norm_num [discreteMonomial, powerSum, Finset.sum_range_succ]

-- 1·4 + 2·3 + 3·2 + 4·1 = 20.
example : (discreteMonomial 1 1).eval 5 = 20 := by
  norm_num [discreteMonomial, powerSum, Polynomial.bernoulli, Finset.sum_range_succ,
    eval_finsetSum, eval_monomial]

-- Each declaration below is a proposition, not a proof of that proposition.
#check (UniversalCountAndSimplicity : Prop)
#check (PrimeIndexCountAndSimplicity : Prop)
#check (UniversalRationalExponentialCountAndSimplicity : Prop)
#check (PrimeIndexRationalExponentialCountAndSimplicity : Prop)
#check (DiscreteConvolutionSpecification : Prop)
#check (MatchingDivisibilityAtOrder : ℕ → Prop)
#check (MatchingCorrespondenceAtOrder : ℕ → Prop)
#check (SimplicityCorrespondenceAtOrder : ℕ → Prop)

-- Completed foundations: these declarations have the requested propositions as their types.
#check (discreteConvolutionSpecification : DiscreteConvolutionSpecification)
#check (matchingDivisibilityAtOrder : ∀ p, MatchingDivisibilityAtOrder p)

/--
info: 'PolynomialRigidity.Enumeration.discreteConvolutionSpecification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PolynomialRigidity.Enumeration.discreteConvolutionSpecification

/-- info: 'PolynomialRigidity.Enumeration.matchingDivisibilityAtOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PolynomialRigidity.Enumeration.matchingDivisibilityAtOrder

#check (matchingCorrespondenceAtOrder : ∀ {p}, 2 ≤ p → MatchingCorrespondenceAtOrder p)
#check (simplicityCorrespondenceAtOrder : ∀ {p}, 2 ≤ p → SimplicityCorrespondenceAtOrder p)

/--
info: 'PolynomialRigidity.Enumeration.matchingCorrespondenceAtOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PolynomialRigidity.Enumeration.matchingCorrespondenceAtOrder

/--
info: 'PolynomialRigidity.Enumeration.simplicityCorrespondenceAtOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PolynomialRigidity.Enumeration.simplicityCorrespondenceAtOrder

/-- info: 'PolynomialRigidity.Enumeration.prime_index_all_simple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PolynomialRigidity.Enumeration.prime_index_all_simple

/--
info: 'PolynomialRigidity.Enumeration.prime_index_finite_and_card_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PolynomialRigidity.Enumeration.prime_index_finite_and_card_le

#check PolynomialRigidity.Enumeration.PolynomialSystem.hensel_simple_system

-- The proof types are exactly the fixed prime-index propositions.
#check (primeIndexCountAndSimplicity : PrimeIndexCountAndSimplicity)
#check (primeIndexRationalExponentialCountAndSimplicity :
  PrimeIndexRationalExponentialCountAndSimplicity)

/-- info: 'PolynomialRigidity.Enumeration.primeIndexCountAndSimplicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PolynomialRigidity.Enumeration.primeIndexCountAndSimplicity

/--
info: 'PolynomialRigidity.Enumeration.primeIndexRationalExponentialCountAndSimplicity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PolynomialRigidity.Enumeration.primeIndexRationalExponentialCountAndSimplicity
