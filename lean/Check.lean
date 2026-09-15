import PolynomialRigidity

open Polynomial PolynomialRigidity

-- The smallest admissible order, with an arbitrary complex polynomial.
example (A : ℂ[X]) (hA : A.Monic) (hdegree : A.natDegree = 1)
    (hdiv : A ∣ convolution A) : A = X := by
  simpa using rigidity_prime_index (p := 2) (by norm_num) (by norm_num) A hA hdegree hdiv

-- A larger order exercises the p ↦ p - 1 indexing without enumerating solutions.
example (A : ℂ[X]) (hA : A.Monic) (hdegree : A.natDegree = 50)
    (hdiv : A ∣ convolution A) : A = X ^ 50 := by
  exact rigidity_prime_index (p := 51) (by norm_num) (by norm_num) A hA hdegree hdiv

-- The statement also handles an arbitrary nonzero leading coefficient.
example (A : ℂ[X]) (hA : A ≠ 0) (hdegree : A.natDegree = 2)
    (hdiv : A ∣ convolution A) : A = C A.leadingCoeff * X ^ 2 := by
  exact polynomial_rigidity_prime_index (p := 3) (by norm_num) (by norm_num)
    hdegree hA hdiv

/-- info: 'PolynomialRigidity.rigidity_prime_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PolynomialRigidity.rigidity_prime_index

/-- info: 'PolynomialRigidity.polynomial_rigidity_prime_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PolynomialRigidity.polynomial_rigidity_prime_index

/-- info: 'PolynomialRigidity.eq_monomial_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PolynomialRigidity.eq_monomial_of_prime
