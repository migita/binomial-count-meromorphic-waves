import PolynomialRigidity.Enumeration.PrimeLowerBound
import PolynomialRigidity.Enumeration.SimplicityCorrespondence

/-!
# Prime-index enumeration and simplicity

These are proofs of the two original propositions in `EnumerationStatement`.
The upper and lower bounds count all complex matching points. The proved
matching and simplicity correspondences give the direct rational-function
equation-profile count, with its original infinitesimal simplicity condition.
-/

noncomputable section

namespace PolynomialRigidity.Enumeration

/-- Exact count and Jacobian simplicity for every prime index. -/
theorem primeIndexCountAndSimplicity : PrimeIndexCountAndSimplicity := by
  intro p hp hprime
  obtain ⟨hfinite, hupper⟩ := prime_index_finite_and_card_le hp hprime
  exact ⟨hfinite, Nat.le_antisymm hupper (prime_index_card_ge hp hprime),
    prime_index_all_simple hp hprime⟩

/-- The requested count and simplicity theorem for the direct rational-exponential ODE pairs. -/
theorem primeIndexRationalExponentialCountAndSimplicity :
    PrimeIndexRationalExponentialCountAndSimplicity := by
  intro p hp hprime
  exact rationalCountAndSimplicity_of_matching hp
    (primeIndexCountAndSimplicity p hp hprime) (simplicityCorrespondenceAtOrder hp)

end PolynomialRigidity.Enumeration
