import Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInformation
import Mettapedia.PLN.Comparisons.BalancedScreeningInformationError
import Mettapedia.PLN.Comparisons.ModelErrorBounds

/-!
# Balanced information bounds on finite PLN world models

Both endpoint marginals are retained by the screening projection. The resulting
complementary-mass improvement applies to the actual finite-table query. A
reference/working comparison retains model discrepancy as a separate budget.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointBalancedInformation

open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointDistribution
open Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInformation
open Mettapedia.PLN.Comparisons.BalancedScreeningInformationError
open Mettapedia.PLN.Comparisons.ModelErrorBounds
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation

variable {n : ℕ}

/-- `2 P(A) error² ≤ (1-P(A)) I(A;C|B)` for the actual finite-table PLN formula. -/
theorem query_error_sq_le_balanced_cmi (source : JointDistribution n) (a b c : Fin n)
    (possible : 0 < marginalProb source a) :
    2 * marginalProb source a *
      (completeDeduction source a b c -
        plnDeductionStrength (condProb source b a) (condProb source c b)
          (marginalProb source b) (marginalProb source c)) ^ 2 ≤
      (1 - marginalProb source a) * condMutualInfo source.prob (worldToAssignment n · a)
        (worldToAssignment n · b) (worldToAssignment n · c) := by
  have sourcePossible : 0 < pushforward (probabilityEquiv source).1
      (worldToAssignment n · a) true := by
    change 0 < pushforward source.prob (worldToAssignment n · a) true
    rw [pushforward_true]
    exact possible
  have bound := pln_query_error_sq_le_balanced_cmi (probabilityEquiv source)
    (worldToAssignment n · a) (worldToAssignment n · b) (worldToAssignment n · c) sourcePossible
  simp only [probabilityEquiv, Equiv.coe_fn_mk] at bound
  rw [information_query_readout source c a, information_query_readout source b a,
    information_query_readout source c b, pushforward_true source a,
    pushforward_true source b, pushforward_true source c] at bound
  exact bound

/-- The loss certificate is conditional on a supported source query. No
nonempty-middle-branch or independence premise is required. -/
theorem query_error_le_sqrt_balanced_cmi (source : JointDistribution n) (a b c : Fin n)
    (possible : 0 < marginalProb source a) :
    |completeDeduction source a b c -
        plnDeductionStrength (condProb source b a) (condProb source c b)
          (marginalProb source b) (marginalProb source c)| ≤
      Real.sqrt ((1 - marginalProb source a) * condMutualInfo source.prob (worldToAssignment n · a)
        (worldToAssignment n · b) (worldToAssignment n · c) / (2 * marginalProb source a)) := by
  have sourcePossible : 0 < pushforward (probabilityEquiv source).1
      (worldToAssignment n · a) true := by
    change 0 < pushforward source.prob (worldToAssignment n · a) true
    rw [pushforward_true]
    exact possible
  have bound := pln_query_error_le_sqrt_balanced_cmi (probabilityEquiv source)
    (worldToAssignment n · a) (worldToAssignment n · b) (worldToAssignment n · c) sourcePossible
  simp only [probabilityEquiv, Equiv.coe_fn_mk] at bound
  rw [information_query_readout source c a, information_query_readout source b a,
    information_query_readout source c b, pushforward_true source a,
    pushforward_true source b, pushforward_true source c] at bound
  exact bound

/-- Source-model error and the working model's balanced dependence error are
separate terms. Small CMI in the working model does not bound model mismatch. -/
theorem model_and_balanced_information_error_le (source working : JointDistribution n)
    (a b c : Fin n) (sourcePossible : 0 < marginalProb source a)
    (workingPossible : 0 < marginalProb working a) :
    |completeDeduction source a b c -
      plnDeductionStrength (condProb working b a) (condProb working c b)
        (marginalProb working b) (marginalProb working c)| ≤
      queryModelErrorBound source working a +
        Real.sqrt ((1 - marginalProb working a) * condMutualInfo working.prob
          (worldToAssignment n · a) (worldToAssignment n · b) (worldToAssignment n · c) /
            (2 * marginalProb working a)) := by
  exact (abs_sub_le _ (completeDeduction working a b c) _).trans
    (add_le_add (query_model_error_le source working a c sourcePossible workingPossible)
      (query_error_le_sqrt_balanced_cmi working a b c workingPossible))

end Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointBalancedInformation
