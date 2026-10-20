import Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointDistribution
import Mettapedia.PLN.Comparisons.ScreeningInformationError
import Mettapedia.PLN.Comparisons.ErrorCharacterization

/-!
# Information bounds on the finite PLN joint-table API

The source table is transported without loss to the existing probability
vector interface. Its Boolean queries then instantiate the information-error
theorem. Conditional mutual information remains distinct from a focused
branch-screening predicate and from the error of one particular query.
-/

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInformation

open scoped BigOperators
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointDistribution
open Mettapedia.PLN.Comparisons.ScreeningInformationError
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation

variable {n : ℕ}

theorem pushforward_true (source : JointDistribution n) (i : Fin n) :
    pushforward source.prob (worldToAssignment n · i) true = marginalProb source i := by
  simp only [pushforward_eq_sum_ite, marginalProb]

theorem law2_true_true (source : JointDistribution n) (i j : Fin n) :
    law2 source.prob (worldToAssignment n · i) (worldToAssignment n · j) (true, true) =
      jointProb2 source i j := by
  rw [law2, pushforward_eq_sum_ite]
  unfold jointProb2
  apply Finset.sum_congr rfl
  intro world _
  cases hi : worldToAssignment n world i <;>
    cases hj : worldToAssignment n world j <;> simp

theorem information_query_readout (source : JointDistribution n) (i j : Fin n) :
    law2 source.prob (worldToAssignment n · j) (worldToAssignment n · i) (true, true) /
        pushforward source.prob (worldToAssignment n · j) true = condProb source i j := by
  rw [law2_true_true, pushforward_true, jointProb2_comm source j i, joint_ratio_readout]

/-- `2 P(A) error² ≤ I(A;C|B)` for the actual finite-table PLN formula. -/
theorem query_error_sq_le_cmi (source : JointDistribution n) (a b c : Fin n)
    (possible : 0 < marginalProb source a) :
    2 * marginalProb source a *
      (completeDeduction source a b c -
        plnDeductionStrength (condProb source b a) (condProb source c b)
          (marginalProb source b) (marginalProb source c)) ^ 2 ≤
      condMutualInfo source.prob (worldToAssignment n · a)
        (worldToAssignment n · b) (worldToAssignment n · c) := by
  have sourcePossible : 0 < pushforward (probabilityEquiv source).1
      (worldToAssignment n · a) true := by
    change 0 < pushforward source.prob (worldToAssignment n · a) true
    rw [pushforward_true]
    exact possible
  have bound := pln_query_error_sq_le_cmi (probabilityEquiv source)
    (worldToAssignment n · a) (worldToAssignment n · b) (worldToAssignment n · c) sourcePossible
  simp only [probabilityEquiv, Equiv.coe_fn_mk] at bound
  rw [information_query_readout source c a, information_query_readout source b a,
    information_query_readout source c b, pushforward_true source a,
    pushforward_true source b, pushforward_true source c] at bound
  exact bound

/-- The loss certificate is conditional on a supported source query. No
nonempty-middle-branch or independence premise is required. -/
theorem query_error_le_sqrt_cmi (source : JointDistribution n) (a b c : Fin n)
    (possible : 0 < marginalProb source a) :
    |completeDeduction source a b c -
        plnDeductionStrength (condProb source b a) (condProb source c b)
          (marginalProb source b) (marginalProb source c)| ≤
      Real.sqrt (condMutualInfo source.prob (worldToAssignment n · a)
        (worldToAssignment n · b) (worldToAssignment n · c) / (2 * marginalProb source a)) := by
  have sourcePossible : 0 < pushforward (probabilityEquiv source).1
      (worldToAssignment n · a) true := by
    change 0 < pushforward source.prob (worldToAssignment n · a) true
    rw [pushforward_true]
    exact possible
  have bound := pln_query_error_le_sqrt_cmi (probabilityEquiv source)
    (worldToAssignment n · a) (worldToAssignment n · b) (worldToAssignment n · c) sourcePossible
  simp only [probabilityEquiv, Equiv.coe_fn_mk] at bound
  rw [information_query_readout source c a, information_query_readout source b a,
    information_query_readout source c b, pushforward_true source a,
    pushforward_true source b, pushforward_true source c] at bound
  exact bound

theorem zero_cmi_implies_query_exact (source : JointDistribution n) (a b c : Fin n)
    (possible : 0 < marginalProb source a)
    (zero : condMutualInfo source.prob (worldToAssignment n · a)
      (worldToAssignment n · b) (worldToAssignment n · c) = 0) :
    completeDeduction source a b c =
      plnDeductionStrength (condProb source b a) (condProb source c b)
        (marginalProb source b) (marginalProb source c) := by
  have bound := query_error_le_sqrt_cmi source a b c possible
  rw [zero, zero_div, Real.sqrt_zero] at bound
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm bound (abs_nonneg _)))

namespace Controls

open Mettapedia.PLN.Comparisons.ErrorCharacterization
open Mettapedia.PLN.Comparisons.ErrorCharacterization.Controls

private theorem sum_boolean_three (f : Fin (2 ^ 3) → ℝ) :
    (∑ x, f x) = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + f 7)))))) := by
  change (∑ x : Fin 8, f x) = _
  simp [Fin.sum_univ_succ]

/-- The parity example is genuinely dependent even though its selected
conditional query is predicted exactly. CMI is not that query's error. -/
theorem cancelling_query_has_positive_cmi :
    completeDeduction cancellingDistribution 0 1 2 =
        screeningDeduction cancellingDistribution 0 1 2 ∧
      0 < condMutualInfo cancellingDistribution.prob (worldToAssignment 3 · 0)
        (worldToAssignment 3 · 1) (worldToAssignment 3 · 2) := by
  refine ⟨exact_query_need_not_have_branch_screening.1, ?_⟩
  have nonnegative := condMutualInfo_nonneg cancellingDistribution.prob
    cancellingDistribution.prob_nonneg (worldToAssignment 3 · 0)
    (worldToAssignment 3 · 1) (worldToAssignment 3 · 2)
  apply lt_of_le_of_ne nonnegative
  intro zero
  have independent := (condMutualInfo_eq_zero_iff cancellingDistribution.prob
    cancellingDistribution.prob_nonneg (worldToAssignment 3 · 0)
    (worldToAssignment 3 · 1) (worldToAssignment 3 · 2)).mp zero.symm
  have atom := independent (true, true, true)
  norm_num [CondIndep, law3, law2, pushforward_eq_sum_ite, cancellingDistribution,
    sum_boolean_three, worldToAssignment] at atom

end Controls

end Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInformation
