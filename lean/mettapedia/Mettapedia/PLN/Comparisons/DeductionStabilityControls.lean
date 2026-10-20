import Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInputStability

/-!
# The denominator margin cannot be dropped

Two explicit three-atom joint laws each satisfy conditional independence. Their
AB, BC and B readouts agree, while their C marginals differ by epsilon. Both
the exact query and the screened deduction answer differ by one. Small input
error alone therefore gives no uniform stability certificate near B = 1.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Comparisons.DeductionStability.Controls

open Mettapedia.PLN.Comparisons.DeductionStability
open Mettapedia.PLN.Bridges.ProbabilityTheory
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.InformationTheory.FiniteRV

private theorem sum_eight (value : Fin (2^3) → ℝ) :
    (∑ world, value world) = value 0 + (value 1 + (value 2 + (value 3 +
      (value 4 + (value 5 + (value 6 + value 7)))))) := by
  change (∑ world : Fin 8, value world) = _
  simp [Fin.sum_univ_succ]

/-- A rare antecedent lies outside the middle event and has a false target. -/
noncomputable def lower (epsilon : ℝ) (unit : epsilon ∈ Set.Icc (0 : ℝ) 1) : JointDistribution 3 where
  prob world := match world.val with | 1 => epsilon | 6 => 1-epsilon | _ => 0
  prob_nonneg world := by split <;> linarith [unit.1, unit.2]
  prob_sum_one := by
    change (∑ world : Fin 8, match world.val with | 1 => epsilon | 6 => 1-epsilon | _ => 0) = 1
    norm_num [Fin.sum_univ_succ]

/-- Move only the rare antecedent mass to a true-target world. -/
noncomputable def upper (epsilon : ℝ) (unit : epsilon ∈ Set.Icc (0 : ℝ) 1) : JointDistribution 3 where
  prob world := match world.val with | 5 => epsilon | 6 => 1-epsilon | _ => 0
  prob_nonneg world := by split <;> linarith [unit.1, unit.2]
  prob_sum_one := by
    change (∑ world : Fin 8, match world.val with | 5 => epsilon | 6 => 1-epsilon | _ => 0) = 1
    norm_num [Fin.sum_univ_succ]

/-- Both source laws satisfy screening off; the instability below comes from
small complementary mass, rather than from dependence error. -/
theorem component_cmi_zero (epsilon : ℝ) (unit : epsilon ∈ Set.Icc (0 : ℝ) 1) :
    condMutualInfo (lower epsilon unit).prob (worldToAssignment 3 · 0)
      (worldToAssignment 3 · 1) (worldToAssignment 3 · 2) = 0 ∧
    condMutualInfo (upper epsilon unit).prob (worldToAssignment 3 · 0)
      (worldToAssignment 3 · 1) (worldToAssignment 3 · 2) = 0 := by
  constructor
  · apply (condMutualInfo_eq_zero_iff _ (lower epsilon unit).prob_nonneg _ _ _).mpr
    rintro ⟨a,b,c⟩
    cases a <;> cases b <;> cases c <;>
      norm_num [law3, law2, pushforward_eq_sum_ite, lower, sum_eight, worldToAssignment]
  · apply (condMutualInfo_eq_zero_iff _ (upper epsilon unit).prob_nonneg _ _ _).mpr
    rintro ⟨a,b,c⟩
    cases a <;> cases b <;> cases c <;>
      norm_num [law3, law2, pushforward_eq_sum_ite, upper, sum_eight, worldToAssignment]

/-- A target-marginal perturbation of epsilon changes the exact conditional
and the screened PLN answer by one. The inverse-margin factor is necessary. -/
theorem small_premise_change_full_conclusion_change (epsilon : ℝ)
    (positive : 0 < epsilon) (small : epsilon < 1) :
    let unit : epsilon ∈ Set.Icc (0 : ℝ) 1 := ⟨positive.le, small.le⟩
    let first := lower epsilon unit
    let second := upper epsilon unit
    (condProb first 1 0, condProb first 2 1, marginalProb first 1) =
      (condProb second 1 0, condProb second 2 1, marginalProb second 1) ∧
    |marginalProb first 2 - marginalProb second 2| = epsilon ∧
    |completeDeduction first 0 1 2 - completeDeduction second 0 1 2| = 1 ∧
    |estimate (FiniteJointInputStability.premises first 0 1 2) -
      estimate (FiniteJointInputStability.premises second 0 1 2)| = 1 := by
  dsimp only
  have epsilonNonzero := positive.ne'
  have complementNonzero : 1-epsilon ≠ 0 := by linarith
  norm_num [completeDeduction, condProb, jointProb2, marginalProb, lower, upper,
    sum_eight, worldToAssignment, estimate, FiniteJointInputStability.premises, plnDeductionStrength,
    epsilonNonzero, complementNonzero, abs_of_nonneg positive.le]

/-- The inverse-margin contribution is attained exactly by these screened
finite worlds; it is not solely an artifact of the triangle inequality. -/
theorem perturbation_budget_attained (epsilon : ℝ) (positive : 0 < epsilon) (small : epsilon < 1) :
    let unit : epsilon ∈ Set.Icc (0 : ℝ) 1 := ⟨positive.le, small.le⟩
    perturbationBudget epsilon (FiniteJointInputStability.premises (lower epsilon unit) 0 1 2)
      (FiniteJointInputStability.premises (upper epsilon unit) 0 1 2) = 1 := by
  dsimp only
  have epsilonNonzero := positive.ne'
  have complementNonzero : 1-epsilon ≠ 0 := by linarith
  norm_num [perturbationBudget, FiniteJointInputStability.premises, condProb, jointProb2,
    marginalProb, lower, upper, sum_eight, worldToAssignment, epsilonNonzero,
    complementNonzero, abs_of_nonneg positive.le]

end Mettapedia.PLN.Comparisons.DeductionStability.Controls
