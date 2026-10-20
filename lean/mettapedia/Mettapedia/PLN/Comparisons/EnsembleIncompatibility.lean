import Mettapedia.PLN.Comparisons.EnsembleAveraging

/-!
# Pooled conditional answers need not have a joint realization

Two explicit finite joint laws each screen off the endpoints through the middle
atom. Their averaged middle marginal, conditional and target marginal violate
an inequality satisfied by every joint probability law. Feeding the averaged
premises into raw PLN deduction gives a negative number, while both component
answers are zero.

This is a finite-table control. It does not identify a native CPT witness.
Per-query model votes and population probabilities therefore require distinct
interpretations; conditional-independence facts inside the components do not
supply the missing bridge.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Comparisons.EnsembleIncompatibility

open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
open Mettapedia.InformationTheory.FiniteRV

/-- A coherence condition on every actual joint probability law. -/
theorem conditional_readout_compatible {n : ℕ} (joint : JointDistribution n) (b c : Fin n) :
    marginalProb joint b * condProb joint c b ≤ marginalProb joint c := by
  rw [marginal_mul_condProb]
  exact event_mass_mono joint _ _ (fun _ both => both.2)

private theorem sum_eight (value : Fin (2^3) → ℝ) :
    (∑ world, value world) = value 0 + (value 1 + (value 2 + (value 3 +
      (value 4 + (value 5 + (value 6 + value 7)))))) := by
  change (∑ world : Fin 8, value world) = _
  simp [Fin.sum_univ_succ]

noncomputable def first : JointDistribution 3 where
  prob world := match world.val with | 1 => 1/10 | 2 => 9/10 | _ => 0
  prob_nonneg world := by split <;> norm_num
  prob_sum_one := by norm_num [sum_eight]

noncomputable def second : JointDistribution 3 where
  prob world := match world.val with | 1 => 9/10 | 6 => 1/10 | _ => 0
  prob_nonneg world := by split <;> norm_num
  prob_sum_one := by norm_num [sum_eight]

theorem pooled_readouts :
    ((marginalProb first 1 + marginalProb second 1)/2,
      (condProb first 2 1 + condProb second 2 1)/2,
      (marginalProb first 2 + marginalProb second 2)/2) =
        ((1/2 : ℝ), (1/2 : ℝ), (1/20 : ℝ)) := by
  norm_num [marginalProb, condProb, jointProb2, first, second, sum_eight, worldToAssignment]

theorem no_joint_realizes_pooled_readouts :
    ¬ ∃ joint : JointDistribution 3,
      marginalProb joint 1 = 1/2 ∧ condProb joint 2 1 = 1/2 ∧ marginalProb joint 2 = 1/20 := by
  rintro ⟨joint, middle, conditional, target⟩
  have compatible := conditional_readout_compatible joint 1 2
  rw [middle, conditional, target] at compatible
  norm_num at compatible

theorem components_screen_off :
    condMutualInfo first.prob (worldToAssignment 3 · 0)
      (worldToAssignment 3 · 1) (worldToAssignment 3 · 2) = 0 ∧
    condMutualInfo second.prob (worldToAssignment 3 · 0)
      (worldToAssignment 3 · 1) (worldToAssignment 3 · 2) = 0 := by
  constructor
  · apply (condMutualInfo_eq_zero_iff _ first.prob_nonneg _ _ _).mpr
    rintro ⟨a,b,c⟩
    cases a <;> cases b <;> cases c <;>
      norm_num [law3, law2, pushforward_eq_sum_ite, first, sum_eight, worldToAssignment]
  · apply (condMutualInfo_eq_zero_iff _ second.prob_nonneg _ _ _).mpr
    rintro ⟨a,b,c⟩
    cases a <;> cases b <;> cases c <;>
      norm_num [law3, law2, pushforward_eq_sum_ite, second, sum_eight, worldToAssignment]

theorem pooled_pln_is_negative :
    completeDeduction first 0 1 2 = 0 ∧ completeDeduction second 0 1 2 = 0 ∧
      plnDeductionStrength ((condProb first 1 0 + condProb second 1 0)/2)
        ((condProb first 2 1 + condProb second 2 1)/2)
        ((marginalProb first 1 + marginalProb second 1)/2)
        ((marginalProb first 2 + marginalProb second 2)/2) = -(2/5 : ℝ) := by
  norm_num [completeDeduction, marginalProb, condProb, jointProb2, plnDeductionStrength,
    first, second, sum_eight, worldToAssignment]

end Mettapedia.PLN.Comparisons.EnsembleIncompatibility
