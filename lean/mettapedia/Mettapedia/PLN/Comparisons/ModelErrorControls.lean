import Mettapedia.PLN.Comparisons.ModelErrorBounds

/-!
# A screened working model can mispredict the reference model

The reference and working tables retain exactly the same five deduction
readouts. The working table is conditionally independent, but the reference
conditional differs from its PLN estimate by `9/10`. Dependence computed only
inside an assumed model therefore cannot certify that model's adequacy.
-/

namespace Mettapedia.PLN.Comparisons.ModelErrorControls

open scoped BigOperators
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.PLN.Comparisons.ErrorCharacterization
open Mettapedia.PLN.Comparisons.ErrorCharacterization.Controls
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation

private theorem sum_boolean_three (f : Fin (2 ^ 3) → ℝ) :
    (∑ x, f x) = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + f 7)))))) := by
  change (∑ x : Fin 8, f x) = _
  simp [Fin.sum_univ_succ]

noncomputable def independentWorking : JointDistribution 3 where
  prob world := if world.val = 2 then 81/100
    else if world.val = 3 ∨ world.val = 6 then 9/100
    else if world.val = 7 then 1/100 else 0
  prob_nonneg world := by split_ifs <;> norm_num
  prob_sum_one := by
    change (∑ world : Fin 8, if world.val = 2 then (81/100 : ℝ)
      else if world.val = 3 ∨ world.val = 6 then 9/100
      else if world.val = 7 then 1/100 else 0) = 1
    norm_num [Fin.sum_univ_succ]

theorem five_readouts_agree :
    (marginalProb independentWorking 0, marginalProb independentWorking 1,
      marginalProb independentWorking 2, condProb independentWorking 1 0,
      condProb independentWorking 2 1) =
    (marginalProb rareSubsetDistribution 0, marginalProb rareSubsetDistribution 1,
      marginalProb rareSubsetDistribution 2, condProb rareSubsetDistribution 1 0,
      condProb rareSubsetDistribution 2 1) := by
  norm_num [marginalProb, condProb, jointProb2, independentWorking, rareSubsetDistribution,
    sum_boolean_three, worldToAssignment]

theorem working_information_zero :
    condMutualInfo independentWorking.prob (worldToAssignment 3 · 0)
      (worldToAssignment 3 · 1) (worldToAssignment 3 · 2) = 0 := by
  apply (condMutualInfo_eq_zero_iff independentWorking.prob independentWorking.prob_nonneg
    (worldToAssignment 3 · 0) (worldToAssignment 3 · 1) (worldToAssignment 3 · 2)).mpr
  rintro ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;>
    norm_num [law3, law2, pushforward_eq_sum_ite, independentWorking,
      sum_boolean_three, worldToAssignment]

theorem reference_error_despite_screened_working_model :
    |completeDeduction rareSubsetDistribution 0 1 2 -
      plnDeductionStrength (condProb independentWorking 1 0) (condProb independentWorking 2 1)
        (marginalProb independentWorking 1) (marginalProb independentWorking 2)| = (9/10 : ℝ) := by
  norm_num [completeDeduction, condProb, marginalProb, jointProb2, independentWorking,
    rareSubsetDistribution, plnDeductionStrength,
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.complementConditionalFromMarginal,
    sum_boolean_three, worldToAssignment]

end Mettapedia.PLN.Comparisons.ModelErrorControls
