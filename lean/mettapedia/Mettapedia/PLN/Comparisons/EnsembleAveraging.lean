import Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointBalancedInformation

/-!
# Pooling, conditioning and nonlinear deduction

Exact two-model identities separate the covariance contribution of nonlinear
PLN deduction from the carrier-weighting contribution of conditioning a joint
mixture. The finite-table control has zero conditional mutual information in
each component but a half-unit error after pooling the premise readouts.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Comparisons.EnsembleAveraging

open scoped BigOperators
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.InformationTheory.FiniteRV

/-- The exact between-model covariance contribution for two equally weighted
models with common middle and target marginals. -/
theorem two_model_deduction_gap (x₁ x₂ y₁ y₂ b c : ℝ) (middleNotFull : b ≠ 1) :
    (plnDeductionStrength x₁ y₁ b c + plnDeductionStrength x₂ y₂ b c) / 2 -
      plnDeductionStrength ((x₁+x₂)/2) ((y₁+y₂)/2) b c =
        (x₁-x₂) * (y₁-y₂) / (4 * (1-b)) := by
  have denominator : 1-b ≠ 0 := sub_ne_zero.mpr (Ne.symm middleNotFull)
  unfold plnDeductionStrength
  field_simp
  ring

/-- Conditioning a mixture generally differs from averaging conditional
answers. The discrepancy depends on variation in carrier masses as well. -/
theorem two_model_conditioning_gap (m₁ m₂ t₁ t₂ : ℝ) (possible : m₁+m₂ ≠ 0) :
    (m₁*t₁ + m₂*t₂) / (m₁+m₂) - (t₁+t₂)/2 =
      (m₁-m₂) * (t₁-t₂) / (2*(m₁+m₂)) := by
  field_simp
  ring

/-- Constant antecedent-to-middle or middle-to-target readouts eliminate the
covariance contribution when the two marginals are shared. -/
theorem two_model_deduction_exact_if_constant (x₁ x₂ y₁ y₂ b c : ℝ)
    (middleNotFull : b ≠ 1) (constant : x₁ = x₂ ∨ y₁ = y₂) :
    (plnDeductionStrength x₁ y₁ b c + plnDeductionStrength x₂ y₂ b c) / 2 =
      plnDeductionStrength ((x₁+x₂)/2) ((y₁+y₂)/2) b c := by
  apply sub_eq_zero.mp
  rw [two_model_deduction_gap x₁ x₂ y₁ y₂ b c middleNotFull]
  rcases constant with same | same <;> simp [same]

namespace Controls

/-- Unequal conditioning-event masses distinguish a joint mixture from an
unweighted mean of conditional answers. -/
theorem conditioning_differs_from_answer_pooling :
    ((1/4 : ℝ)*1 + (3/4)*0) / ((1/4)+(3/4)) = 1/4 ∧
      ((1 : ℝ)+0)/2 = 1/2 := by
  norm_num

private theorem sum_eight (value : Fin (2^3) → ℝ) :
    (∑ world, value world) = value 0 + (value 1 + (value 2 + (value 3 +
      (value 4 + (value 5 + (value 6 + value 7)))))) := by
  change (∑ world : Fin 8, value world) = _
  simp [Fin.sum_univ_succ]

/-- The first model makes all three Boolean atoms equal. -/
noncomputable def first : JointDistribution 3 where
  prob world := match world.val with | 0 => 1/2 | 7 => 1/2 | _ => 0
  prob_nonneg world := by split <;> norm_num
  prob_sum_one := by norm_num [sum_eight]

/-- The second model keeps the first and third atoms equal while reversing
both relative to the middle atom. -/
noncomputable def second : JointDistribution 3 where
  prob world := match world.val with | 2 => 1/2 | 5 => 1/2 | _ => 0
  prob_nonneg world := by split <;> norm_num
  prob_sum_one := by norm_num [sum_eight]

noncomputable def pooledEstimate : ℝ :=
  plnDeductionStrength ((condProb first 1 0 + condProb second 1 0)/2)
    ((condProb first 2 1 + condProb second 2 1)/2)
    ((marginalProb first 1 + marginalProb second 1)/2)
    ((marginalProb first 2 + marginalProb second 2)/2)

theorem individual_cmi_zero :
    condMutualInfo first.prob (worldToAssignment 3 · 0)
      (worldToAssignment 3 · 1) (worldToAssignment 3 · 2) = 0 ∧
      condMutualInfo second.prob (worldToAssignment 3 · 0)
        (worldToAssignment 3 · 1) (worldToAssignment 3 · 2) = 0 := by
  constructor
  · apply (condMutualInfo_eq_zero_iff first.prob first.prob_nonneg _ _ _).mpr
    rintro ⟨a, b, c⟩
    cases a <;> cases b <;> cases c <;>
      norm_num [CondIndep, law3, law2, pushforward_eq_sum_ite, first, sum_eight, worldToAssignment]
  · apply (condMutualInfo_eq_zero_iff second.prob second.prob_nonneg _ _ _).mpr
    rintro ⟨a, b, c⟩
    cases a <;> cases b <;> cases c <;>
      norm_num [CondIndep, law3, law2, pushforward_eq_sum_ite, second, sum_eight, worldToAssignment]

theorem pooled_readouts_have_half_error :
    (completeDeduction first 0 1 2 + completeDeduction second 0 1 2)/2 = 1 ∧
      pooledEstimate = 1/2 := by
  norm_num [completeDeduction, pooledEstimate, plnDeductionStrength, condProb,
    jointProb2, marginalProb, first, second, sum_eight, worldToAssignment]

/-- Per-component conditional independence does not license applying PLN to
averaged premise answers without an aggregation term. This is a finite-table
control, independent of any particular CPT construction. -/
theorem independence_does_not_remove_aggregation_gap :
    condMutualInfo first.prob (worldToAssignment 3 · 0)
      (worldToAssignment 3 · 1) (worldToAssignment 3 · 2) = 0 ∧
      condMutualInfo second.prob (worldToAssignment 3 · 0)
        (worldToAssignment 3 · 1) (worldToAssignment 3 · 2) = 0 ∧
      |(completeDeduction first 0 1 2 + completeDeduction second 0 1 2)/2 - pooledEstimate| = 1/2 := by
  exact ⟨individual_cmi_zero.1, individual_cmi_zero.2,
    by rw [pooled_readouts_have_half_error.1, pooled_readouts_have_half_error.2]; norm_num⟩

end Controls
end Mettapedia.PLN.Comparisons.EnsembleAveraging
