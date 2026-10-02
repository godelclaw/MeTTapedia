import MettapediaFourColor.RulePairChargeExample
import MettapediaFourColor.RulePairBudget

/-! Both possible second-sender degrees occur in the saved rotation.
Each example consumes the same paired-budget theorem. -/

namespace FourColor.RulePairBudgetExample

open RulePairExample

local instance (r : Fin 84) : NeZero (NearLinearRuleData.size r) :=
  ⟨by have := (NearLinearRuleData.headers r).1; omega⟩

/-- The previously checked degree-six branch supplies a paired budget. -/
theorem six_branch :
    RulePairChargeExample.root.fst ≠
      (RulePairDiamond.secondRoot (rotation := rotation) RulePairChargeExample.root).fst ∧
    7 ≤ NearLinearCharge.net rotation RulePairChargeExample.root.fst
      RulePairChargeExample.root.snd + NearLinearCharge.net rotation
        (RulePairDiamond.secondRoot (rotation := rotation) RulePairChargeExample.root).fst
        RulePairChargeExample.root.snd := by
  obtain ⟨hl, hr, hs, hf, ho, _, hc⟩ := RulePairChargeExample.observations
  exact RulePairBudget.joint_seven cyclic _ hl hr hs hf ho hc

def root : graph.Dart := ⟨(4, 16), by decide +kernel⟩

def leftImages (i : NearLinearRuleData.Vertex 4) : Fin 42 :=
  ([4, 16, 6, 30] : List (Fin 42)).getD i.val 0

def rightImages (i : NearLinearRuleData.Vertex 5) : Fin 42 :=
  ([37, 16, 6, 31, 30] : List (Fin 42)).getD i.val 0

theorem left_candidate : RuleMatcher.candidate rotation 4 root = leftImages := by
  funext i
  fin_cases i <;> decide +kernel

theorem right_candidate : RuleMatcher.candidate rotation 5
    (RulePairDiamond.secondRoot (rotation := rotation) root) = rightImages := by
  funext i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
-- Check the two complete readings and all degrees on cached vertex images.
theorem observations :
    RuleMatcher.check rotation 4 root = true ∧
    RuleMatcher.check rotation 5 (RulePairDiamond.secondRoot (rotation := rotation) root) = true ∧
    graph.degree root.fst = 5 ∧
    graph.degree (RuleMatcher.candidate rotation 4 root 2) = 5 ∧
    graph.degree (RuleMatcher.candidate rotation 5
      (RulePairDiamond.secondRoot (rotation := rotation) root) 3) = 6 ∧
    graph.degree (RulePairDiamond.secondRoot (rotation := rotation) root).fst = 5 ∧
    7 ≤ graph.degree root.snd := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RuleMatcher.check
    rw [left_candidate]
    decide +kernel
  · unfold RuleMatcher.check
    rw [right_candidate]
    decide +kernel
  · decide +kernel
  · rw [left_candidate]
    decide +kernel
  · rw [right_candidate]
    decide +kernel
  · decide +kernel
  · decide +kernel

/-- The same uniform argument covers a second sender of degree five. -/
theorem five_branch :
    root.fst ≠ (RulePairDiamond.secondRoot (rotation := rotation) root).fst ∧
    7 ≤ NearLinearCharge.net rotation root.fst root.snd +
      NearLinearCharge.net rotation
        (RulePairDiamond.secondRoot (rotation := rotation) root).fst root.snd := by
  obtain ⟨hl, hr, hs, hf, ho, _, hc⟩ := observations
  exact RulePairBudget.joint_seven cyclic _ hl hr hs hf ho hc

/-- The same branch retains its stronger lower bound rather than losing
the extra unit in the common seven-unit estimate. -/
theorem five_branch_eight :
    8 ≤ NearLinearCharge.net rotation root.fst root.snd +
      NearLinearCharge.net rotation
        (RulePairDiamond.secondRoot (rotation := rotation) root).fst root.snd := by
  obtain ⟨hl, hr, hs, hf, ho, hsecond, hc⟩ := observations
  have h := (RulePairBudget.joint_bound cyclic _ hl hr hs hf ho hc).2
  simpa only [hsecond, ite_true] using h

end FourColor.RulePairBudgetExample
