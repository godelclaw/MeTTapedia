import MettapediaFourColor.RulePairExample
import MettapediaFourColor.RulePairCharge

/-! A nonempty instance of the joint charge implication on the same
certified cyclic triangular rotation as the two reduction examples. -/

namespace FourColor.RulePairChargeExample

open RulePairExample

local instance (r : Fin 84) : NeZero (NearLinearRuleData.size r) :=
  ⟨by have := (NearLinearRuleData.headers r).1; omega⟩

def root : graph.Dart := ⟨(7, 11), by decide +kernel⟩

def leftImages (i : NearLinearRuleData.Vertex 4) : Fin 42 :=
  ([7, 11, 36, 27] : List (Fin 42)).getD i.val 0

def rightImages (i : NearLinearRuleData.Vertex 5) : Fin 42 :=
  ([9, 11, 36, 39, 27] : List (Fin 42)).getD i.val 0

theorem left_candidate : RuleMatcher.candidate rotation 4 root = leftImages := by
  funext i
  fin_cases i <;> decide +kernel

theorem right_candidate : RuleMatcher.candidate rotation 5
    (RulePairDiamond.secondRoot (rotation := rotation) root) = rightImages := by
  funext i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
-- Check all source constraints after computing each vertex reading once.
theorem observations :
    RuleMatcher.check rotation 4 root = true ∧
    RuleMatcher.check rotation 5 (RulePairDiamond.secondRoot (rotation := rotation) root) = true ∧
    graph.degree root.fst = 5 ∧
    graph.degree (RuleMatcher.candidate rotation 4 root 2) = 5 ∧
    graph.degree (RuleMatcher.candidate rotation 5
      (RulePairDiamond.secondRoot (rotation := rotation) root) 3) = 6 ∧
    graph.degree (RulePairDiamond.secondRoot (rotation := rotation) root).fst = 6 ∧
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

/-- The larger occurrence is derived from gluing, not checked independently. -/
theorem has_third : RuleMatcher.check rotation 9
    (RulePairDiamond.secondRoot (rotation := rotation) root) = true :=
  RulePairCharge.third_of_checks cyclic root observations.1 observations.2.1
    observations.2.2.1 observations.2.2.2.1 observations.2.2.2.2.1
    observations.2.2.2.2.2.1 observations.2.2.2.2.2.2

theorem receives_three : 3 ≤ RuleMatcher.sentAt rotation
    (RulePairDiamond.secondRoot (rotation := rotation) root) :=
  RulePairCharge.three_of_checks _ observations.2.1 has_third

theorem net_receives_three : 3 ≤ NearLinearCharge.net rotation
    (RulePairDiamond.secondRoot (rotation := rotation) root).fst root.snd := by
  have h := RulePairCharge.net_three _ observations.2.1 has_third
  rw [RulePairCharge.second_receiver] at h
  exact h

end FourColor.RulePairChargeExample
