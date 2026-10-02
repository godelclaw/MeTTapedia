import MettapediaFourColor.RulePairExample

/-! A nonempty instance of the identified-corner branch in the same
certified cyclic triangular rotation as the mixed-diamond example. -/

namespace FourColor.RulePairCollisionExample

open RulePairExample

local instance (r : Fin 84) : NeZero (NearLinearRuleData.size r) :=
  ⟨by have := (NearLinearRuleData.headers r).1; omega⟩

def root : graph.Dart := ⟨(41, 39), by decide +kernel⟩

def leftImages (i : NearLinearRuleData.Vertex 4) : Fin 42 :=
  ([41, 39, 32, 30] : List (Fin 42)).getD i.val 0

def rightImages (i : NearLinearRuleData.Vertex 5) : Fin 42 :=
  ([9, 39, 32, 4, 30] : List (Fin 42)).getD i.val 0

theorem left_candidate : RuleMatcher.candidate rotation 4 root = leftImages := by
  funext i
  fin_cases i <;> decide +kernel

theorem right_candidate : RuleMatcher.candidate rotation 5
    (RulePairDiamond.secondRoot (rotation := rotation) root) = rightImages := by
  funext i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
-- Evaluate the full finite constraints after caching their vertex readings.
/-- Both full rule checks hold, including the three degree-five guards. -/
theorem observations :
    RuleMatcher.check rotation 4 root = true ∧
    RuleMatcher.check rotation 5 (RulePairDiamond.secondRoot (rotation := rotation) root) = true ∧
    graph.degree root.fst = 5 ∧
    graph.degree (RuleMatcher.candidate rotation 4 root 2) = 5 ∧
    graph.degree (RuleMatcher.candidate rotation 5
      (RulePairDiamond.secondRoot (rotation := rotation) root) 3) = 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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

/-- Genuine shared rule readings consume the uniform collision argument. -/
theorem has_pentagonal : ∃ d : graph.Dart, RulePairDiamond.PentagonalAt rotation d :=
  RulePairDiamond.pentagonal_of_checks cyclic triangular root observations.1
    observations.2.1 observations.2.2.1 observations.2.2.2.1 observations.2.2.2.2

end FourColor.RulePairCollisionExample
