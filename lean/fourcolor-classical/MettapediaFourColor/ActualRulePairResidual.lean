import MettapediaFourColor.RulePairResidual
import MettapediaFourColor.ActualRulePairCharge

/-! Exclude the five-valent second sender through the existing mixed
diamond reduction, then derive the glued third rule without a supplied
second-sender degree. -/

namespace FourColor.ActualRulePairResidual

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality RulePairDiamond ActualRulePairDiamond RuleMatcher

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

local instance (r : Fin 84) : NeZero (NearLinearRuleData.size r) :=
  ⟨by have := (NearLinearRuleData.headers r).1; omega⟩

/-- Changing the chosen reduction edge eliminates the remaining degree-five
sender branch; strict descent and actual colouring reconstruction are reused. -/
theorem not_second_five (d : (graph original minimal).Dart)
    (left : check (rotation original minimal) 4 d = true)
    (right : check (rotation original minimal) 5
      (secondRoot (rotation := rotation original minimal) d) = true)
    (sender : (graph original minimal).degree d.fst = 5)
    (second : (graph original minimal).degree
      (secondRoot (rotation := rotation original minimal) d).fst = 5) : False := by
  obtain ⟨five, outer⟩ := surviving_pair_degrees original minimal d left right sender
  have shared := RulePairBudget.shared_candidates d left right
  have five' : (graph original minimal).degree
      (candidate (rotation original minimal) 5
        (secondRoot (rotation := rotation original minimal) d) 2) = 5 := shared ▸ five
  obtain ⟨e, he⟩ := RulePairResidual.right_mixed_of_check _ right second five' outer
  obtain ⟨root, hroot⟩ := face_pattern original minimal e he
  exact MixedDiamondPatch.Tangle.FaceReduction.not_in_minimal_counterexample_of_face_pattern
    original root hroot minimal

/-- The source bounds and the rerooted reduction force degree six. -/
theorem second_degree_six (d : (graph original minimal).Dart)
    (left : check (rotation original minimal) 4 d = true)
    (right : check (rotation original minimal) 5
      (secondRoot (rotation := rotation original minimal) d) = true)
    (sender : (graph original minimal).degree d.fst = 5) :
    (graph original minimal).degree
      (secondRoot (rotation := rotation original minimal) d).fst = 6 := by
  obtain ⟨y, ys, _⟩ := (check_iff (rotation original minimal) _).mp right
  have h := y.degree 0
  rw [show NearLinearRuleData.lower 5 0 = 5 from by decide +kernel,
    show NearLinearRuleData.upper 5 0 = 6 from by decide +kernel] at h
  change y.vertex 0 = (secondRoot (rotation := rotation original minimal) d).fst at ys
  rw [ys] at h
  change 5 ≤ (graph original minimal).degree
      (secondRoot (rotation := rotation original minimal) d).fst ∧
    (6 = 0 ∨ (graph original minimal).degree
      (secondRoot (rotation := rotation original minimal) d).fst ≤ 6) at h
  have hn := not_second_five original minimal d left right sender
  have interval (n : ℕ) (lower : 5 ≤ n) (upper : n ≤ 6) (notFive : n ≠ 5) : n = 6 := by
    omega
  exact interval _ h.1 (h.2.resolve_left (by decide)) hn

/-- Every surviving aligned pair with a five-valent first sender forces
the larger rule and three net units on its second edge. -/
theorem forced_third (d : (graph original minimal).Dart)
    (left : check (rotation original minimal) 4 d = true)
    (right : check (rotation original minimal) 5
      (secondRoot (rotation := rotation original minimal) d) = true)
    (sender : (graph original minimal).degree d.fst = 5)
    (receiver : 7 ≤ (graph original minimal).degree d.snd) :
    check (rotation original minimal) 9
      (secondRoot (rotation := rotation original minimal) d) = true ∧
    3 ≤ NearLinearCharge.net (rotation original minimal)
      (secondRoot (rotation := rotation original minimal) d).fst d.snd :=
  ActualRulePairCharge.third_and_charge original minimal d left right sender
    (second_degree_six original minimal d left right sender) receiver

end
end FourColor.ActualRulePairResidual
