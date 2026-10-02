import MettapediaFourColor.RulePairBudget
import MettapediaFourColor.ActualRulePairDiamond

/-! Joint signed supply in the actual minimal-map domain. Both diamond
reductions determine the surviving degree profile; the paired rule argument
then covers either possible degree of the second sender. -/

namespace FourColor.ActualRulePairBudget

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality RulePairDiamond ActualRulePairDiamond RuleMatcher

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

/-- No separate degree choice or distinct-sender premise is required. -/
theorem paired_budget (d : (graph original minimal).Dart)
    (left : check (rotation original minimal) 4 d = true)
    (right : check (rotation original minimal) 5
      (secondRoot (rotation := rotation original minimal) d) = true)
    (sender : (graph original minimal).degree d.fst = 5)
    (receiver : 7 ≤ (graph original minimal).degree d.snd) :
    d.fst ≠ (secondRoot (rotation := rotation original minimal) d).fst ∧
    7 ≤ NearLinearCharge.net (rotation original minimal) d.fst d.snd +
      NearLinearCharge.net (rotation original minimal)
        (secondRoot (rotation := rotation original minimal) d).fst d.snd := by
  obtain ⟨five, outer⟩ := surviving_pair_degrees original minimal d left right sender
  exact RulePairBudget.joint_seven (MinimalExceptionalEmbedding.cyclic original minimal)
    d left right sender five outer receiver

/-- A flat eight-valent centre has at most thirteen net units outside
the two distinct incoming edges. All other signed transfers remain present. -/
theorem flat_remainder (d : (graph original minimal).Dart)
    (left : check (rotation original minimal) 4 d = true)
    (right : check (rotation original minimal) 5
      (secondRoot (rotation := rotation original minimal) d) = true)
    (sender : (graph original minimal).degree d.fst = 5)
    (eight : (graph original minimal).degree d.snd = 8)
    (flat : NearLinearCharge.finalCharge (rotation original minimal) d.snd = 0) :
    RulePairBudget.pairRemainder (rotation := rotation original minimal)
      d.fst (secondRoot (rotation := rotation original minimal) d).fst d.snd ≤ 13 := by
  obtain ⟨five, outer⟩ := surviving_pair_degrees original minimal d left right sender
  exact RulePairBudget.flat_pair_remainder (MinimalExceptionalEmbedding.cyclic original minimal)
    d left right sender five outer eight flat

end
end FourColor.ActualRulePairBudget
