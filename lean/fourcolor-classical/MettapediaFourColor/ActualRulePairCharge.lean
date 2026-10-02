import MettapediaFourColor.RulePairCharge
import MettapediaFourColor.ActualRulePairDiamond

/-! The actual minimal-map consumer of the joint rule law. The degree
profile is obtained by the two established strict reductions, before the
third occurrence and its charge are reconstructed. -/

namespace FourColor.ActualRulePairCharge

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality RulePairDiamond ActualRulePairDiamond RuleMatcher

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

/-- A surviving pair forces the larger rule and at least three units of
incoming charge. The two excluded profiles use genuine colour reconstruction. -/
theorem third_and_charge (d : (graph original minimal).Dart)
    (left : check (rotation original minimal) 4 d = true)
    (right : check (rotation original minimal) 5
      (secondRoot (rotation := rotation original minimal) d) = true)
    (sender : (graph original minimal).degree d.fst = 5)
    (second : (graph original minimal).degree
      (secondRoot (rotation := rotation original minimal) d).fst = 6)
    (receiver : 7 ≤ (graph original minimal).degree d.snd) :
    check (rotation original minimal) 9
      (secondRoot (rotation := rotation original minimal) d) = true ∧
    3 ≤ NearLinearCharge.net (rotation original minimal)
      (secondRoot (rotation := rotation original minimal) d).fst d.snd := by
  obtain ⟨five, outer⟩ := surviving_pair_degrees original minimal d left right sender
  have h9 := RulePairCharge.third_of_checks (MinimalExceptionalEmbedding.cyclic original minimal)
    d left right sender five outer second receiver
  refine ⟨h9, ?_⟩
  have h := RulePairCharge.net_three _ right h9
  rw [RulePairCharge.second_receiver] at h
  exact h

/-- The surviving overlap constrains the remaining net supply at a flat
eight-valent centre, using the actual minimal-map reductions. -/
theorem flat_remainder (d : (graph original minimal).Dart)
    (left : check (rotation original minimal) 4 d = true)
    (right : check (rotation original minimal) 5
      (secondRoot (rotation := rotation original minimal) d) = true)
    (sender : (graph original minimal).degree d.fst = 5)
    (second : (graph original minimal).degree
      (secondRoot (rotation := rotation original minimal) d).fst = 6)
    (eight : (graph original minimal).degree d.snd = 8)
    (flat : NearLinearCharge.finalCharge (rotation original minimal) d.snd = 0) :
    RulePairCharge.remainingSupply (rotation := rotation original minimal)
      (secondRoot (rotation := rotation original minimal) d).fst d.snd ≤ 17 := by
  obtain ⟨h9, _⟩ := third_and_charge original minimal d left right sender second (by omega)
  have he := RulePairCharge.second_receiver (rotation := rotation original minimal) d
  have h := RulePairCharge.flat_remainder (secondRoot (rotation := rotation original minimal) d)
    (he ▸ eight) (he ▸ flat) right h9
  rw [he] at h
  exact h

end
end FourColor.ActualRulePairCharge
