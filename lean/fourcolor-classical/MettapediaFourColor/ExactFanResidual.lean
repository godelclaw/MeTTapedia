import MettapediaFourColor.ExactCyclicCharge

/-!
# Two exact remaining budgets at the shared fan

The actual-map continuation now retains the complete residual charge
budget and the already excluded extra-rule observation on its marked edge.
The two budgets are open geometric obligations, not abstract repair inputs.
-/

namespace FourColor.ExactFanResidual

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality
open ActualRulePairDiamond (graph rotation)
open RuleFanSupply ExtraChargeReduction CyclicCharge CyclicFanContinuation ExactCyclicCharge
open ChainFanRecognition (walk walk_fst walk_next)

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

/-- A third centre, or one of two exact single-five budgets, with the
same actual vertices and the existing reduction exclusion retained. -/
theorem alternatives (d : (graph original minimal).Dart)
    (fixed : Fixed (rotation original minimal) d)
    (seven : (graph original minimal).degree (firstFree (rotation original minimal) d) = 7)
    (flat : NearLinearCharge.finalCharge (rotation original minimal)
      (firstFree (rotation original minimal) d) = 0) :
    (∃ w, w ≠ d.snd ∧ w ≠ firstFree (rotation original minimal) d ∧
      (graph original minimal).Adj (firstFree (rotation original minimal) d) w ∧
      w ∈ LocalCoverageAssembly.closedBall (graph original minimal) d.snd 3 ∧
      7 ≤ (graph original minimal).degree w) ∨
    ((∀ w, (graph original minimal).Adj (firstFree (rotation original minimal) d) w →
      w ≠ (walk (rotation original minimal) d 2).snd → (graph original minimal).degree w = 6) ∧
      RuleMatcher.check (rotation original minimal) 5
        (fanRoot (rotation original minimal)
          (MinimalExceptionalEmbedding.triangular original minimal) d) = false ∧
      ((tipCount (rotation original minimal) (firstFree (rotation original minimal) d) = 2 ∧
        residualCount (rotation original minimal) (firstFree (rotation original minimal) d) = 2) ∨
       (tipCount (rotation original minimal) (firstFree (rotation original minimal) d) = 3 ∧
        residualCount (rotation original minimal)
          (firstFree (rotation original minimal) d) = 0))) := by
  rcases ActualExtraChargeReduction.flat_alternatives original minimal d fixed seven flat with
    high | ⟨residual,no⟩
  · exact Or.inl high
  · refine Or.inr ⟨residual,no,?_⟩
    have tri := MinimalExceptionalEmbedding.triangular original minimal
    apply flat_seven_cases (rotation original minimal) tri _ _ seven
      (fanRoot (rotation original minimal) tri d).adj.symm fixed.second residual
      (fan_tips (rotation original minimal) tri d fixed) flat

end
end FourColor.ExactFanResidual
