import MettapediaFourColor.TwoFiveWheelOccurrence
import MettapediaFourColor.SecondFanResidual

/-!
# The second fan supplies a complete wheel, not just a degree pattern

The exact charge classification is consumed on the same actual centre and
marked five. Its two-five branch constructs all vertices of one twelve-port
wheel and retains the second five, radius bound and exact charge observations.
Full wheel repair is not assumed for this geometric supply theorem.
-/

namespace FourColor.SecondFanWheelOccurrence

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality
open MinimalExceptionalEmbedding (graph rotation)
open RuleFanSupply CyclicCharge CyclicFanContinuation ExactCyclicCharge
open ChainFanRecognition (walk walk_next)

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

theorem alternatives (d : (graph original minimal).Dart)
    (fixed : Fixed (rotation original minimal) d)
    (seven : (graph original minimal).degree (secondFree (rotation original minimal) d) = 7)
    (flat : NearLinearCharge.finalCharge (rotation original minimal)
      (secondFree (rotation original minimal) d) = 0) :
    (∃ w, w ≠ d.snd ∧ w ≠ secondFree (rotation original minimal) d ∧
      (graph original minimal).Adj (secondFree (rotation original minimal) d) w ∧
      w ∈ LocalCoverageAssembly.closedBall (graph original minimal) d.snd 3 ∧
      7 ≤ (graph original minimal).degree w) ∨
    (∃ o : D3009Boundary.Occurrence (rotation original minimal),
      o.hom 13 = secondFree (rotation original minimal) d ∧
      o.hom 14 = (walk (rotation original minimal) d 5).snd) ∨
    (∃ p : Fin 6, ∃ o : WheelBoundaryCompletion.Occurrence
        (WheelBoundaryLayouts.twoFive p) (rotation original minimal),
      o.hom 12 = secondFree (rotation original minimal) d ∧
      o.hom 13 = (walk (rotation original minimal) d 5).snd ∧
      o.hom ((D3009Wheel.rim (TwoFiveWheelData.selected p)).natAdd 12) ≠ o.hom 13 ∧
      (graph original minimal).degree
        (o.hom ((D3009Wheel.rim (TwoFiveWheelData.selected p)).natAdd 12)) = 5 ∧
      fiveCount (G := graph original minimal) (o.hom 12) = 2 ∧
      tipCount (rotation original minimal) (o.hom 12) = 1 ∧
      extraCount (rotation original minimal) (o.hom 12) = 0 ∧
      (∀ e : Star (G := graph original minimal) (o.hom 12),
        ∀ j ∈ extraRules, RuleMatcher.check (rotation original minimal) j e.val.symm = false)) := by
  let r := rotation original minimal
  have tri := MinimalExceptionalEmbedding.triangular original minimal
  have bp : (graph original minimal).Adj (secondFree r d) (walk r d 5).snd := by
    have h := ExceptionalOverlap.consecutive_adjacent r tri (walk r d 4)
    rw [walk_next] at h
    exact h
  let e : (graph original minimal).Dart := ⟨(secondFree r d,(walk r d 5).snd),bp⟩
  rcases ActualSecondFanResidual.profile_alternatives original minimal d fixed seven flat with
    high | single | ⟨q,adj,distinct,five,six,count,tips,extras,noextra⟩
  · exact Or.inl high
  · exact Or.inr (Or.inl ⟨ActualWheelOccurrence.occurrence original minimal e
      seven fixed.last single, rfl, rfl⟩)
  · obtain ⟨p,o,centre,marked,second⟩ := TwoFiveWheelOccurrence.supplied original minimal
      e seven fixed.last q adj five distinct six
    refine Or.inr (Or.inr ⟨p,o,centre,marked,?_,?_,?_,?_,?_,?_⟩)
    · rw [second,marked]; exact distinct
    · rw [second]; exact five
    · rw [centre]; exact count
    · rw [centre]; exact tips
    · rw [centre]; exact extras
    · rw [centre]; exact noextra

end
end FourColor.SecondFanWheelOccurrence
