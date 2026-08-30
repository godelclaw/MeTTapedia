import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairOverlapStateReversal
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeClosureReversal

/-!
# Reversing the realised two-site overlap support

The complete finite state set realised by two Kempe orbits is independent of
which direction the physical pair of sites is read.  Reversing direction
exchanges the two sites and applies the explicit overlap-state involution.

No cancellation or wall-exclusion conclusion is drawn here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AdjacentPairOverlapSupportReversal

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairReversal
open GoertzelV24AdjacentPairStateReversal
open GoertzelV24AdjacentPairOverlapStateReversal
open GoertzelV24AdjacentPairKempeClosureReversal
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Reversal and source--target exchange identify the complete finite overlap
supports realised by the two Kempe orbits. -/
theorem overlapKempeStateSupport_reverse_swap
    (source target : AdjacentPairData G)
    (sourceBase : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetBase : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) :
    reverseOverlapKempeState ''
        overlapKempeStateSupport source target sourceBase targetBase =
      overlapKempeStateSupport (reverse target) (reverse source)
        (reverseColoring target targetBase)
        (reverseColoring source sourceBase) := by
  ext state
  constructor
  · rintro ⟨originalState, horiginal, rfl⟩
    rcases horiginal with
      ⟨sourceColoring, hsourceClosure, hsourceTait,
        targetColoring, htargetClosure, htargetTait, rfl⟩
    refine ⟨reverseColoring target targetColoring,
      mem_edgeKempeClosure_reverseColoring target htargetClosure,
      isTaitEdgeColoring_reverseColoring target targetColoring htargetTait,
      reverseColoring source sourceColoring,
      mem_edgeKempeClosure_reverseColoring source hsourceClosure,
      isTaitEdgeColoring_reverseColoring source sourceColoring hsourceTait,
      ?_⟩
    exact (overlapKempeState_reverse_swap source target
      sourceColoring targetColoring).symm
  · intro hreversed
    rcases hreversed with
      ⟨reversedSourceColoring, hreversedSourceClosure,
        hreversedSourceTait, reversedTargetColoring,
        hreversedTargetClosure, hreversedTargetTait, rfl⟩
    let sourceColoring :=
      reverseColoring (reverse source) reversedTargetColoring
    let targetColoring :=
      reverseColoring (reverse target) reversedSourceColoring
    have hsourceClosure : sourceColoring ∈
        (OriginalGraph source).EdgeKempeClosure sourceBase := by
      have hback := mem_edgeKempeClosure_reverseColoring
        (data := reverse source) hreversedTargetClosure
      change sourceColoring ∈
        (OriginalGraph source).EdgeKempeClosure
          (reverseColoring (reverse source)
            (reverseColoring source sourceBase)) at hback
      simpa using hback
    have htargetClosure : targetColoring ∈
        (OriginalGraph target).EdgeKempeClosure targetBase := by
      have hback := mem_edgeKempeClosure_reverseColoring
        (data := reverse target) hreversedSourceClosure
      change targetColoring ∈
        (OriginalGraph target).EdgeKempeClosure
          (reverseColoring (reverse target)
            (reverseColoring target targetBase)) at hback
      simpa using hback
    have hsourceTait : IsTaitEdgeColoring (OriginalGraph source)
        sourceColoring := by
      have hback := isTaitEdgeColoring_reverseColoring
        (reverse source) reversedTargetColoring hreversedTargetTait
      simpa [sourceColoring] using hback
    have htargetTait : IsTaitEdgeColoring (OriginalGraph target)
        targetColoring := by
      have hback := isTaitEdgeColoring_reverseColoring
        (reverse target) reversedSourceColoring hreversedSourceTait
      simpa [targetColoring] using hback
    refine ⟨overlapKempeState source target sourceColoring targetColoring,
      ⟨sourceColoring, hsourceClosure, hsourceTait,
        targetColoring, htargetClosure, htargetTait, rfl⟩, ?_⟩
    have hstate := overlapKempeState_reverse_swap source target
      sourceColoring targetColoring
    simpa [sourceColoring, targetColoring] using hstate.symm

end

end GoertzelV24AdjacentPairOverlapSupportReversal

end Mettapedia.GraphTheory.FourColor
