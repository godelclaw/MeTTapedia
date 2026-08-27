import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualCycleSeparator
import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualPathTransversalPair

/-!
# Closing a selected transversal pair into a selected dual cycle

Two separated selected transversals have a canonical closed facial-dual walk:
follow the left path and return along the reverse of the right path.  This file
retains the literal primal crossing chosen by the corresponding source path at
every step of that closed walk.  It is pure finite-index bookkeeping; no face
intersection uniqueness is assumed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SelectedDualPathTransversal

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24SelectedDualCycleSeparator

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace SeparatedAlignedSelectedDualTransversals

/-- The original right-path step corresponding to a step of its reversed
walk. -/
def originalRightStep
    {RS : RotationSystem V E}
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (step : Fin pair.right.crosscut.walk.reverse.length) :
    Fin pair.right.crosscut.walk.length :=
  ⟨pair.right.crosscut.walk.length - (step.val + 1), by
    have hstep : step.val < pair.right.crosscut.walk.length := by
      simpa using step.isLt
    omega⟩

/-- The literally selected primal crossing of the closed paired walk.  Steps
in the second summand are read in reverse order from the right transversal. -/
def pairedCycleCrossingEdge
    {RS : RotationSystem V E}
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (step : Fin pair.dualLoop.length) : E :=
  if hleft : step.val < pair.left.crosscut.walk.length then
    pair.left.crossingEdge ⟨step.val, hleft⟩
  else
    let reverseStep : Fin pair.right.crosscut.walk.reverse.length :=
      ⟨step.val - pair.left.crosscut.walk.length, by
        have hstep : step.val < pair.left.crosscut.walk.length +
            pair.right.crosscut.walk.length := by
          calc
            step.val < pair.dualLoop.length := step.isLt
            _ = _ := pair.dualLoop_length
        simpa using (show step.val - pair.left.crosscut.walk.length <
          pair.right.crosscut.walk.length by omega)⟩
    pair.right.crossingEdge (pair.originalRightStep reverseStep)

/-- On the left summand, the paired-cycle crossing is definitionally the
selected left crossing. -/
@[simp] theorem pairedCycleCrossingEdge_left
    {RS : RotationSystem V E}
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (step : Fin pair.left.crosscut.walk.length) :
    pair.pairedCycleCrossingEdge
        ⟨step.val, by rw [pair.dualLoop_length]; omega⟩ =
      pair.left.crossingEdge step := by
  simp [pairedCycleCrossingEdge, step.isLt]

/-- On the reversed right summand, the paired-cycle crossing is the selected
right crossing at the corresponding original position. -/
@[simp] theorem pairedCycleCrossingEdge_rightReverse
    {RS : RotationSystem V E}
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (step : Fin pair.right.crosscut.walk.reverse.length) :
    pair.pairedCycleCrossingEdge
        ⟨pair.left.crosscut.walk.length + step.val, by
          rw [pair.dualLoop_length]
          have := step.isLt
          simpa using this⟩ =
      pair.right.crossingEdge (pair.originalRightStep step) := by
  simp [pairedCycleCrossingEdge]

/-- The selected closed cycle induced by the paired transversals. -/
def selectedDualCycle
    {RS : RotationSystem V E}
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish) :
    SelectedDualCycle RS start where
  walk := pair.dualLoop
  isCycle := pair.dualLoop_isCycle
  crossingEdge := pair.pairedCycleCrossingEdge
  crossing_mem_shared := by
    intro step
    by_cases hleft : step.val < pair.left.crosscut.walk.length
    · let leftStep : Fin pair.left.crosscut.walk.length := ⟨step.val, hleft⟩
      have hgetLeft : pair.dualLoop.getVert step.val =
          pair.left.crosscut.walk.getVert leftStep.val := by
        change (pair.left.crosscut.walk.append
          pair.right.crosscut.walk.reverse).getVert step.val = _
        rw [SimpleGraph.Walk.getVert_append]
        simp [leftStep, hleft]
      have hgetRight : pair.dualLoop.getVert (step.val + 1) =
          pair.left.crosscut.walk.getVert (leftStep.val + 1) := by
        change (pair.left.crosscut.walk.append
          pair.right.crosscut.walk.reverse).getVert (step.val + 1) = _
        rw [SimpleGraph.Walk.getVert_append]
        by_cases hnext : step.val + 1 < pair.left.crosscut.walk.length
        · simp [leftStep, hnext]
        · have hlast : step.val + 1 = pair.left.crosscut.walk.length := by
            omega
          simp [leftStep, hlast]
      simpa [pairedCycleCrossingEdge, hleft, leftStep, hgetLeft, hgetRight]
        using pair.left.crossing_mem_shared leftStep
    · let reverseStep : Fin pair.right.crosscut.walk.reverse.length :=
        ⟨step.val - pair.left.crosscut.walk.length, by
          have hstep : step.val < pair.left.crosscut.walk.length +
              pair.right.crosscut.walk.length := by
            calc
              step.val < pair.dualLoop.length := step.isLt
              _ = _ := pair.dualLoop_length
          simpa using (show step.val - pair.left.crosscut.walk.length <
            pair.right.crosscut.walk.length by omega)⟩
      let originalStep := pair.originalRightStep reverseStep
      have hgetLeft : pair.dualLoop.getVert step.val =
          pair.right.crosscut.walk.getVert (originalStep.val + 1) := by
        change (pair.left.crosscut.walk.append
          pair.right.crosscut.walk.reverse).getVert step.val = _
        rw [SimpleGraph.Walk.getVert_append]
        have hnot : ¬ step.val < pair.left.crosscut.walk.length := hleft
        simp only [hnot, ↓reduceIte]
        rw [SimpleGraph.Walk.getVert_reverse]
        congr 1
        dsimp [reverseStep, originalStep, originalRightStep]
        have hstep : step.val < pair.left.crosscut.walk.length +
            pair.right.crosscut.walk.length := by
          simpa [pair.dualLoop_length] using step.isLt
        omega
      have hgetRight : pair.dualLoop.getVert (step.val + 1) =
          pair.right.crosscut.walk.getVert originalStep.val := by
        change (pair.left.crosscut.walk.append
          pair.right.crosscut.walk.reverse).getVert (step.val + 1) = _
        rw [SimpleGraph.Walk.getVert_append]
        have hnot : ¬ step.val + 1 < pair.left.crosscut.walk.length := by omega
        simp only [hnot, ↓reduceIte]
        rw [SimpleGraph.Walk.getVert_reverse]
        congr 1
        dsimp [reverseStep, originalStep, originalRightStep]
        have hstep : step.val < pair.left.crosscut.walk.length +
            pair.right.crosscut.walk.length := by
          simpa [pair.dualLoop_length] using step.isLt
        omega
      have hshared := pair.right.crossing_mem_shared originalStep
      have hedge : pair.pairedCycleCrossingEdge step =
          pair.right.crossingEdge originalStep := by
        simp [pairedCycleCrossingEdge, hleft, reverseStep, originalStep]
      rw [hedge, hgetLeft, hgetRight]
      rw [mem_sharedInteriorEdges_iff]
      rcases (mem_sharedInteriorEdges_iff
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).1 hshared with
        ⟨hinterior, hfirst, hsecond⟩
      exact ⟨hinterior, hsecond, hfirst⟩

/-- The selected cycle retains exactly the union of the two source crossing
supports. -/
theorem selectedDualCycle_crossingEdges
    {RS : RotationSystem V E}
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish) :
    pair.selectedDualCycle.crossingEdges = pair.crossingSupport := by
  ext edge
  simp only [GoertzelV24SelectedDualCycleSeparator.SelectedDualCycle.mem_crossingEdges_iff,
    crossingSupport, Finset.mem_union,
    SelectedDualPathTransversal.mem_crossingEdges_iff]
  constructor
  · rintro ⟨step, hstep⟩
    by_cases hleft : step.val < pair.left.crosscut.walk.length
    · left
      refine ⟨⟨step.val, hleft⟩, ?_⟩
      simpa [selectedDualCycle, pairedCycleCrossingEdge, hleft] using hstep
    · right
      let reverseStep : Fin pair.right.crosscut.walk.reverse.length :=
        ⟨step.val - pair.left.crosscut.walk.length, by
          have hstep : step.val < pair.left.crosscut.walk.length +
              pair.right.crosscut.walk.length := by
            calc
              step.val < pair.dualLoop.length := step.isLt
              _ = _ := pair.dualLoop_length
          simpa using (show step.val - pair.left.crosscut.walk.length <
            pair.right.crosscut.walk.length by omega)⟩
      refine ⟨pair.originalRightStep reverseStep, ?_⟩
      simpa [selectedDualCycle, pairedCycleCrossingEdge, hleft, reverseStep]
        using hstep
  · rintro (⟨leftStep, hleft⟩ | ⟨rightStep, hright⟩)
    · refine ⟨⟨leftStep.val, by
          change leftStep.val < pair.dualLoop.length
          rw [pair.dualLoop_length]
          omega⟩, ?_⟩
      simpa [selectedDualCycle] using hleft
    · let reverseStep : Fin pair.right.crosscut.walk.reverse.length :=
        ⟨pair.right.crosscut.walk.length - (rightStep.val + 1), by
          rw [SimpleGraph.Walk.length_reverse]
          omega⟩
      have horiginal : pair.originalRightStep reverseStep = rightStep := by
        apply Fin.ext
        dsimp [reverseStep, originalRightStep]
        omega
      refine ⟨⟨pair.left.crosscut.walk.length + reverseStep.val, by
          change pair.left.crosscut.walk.length + reverseStep.val < pair.dualLoop.length
          rw [pair.dualLoop_length]
          have := reverseStep.isLt
          simpa using this⟩, ?_⟩
      simpa [selectedDualCycle, horiginal] using hright

end SeparatedAlignedSelectedDualTransversals

end

end GoertzelV24SelectedDualPathTransversal

end Mettapedia.GraphTheory.FourColor
