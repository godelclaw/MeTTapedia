import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteProfileReceipt

/-!
# A graph-free output decoder for an actual source boundary rebase

The actual opened-source rebase already supplies one finite packet whose
tracked and facial fields decode all five coordinates of the next
terminal-aware profile.  This file packages the dependent fragment count
with that packet and turns the fieldwise observations into one graph-free
profile decoder.

Every literal source rebase is decoded exactly.  This is the output half of
the recurrence only: the theorem does not say that the predecessor packet
and literal Cell support determine the output letter, nor does it claim a
reachable-state bound.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open SimpleGraphDartRotation

/-- A finite actual-source rebase output packages its dependent successor
fragment count together with the complete five-coordinate receipt. -/
structure SourceLocalLayerBoundaryRebaseFiniteOutputLetterCode where
  outputCount : Fin 5
  receipt :
    Instance.LocalLayerFormation.SourceLocalLayerBoundaryRebaseFiniteProfileReceipt

noncomputable instance :
    DecidableEq SourceLocalLayerBoundaryRebaseFiniteOutputLetterCode :=
  Classical.decEq _

private def sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeEquiv :
    SourceLocalLayerBoundaryRebaseFiniteOutputLetterCode ≃
      Fin 5 ×
        Instance.LocalLayerFormation.SourceLocalLayerBoundaryRebaseFiniteProfileReceipt where
  toFun code := ⟨code.outputCount, code.receipt⟩
  invFun code := { outputCount := code.1, receipt := code.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance :
    Fintype SourceLocalLayerBoundaryRebaseFiniteOutputLetterCode :=
  Fintype.ofEquiv _
    sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeEquiv.symm

/-- Fixed facial slot occupied by one row of the dependent decoded output. -/
def SourceLocalLayerBoundaryRebaseFiniteOutputLetterCode.outputFaceSlot
    (code : SourceLocalLayerBoundaryRebaseFiniteOutputLetterCode) :
    Fin code.outputCount.val → Fin 4 :=
  Fin.castLE (Nat.le_of_lt_succ code.outputCount.isLt)

/-- Decode the complete successor profile from one finite rebase letter. -/
noncomputable def
    SourceLocalLayerBoundaryRebaseFiniteOutputLetterCode.outputProfile
    (code : SourceLocalLayerBoundaryRebaseFiniteOutputLetterCode) :
    BoundedCorridorCutProfile 2 1 4 := by
  classical
  exact {
    faceFragmentCount := code.outputCount
    profile := {
      edgeColor := fun crossing =>
        code.receipt.tracked.roleColor
          (Instance.LocalLayerFormation.sourceLocalLayerBoundaryRebaseSuccessorPortRole
            (.inl crossing))
      strandConnected := fun pair left right => decide
        (code.receipt.tracked.connected pair
          (Instance.LocalLayerFormation.sourceLocalLayerBoundaryRebaseSuccessorPortRole
            left)
          (Instance.LocalLayerFormation.sourceLocalLayerBoundaryRebaseSuccessorPortRole
            right))
      faceContinues := fun left right =>
        code.receipt.facial.faceContinues
          (code.outputFaceSlot left) (code.outputFaceSlot right)
      fragmentContainsPort := fun fragment port =>
        code.receipt.facial.fragmentContainsPort
          (code.outputFaceSlot fragment) port
      faceLengthCap := fun fragment =>
        code.receipt.facial.faceLengthCap (code.outputFaceSlot fragment) }
  }

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialBoundaryRebaseFiniteOutputDecoderEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The canonical finite output letter extracted at one actual source
boundary rebase. -/
noncomputable def sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerBoundaryRebaseFiniteOutputLetterCode :=
  let output := sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor
    hunique (sourceLocalLayerNextOffset offset hnext)
  {
    outputCount := output.faceFragmentCount
    receipt := sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt corridor
      hunique offset hnext }

@[simp]
theorem sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt_outputCount
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt corridor hunique
      offset hnext).outputCount =
        (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext)).faceFragmentCount := by
  rfl

/-- The canonical graph-free output letter decodes exactly to the next
terminal-aware source profile. -/
theorem sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt_outputProfile_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt corridor hunique
      offset hnext).outputProfile =
        sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext) := by
  classical
  let output := sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor
    hunique (sourceLocalLayerNextOffset offset hnext)
  let code := sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt corridor
    hunique offset hnext
  simp only [sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt,
    SourceLocalLayerBoundaryRebaseFiniteOutputLetterCode.outputProfile]
  rw [BoundedCorridorCutProfile.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  rw [CorridorCutProfile.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext crossing
    exact sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt_edgeColor
      corridor hunique offset hnext crossing
  · funext pair left right
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt_strandConnected
      corridor hunique offset hnext pair left right
  · funext left right
    change
      (sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt corridor hunique
        offset hnext).facial.faceContinues
          (code.outputFaceSlot left) (code.outputFaceSlot right) =
        (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext)).profile.faceContinues
            left right
    have hslot (fragment : Fin output.faceFragmentCount.val) :
        code.outputFaceSlot fragment =
          sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
            hunique offset hnext
            (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
              hunique offset hnext fragment) := by
      rw [sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt_index]
      apply Fin.ext
      rfl
    rw [hslot left, hslot right]
    exact sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt_faceContinues
      corridor hunique offset hnext left right
  · funext fragment port
    change
      (sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt corridor hunique
        offset hnext).facial.fragmentContainsPort
          (code.outputFaceSlot fragment) port =
        (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext)).profile.fragmentContainsPort
            fragment port
    have hslot : code.outputFaceSlot fragment =
        sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
          hunique offset hnext
          (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
            hunique offset hnext fragment) := by
      rw [sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt_index]
      apply Fin.ext
      rfl
    rw [hslot]
    exact
      sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt_fragmentContainsPort
        corridor hunique offset hnext fragment port
  · funext fragment
    change
      (sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt corridor hunique
        offset hnext).facial.faceLengthCap (code.outputFaceSlot fragment) =
        (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext)).profile.faceLengthCap
            fragment
    have hslot : code.outputFaceSlot fragment =
        sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
          hunique offset hnext
          (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
            hunique offset hnext fragment) := by
      rw [sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt_index]
      apply Fin.ext
      rfl
    rw [hslot]
    exact sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt_faceLengthCap
      corridor hunique offset hnext fragment

/-- Existential form of the canonical exact output decoder. -/
theorem exists_sourceLocalLayerBoundaryRebaseFiniteOutputLetter_outputProfile_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    ∃ code : SourceLocalLayerBoundaryRebaseFiniteOutputLetterCode,
      code.outputProfile =
        sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext) :=
  ⟨sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt corridor hunique
      offset hnext,
    sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt_outputProfile_eq
      corridor hunique offset hnext⟩

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
