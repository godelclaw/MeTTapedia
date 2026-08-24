import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolReceipt

/-!
# An executable support letter for one literal boundary rebase

A source Cell changes a terminal-aware input profile into a zero-terminal
profile.  Before the next Cell, a distinct finite rebase changes that boundary
presentation back into the next terminal-aware input.  This file packages the
two endpoints, the tracked core-plus-local collar, and the complete Boolean
successor receipt as one finite heterogeneous letter.

The support predicate checks that the successor profile is the receipt's
five-field decoder, that every guarded tracked bit agrees with the exact
core-plus-local closure, and that the occupied facial rows are represented by
distinct components of the facial closure.  Every actual source rebase
produces a supported letter.  No converse asserting that an arbitrary finite
letter has positive manuscript count, and no quotient by geometric
orientation, is claimed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolSupportLetter

open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolOutput
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolReceipt
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24HexSlabConnectivityProfile
open SimpleGraphDartRotation

/-- Complete finite data of one literal boundary rebase.  The input and output
are kept as explicit endpoints because the source word alternates Cell letters
and rebase letters. -/
structure SourceLocalLayerBoundaryRebaseFiniteBoolSupportLetter where
  input : BoundedCorridorCutProfile 2 0 4
  output : BoundedCorridorCutProfile 2 1 4
  trackedCode : BoundedCarrierBoolGraphFamilyCode 28 4
    (TrackedColorPair × Bool)
  outputCode : SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode

noncomputable instance :
    DecidableEq SourceLocalLayerBoundaryRebaseFiniteBoolSupportLetter :=
  Classical.decEq _

private def sourceLocalLayerBoundaryRebaseFiniteBoolSupportLetterEquiv :
    SourceLocalLayerBoundaryRebaseFiniteBoolSupportLetter ≃
      BoundedCorridorCutProfile 2 0 4 ×
        BoundedCorridorCutProfile 2 1 4 ×
          BoundedCarrierBoolGraphFamilyCode 28 4
            (TrackedColorPair × Bool) ×
          SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode where
  toFun letter :=
    ⟨letter.input, letter.output, letter.trackedCode, letter.outputCode⟩
  invFun data := ⟨data.1, data.2.1, data.2.2.1, data.2.2.2⟩
  left_inv letter := by cases letter; rfl
  right_inv data := rfl

noncomputable instance :
    Fintype SourceLocalLayerBoundaryRebaseFiniteBoolSupportLetter :=
  Fintype.ofEquiv _
    sourceLocalLayerBoundaryRebaseFiniteBoolSupportLetterEquiv.symm

/-- Guarded tracked closure computed by the rebase collar.  The guards are
load-bearing because graph reachability is reflexive even at an inactive or
untracked named role. -/
def SourceLocalLayerBoundaryRebaseTrackedClosureConnectedBool
    (state : SourceLocalLayerBoundaryRebaseTrackedState)
    (code : BoundedCarrierBoolGraphFamilyCode 28 4
      (TrackedColorPair × Bool))
    (pair : TrackedColorPair)
    (left right : SourceLocalLayerBoundaryRebaseRole) : Bool :=
  state.roleInRegion left &&
    state.roleInRegion right &&
    decide (IsTrackedColor (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2 (state.roleColor left).toColor) &&
    decide (IsTrackedColor (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2 (state.roleColor right).toColor) &&
    SourceLocalLayerBoundaryRebaseTrackedFiniteClosureBool code pair
      (code.point (sourceLocalLayerBoundaryRebaseRoleEquivFin left))
      (code.point (sourceLocalLayerBoundaryRebaseRoleEquivFin right))

/-- Executable support condition for one complete rebase letter.  The facial
condition says that every live output row has a collar coordinate and that
those coordinates represent exactly the row equality partition.  Ambient-face
continuation remains a distinct stored profile field, as required by the
source. -/
def SourceLocalLayerBoundaryRebaseFiniteSupportsBool
    (letter : SourceLocalLayerBoundaryRebaseFiniteBoolSupportLetter) : Bool :=
  decide
    (letter.output = letter.outputCode.outputProfile ∧
      (∀ pair left right,
        SourceLocalLayerBoundaryRebaseTrackedConnectedBool
            letter.outputCode.tracked pair left right =
          SourceLocalLayerBoundaryRebaseTrackedClosureConnectedBool
            letter.outputCode.tracked letter.trackedCode pair left right) ∧
      (∀ fragment : Fin letter.outputCode.outputCount.val,
        letter.outputCode.facial.fragmentOccupied
            (letter.outputCode.outputFaceSlot fragment) = true ∧
          ∃ coordinate :
              Fin letter.outputCode.facial.collarCode.vertexCount.val,
            letter.outputCode.facial.fragmentCoordinate
                (letter.outputCode.outputFaceSlot fragment) =
              some coordinate) ∧
      (∀ left right : Fin letter.outputCode.outputCount.val,
        ∃ leftCoordinate rightCoordinate :
            Fin letter.outputCode.facial.collarCode.vertexCount.val,
          letter.outputCode.facial.fragmentCoordinate
              (letter.outputCode.outputFaceSlot left) =
              some leftCoordinate ∧
          letter.outputCode.facial.fragmentCoordinate
              (letter.outputCode.outputFaceSlot right) =
              some rightCoordinate ∧
          (SourceLocalLayerBoundaryRebaseFaceFiniteClosureBool
              letter.outputCode.facial.collarCode
              leftCoordinate rightCoordinate = true ↔
            left = right)))

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialBoundaryRebaseFiniteBoolSupportLetterEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Extract the complete finite letter of one actual source rebase. -/
noncomputable def sourceLocalLayerBoundaryRebaseFiniteBoolSupportLetterAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerBoundaryRebaseFiniteBoolSupportLetter where
  input :=
    sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt corridor hunique offset
  output :=
    sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext)
  trackedCode :=
    ofGraphFamilyCode
      (sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt corridor hunique offset
        hnext)
  outputCode :=
    sourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCodeAt corridor hunique
      offset hnext

private theorem sourceLocalLayerBoundaryRebaseTrackedCollarPointAt_role
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (role : SourceLocalLayerBoundaryRebaseRole) :
    (ofGraphFamilyCode
      (sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt corridor hunique offset
        hnext)).point
        (sourceLocalLayerBoundaryRebaseRoleEquivFin role) =
      carrierCoordinate
        (sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset
          hnext)
        ⟨sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role,
          by
            apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ _).2
            exact Or.inl
              ((mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff corridor hunique
                offset hnext _).2 ⟨role, rfl⟩)⟩ := by
  change
    carrierCoordinate
        (sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset
          hnext)
        (sourceLocalLayerBoundaryRebaseTrackedCollarPointAt corridor hunique
          offset hnext (sourceLocalLayerBoundaryRebaseRoleEquivFin role)) =
      _
  apply congrArg
  apply Subtype.ext
  simp [sourceLocalLayerBoundaryRebaseTrackedCollarPointAt]

/-- Every actual literal source rebase satisfies the executable support
condition.  This is the source-sound direction for the later heterogeneous
reachable closure. -/
theorem sourceLocalLayerBoundaryRebaseFiniteBoolSupportLetterAt_supports
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerBoundaryRebaseFiniteSupportsBool
      (sourceLocalLayerBoundaryRebaseFiniteBoolSupportLetterAt corridor hunique
        offset hnext) = true := by
  rw [SourceLocalLayerBoundaryRebaseFiniteSupportsBool, decide_eq_true_eq]
  dsimp only [sourceLocalLayerBoundaryRebaseFiniteBoolSupportLetterAt]
  refine ⟨
    sourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCodeAt_outputProfile_eq
      corridor hunique offset hnext |>.symm, ?_, ?_, ?_⟩
  · intro pair left right
    apply Bool.eq_iff_iff.mpr
    simp only [trackedConnectedBool_eq_true_iff,
      SourceLocalLayerBoundaryRebaseTrackedClosureConnectedBool,
      Bool.and_eq_true, decide_eq_true_eq]
    rw [sourceLocalLayerBoundaryRebaseTrackedCollarPointAt_role,
      sourceLocalLayerBoundaryRebaseTrackedCollarPointAt_role,
      sourceLocalLayerBoundaryRebaseTrackedFiniteClosureBoolAt_eq_true_iff]
    dsimp only [
      sourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCodeAt,
      ofFiniteOutputLetterCode,
      sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt,
      sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt]
    rw [
      sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt_connected_iff,
      regionalTrackedConnectivity_eq_true_iff]
    simp only [decide_eq_true_eq, strandColorOfNonzero_toColor,
      sourceLocalLayerBoundaryRebaseSuccessorTrackedGraphAt,
      sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt]
    simp only [and_assoc]
  · intro fragment
    let actual :=
      sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor hunique
        offset hnext fragment
    refine ⟨?_, ?_⟩
    · change
        (sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt corridor hunique offset
          hnext).fragmentOccupied
            ((sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt corridor
              hunique offset hnext).outputFaceSlot fragment) = true
      have hslot :
          (sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt corridor hunique
            offset hnext).outputFaceSlot fragment =
            sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
              hunique offset hnext actual := by
        rw [sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt_index]
        apply Fin.ext
        rfl
      rw [hslot]
      exact sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_fragmentOccupied
        corridor hunique offset hnext actual
    · refine ⟨
        sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentCoordinateAt corridor
          hunique offset hnext actual, ?_⟩
      change
        (sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt corridor hunique offset
          hnext).fragmentCoordinate
            ((sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt corridor
              hunique offset hnext).outputFaceSlot fragment) =
          some _
      have hslot :
          (sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt corridor hunique
            offset hnext).outputFaceSlot fragment =
            sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
              hunique offset hnext actual := by
        rw [sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt_index]
        apply Fin.ext
        rfl
      rw [hslot]
      exact sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_fragmentCoordinate
        corridor hunique offset hnext actual
  · intro left right
    let leftActual :=
      sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor hunique
        offset hnext left
    let rightActual :=
      sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor hunique
        offset hnext right
    refine ⟨
      sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentCoordinateAt corridor
        hunique offset hnext leftActual,
      sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentCoordinateAt corridor
        hunique offset hnext rightActual, ?_, ?_, ?_⟩
    · change
        (sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt corridor hunique offset
          hnext).fragmentCoordinate
            ((sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt corridor
              hunique offset hnext).outputFaceSlot left) =
          some _
      have hslot :
          (sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt corridor hunique
            offset hnext).outputFaceSlot left =
            sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
              hunique offset hnext leftActual := by
        rw [sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt_index]
        apply Fin.ext
        rfl
      rw [hslot]
      exact sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_fragmentCoordinate
        corridor hunique offset hnext leftActual
    · change
        (sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt corridor hunique offset
          hnext).fragmentCoordinate
            ((sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt corridor
              hunique offset hnext).outputFaceSlot right) =
          some _
      have hslot :
          (sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt corridor hunique
            offset hnext).outputFaceSlot right =
            sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
              hunique offset hnext rightActual := by
        rw [sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt_index]
        apply Fin.ext
        rfl
      rw [hslot]
      exact sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_fragmentCoordinate
        corridor hunique offset hnext rightActual
    · rw [
        sourceLocalLayerBoundaryRebaseFiniteBoolFaceReceiptAt_fragmentClosure_iff_eq]
      exact (Fintype.equivFin
        (SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor hunique
          offset hnext)).symm.injective.eq_iff

end

end GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolSupportLetter

end Mettapedia.GraphTheory.FourColor
