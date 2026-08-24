import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteOutputDecoder

/-!
# An executable five-field output for one literal boundary rebase

The finite boundary-rebase output decoder already stores Boolean tables for
every facial coordinate.  Its tracked coordinate was still decoded through a
proposition-valued residual-connectivity relation.  Here the persistent-port
type is empty, so that relation is exactly the stored residual Boolean bit.

This module reflects that final proposition and defines a native Boolean
successor profile.  It is the executable output half of the rebase letter;
the predecessor-to-successor recurrence remains a separate obligation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolOutput

open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24SimpleGraphPortResidualFactorContraction
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open GoertzelV24WindingClassification
open SimpleGraphDartRotation

/-- Native Boolean interpretation of one tracked successor bit.  The rebase
state has no persistent ports, so the residual matrix is the complete
connectivity witness after the explicit colour and activity guards. -/
def SourceLocalLayerBoundaryRebaseTrackedConnectedBool
    (state : SourceLocalLayerBoundaryRebaseTrackedState)
    (pair : TrackedColorPair)
    (left right : SourceLocalLayerBoundaryRebaseRole) : Bool :=
  state.roleInRegion left &&
    state.roleInRegion right &&
    decide (IsTrackedColor (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2 (state.roleColor left).toColor) &&
    decide (IsTrackedColor (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2 (state.roleColor right).toColor) &&
    (state.trackedResidual pair).residualConnected left right

/-- The native tracked query is exact for the earlier proof-facing
interpretation. -/
@[simp]
theorem trackedConnectedBool_eq_true_iff
    (state : SourceLocalLayerBoundaryRebaseTrackedState)
    (pair : TrackedColorPair)
    (left right : SourceLocalLayerBoundaryRebaseRole) :
    SourceLocalLayerBoundaryRebaseTrackedConnectedBool state pair left right =
        true ↔
      state.connected pair left right := by
  simp [SourceLocalLayerBoundaryRebaseTrackedConnectedBool,
    SourceLocalLayerBoundaryRebaseTrackedState.connected,
    SupportedPortResidualFactoredReachability,
    PortResidualFactoredReachability, and_assoc]

/-- Decode the complete terminal-aware successor using only native Boolean
queries. -/
def sourceLocalLayerBoundaryRebaseFiniteOutputProfileBool
    (code : SourceLocalLayerBoundaryRebaseFiniteOutputLetterCode) :
    GoertzelV24BoundaryProfileFiniteState.BoundedCorridorCutProfile 2 1 4 :=
  {
    faceFragmentCount := code.outputCount
    profile := {
      edgeColor := fun crossing =>
        code.receipt.tracked.roleColor
          (sourceLocalLayerBoundaryRebaseSuccessorPortRole (.inl crossing))
      strandConnected := fun pair left right =>
        SourceLocalLayerBoundaryRebaseTrackedConnectedBool
          code.receipt.tracked pair
          (sourceLocalLayerBoundaryRebaseSuccessorPortRole left)
          (sourceLocalLayerBoundaryRebaseSuccessorPortRole right)
      faceContinues := fun left right =>
        code.receipt.facial.faceContinues
          (code.outputFaceSlot left) (code.outputFaceSlot right)
      fragmentContainsPort := fun fragment port =>
        code.receipt.facial.fragmentContainsPort
          (code.outputFaceSlot fragment) port
      faceLengthCap := fun fragment =>
        code.receipt.facial.faceLengthCap (code.outputFaceSlot fragment) }
  }

/-- Boolean and proof-facing decoders give definitionally the same four
facial coordinates and propositionally the same tracked coordinate. -/
theorem outputProfileBool_eq_outputProfile
    (code : SourceLocalLayerBoundaryRebaseFiniteOutputLetterCode) :
    sourceLocalLayerBoundaryRebaseFiniteOutputProfileBool code =
      code.outputProfile := by
  simp only [sourceLocalLayerBoundaryRebaseFiniteOutputProfileBool,
    SourceLocalLayerBoundaryRebaseFiniteOutputLetterCode.outputProfile]
  rw [GoertzelV24BoundaryProfileFiniteState.BoundedCorridorCutProfile.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  rw [CorridorCutProfile.mk.injEq]
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  funext pair left right
  apply Bool.eq_iff_iff.mpr
  simp only [trackedConnectedBool_eq_true_iff, decide_eq_true_eq]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialBoundaryRebaseFiniteBoolOutputEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- For every literal source rebase, the native Boolean decoder is exactly
the terminal-aware profile consumed by the next Cell. -/
theorem sourceLocalLayerBoundaryRebaseFiniteOutputProfileBoolAt_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    sourceLocalLayerBoundaryRebaseFiniteOutputProfileBool
        (sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt corridor
          hunique offset hnext) =
      sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) := by
  rw [outputProfileBool_eq_outputProfile]
  exact
    sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt_outputProfile_eq
      corridor hunique offset hnext

end

end GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolOutput

end Mettapedia.GraphTheory.FourColor
