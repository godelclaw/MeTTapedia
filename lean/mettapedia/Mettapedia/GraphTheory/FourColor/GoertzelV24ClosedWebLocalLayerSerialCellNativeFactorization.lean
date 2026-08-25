import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedBoolColorCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellSplicedFiniteSupportLetter
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellStateFactorization

/-!
# A prefix-independent native Cell factor

The earlier factored finite letter separated the cumulative prefix fields from
the local Cell fields, but its tracked graph table was still specialized to
the colours of that particular prefix.  Such a record is finite yet cannot be
used as a pumpable physical alphabet.

This file makes the remaining dependency explicit.  The cumulative state
stores the prefix partial-colour table.  A physical Cell factor stores only
uncoloured local geometry and the Cell partial-colour table.  The executable
transition reconstructs both tracked Cell graphs and the residual seam from
those two inputs, and rejects incompatible partial tables.

For every literal compatible prefix/Cell splice, native reconstruction is
exactly the Boolean reflection of the already-proved five-field support
letter.  This is representation factorization for the source's Phase-5
transfer construction.  It neither computes a reachable closure nor revives
the refuted good-word closed-web obstruction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization

open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellColorSplice
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteAmbientContinuation
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteBoolSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedBoolColorCode
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedColorCode
open GoertzelV24ClosedWebLocalLayerSerialCellSplicedFiniteSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialCellStateFactorization
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedTransitionCarrier
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open GoertzelV24WindingClassification
open SimpleGraphDartRotation

/-- Native reconstruction is literally the Boolean reflection of the
proof-facing finite-colour reconstruction, not merely graph-equivalent to it.
This identity lets all existing reflected closure theorems be reused. -/
theorem sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry_eq_reflection
    (geometry : BoundedCarrierGraphFamilyCode 21 5 Unit)
    (oldCode cellCode : SourceLocalLayerSerialCarrierColorCode) :
    sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry
        (ofGraphFamilyCode geometry) oldCode cellCode =
      ofGraphFamilyCode
        (sourceLocalLayerSerialTrackedCodeOfFiniteColors geometry oldCode
          cellCode) := by
  classical
  cases geometry with
  | mk vertexCount point graph =>
    unfold sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry
      sourceLocalLayerSerialTrackedCodeOfFiniteColors ofGraphFamilyCode
    simp only [BoundedCarrierBoolGraphFamilyCode.mk.injEq]
    refine ⟨trivial, HEq.rfl, ?_⟩
    apply heq_of_eq
    funext factor first second
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    exact
      sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry_adjacency_eq_true_iff
        ({ vertexCount := vertexCount, point := point, graph := graph }) oldCode
          cellCode factor first second

/-- The cumulative prefix state together with the exact partial colour table
on the stable twenty-one-slot transition carrier. -/
structure SourceLocalLayerSerialColoredCumulativeState extends
    SourceLocalLayerSerialCumulativeState where
  colorCode : SourceLocalLayerSerialCarrierColorCode

noncomputable instance :
    DecidableEq SourceLocalLayerSerialColoredCumulativeState :=
  Classical.decEq _

private def sourceLocalLayerSerialColoredCumulativeStateEquiv :
    SourceLocalLayerSerialColoredCumulativeState ≃
      SourceLocalLayerSerialCumulativeState ×
        SourceLocalLayerSerialCarrierColorCode where
  toFun state := ⟨state.toSourceLocalLayerSerialCumulativeState,
    state.colorCode⟩
  invFun data := {
    toSourceLocalLayerSerialCumulativeState := data.1
    colorCode := data.2 }
  left_inv state := by cases state; rfl
  right_inv data := by cases data; rfl

noncomputable instance :
    Fintype SourceLocalLayerSerialColoredCumulativeState :=
  Fintype.ofEquiv _ sourceLocalLayerSerialColoredCumulativeStateEquiv.symm

/-- A genuinely prefix-independent physical Cell factor.  Its tracked datum
is uncoloured geometry plus the Cell colour table; the residual seam is
computed only when this factor is applied to a cumulative state. -/
structure SourceLocalLayerSerialCellPhysicalBoolLocalFactor
    (outputCount : Fin 5) where
  outputColor : Fin 2 → StrandColor
  trackedGeometry : BoundedCarrierBoolGraphFamilyCode 21 5 Unit
  trackedCellColor : SourceLocalLayerSerialCarrierColorCode
  trackedOutputSlot : Fin 2 → Fin 21
  faceCode : BoundedCarrierBoolGraphFamilyCode 24 0 Bool
  faceEdgeState : SourceLocalLayerSerialFaceFiniteEdgeState
  faceOutputSlot : Fin outputCount.val → Fin 24
  facePortSlot : Fin 2 → Fin 2 → Fin 24
  faceRole : Fin outputCount.val → SourceLocalLayerSerialOutputFaceRole

noncomputable instance (outputCount : Fin 5) :
    DecidableEq
      (SourceLocalLayerSerialCellPhysicalBoolLocalFactor outputCount) :=
  Classical.decEq _

private abbrev sourceLocalLayerSerialCellPhysicalBoolLocalFactorCode
    (outputCount : Fin 5) :=
  (Fin 2 → StrandColor) ×
    BoundedCarrierBoolGraphFamilyCode 21 5 Unit ×
    SourceLocalLayerSerialCarrierColorCode ×
    (Fin 2 → Fin 21) ×
    BoundedCarrierBoolGraphFamilyCode 24 0 Bool ×
    SourceLocalLayerSerialFaceFiniteEdgeState ×
    (Fin outputCount.val → Fin 24) ×
    (Fin 2 → Fin 2 → Fin 24) ×
    (Fin outputCount.val → SourceLocalLayerSerialOutputFaceRole)

private def sourceLocalLayerSerialCellPhysicalBoolLocalFactorEquiv
    (outputCount : Fin 5) :
    SourceLocalLayerSerialCellPhysicalBoolLocalFactor outputCount ≃
      sourceLocalLayerSerialCellPhysicalBoolLocalFactorCode outputCount where
  toFun factor := ⟨factor.outputColor, factor.trackedGeometry,
    factor.trackedCellColor, factor.trackedOutputSlot, factor.faceCode,
    factor.faceEdgeState, factor.faceOutputSlot, factor.facePortSlot,
    factor.faceRole⟩
  invFun data := by
    rcases data with ⟨outputColor, trackedGeometry, trackedCellColor,
      trackedOutputSlot, faceCode, faceEdgeState, faceOutputSlot, facePortSlot,
      faceRole⟩
    exact {
      outputColor := outputColor
      trackedGeometry := trackedGeometry
      trackedCellColor := trackedCellColor
      trackedOutputSlot := trackedOutputSlot
      faceCode := faceCode
      faceEdgeState := faceEdgeState
      faceOutputSlot := faceOutputSlot
      facePortSlot := facePortSlot
      faceRole := faceRole }
  left_inv factor := by cases factor; rfl
  right_inv data := by
    rcases data with ⟨outputColor, trackedGeometry, trackedCellColor,
      trackedOutputSlot, faceCode, faceEdgeState, faceOutputSlot, facePortSlot,
      faceRole⟩
    rfl

noncomputable instance (outputCount : Fin 5) : Fintype
    (SourceLocalLayerSerialCellPhysicalBoolLocalFactor outputCount) :=
  Fintype.ofEquiv _
    (sourceLocalLayerSerialCellPhysicalBoolLocalFactorEquiv outputCount).symm

/-- A state, candidate output, and one physical Cell factor. -/
abbrev SourceLocalLayerSerialCellPhysicalBoolFactoredLetter :=
  SourceLocalLayerSerialColoredCumulativeState ×
    Σ output : BoundedCorridorCutProfile 2 0 4,
      SourceLocalLayerSerialCellPhysicalBoolLocalFactor
        output.faceFragmentCount

/-- Apply one physical Cell factor to a cumulative state.  The tracked graph
table is reconstructed at this point, so it cannot carry a hidden dependency
on the prefix from which the Cell was originally observed. -/
def reassemblePhysicalBoolSupportLetter
    (state : SourceLocalLayerSerialColoredCumulativeState)
    (output : BoundedCorridorCutProfile 2 0 4)
    (localFactor : SourceLocalLayerSerialCellPhysicalBoolLocalFactor
      output.faceFragmentCount) :
    SourceLocalLayerSerialCellFiniteBoolSupportLetter where
  input := state.input
  output := output
  outputColor := localFactor.outputColor
  trackedState := state.tracked
  trackedCode := sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry
    localFactor.trackedGeometry state.colorCode localFactor.trackedCellColor
  trackedOutputSlot := localFactor.trackedOutputSlot
  faceState := state.face
  faceCode := localFactor.faceCode
  faceEdgeState := localFactor.faceEdgeState
  faceOutputSlot := localFactor.faceOutputSlot
  facePortSlot := localFactor.facePortSlot
  faceRole := localFactor.faceRole

/-- Executable transition test for a physical Cell.  Compatibility is a
separate conjunct because graph reachability cannot detect a colour mismatch
at an isolated overlap slot. -/
def SourceLocalLayerSerialCellPhysicalSupportsBool
    (state : SourceLocalLayerSerialColoredCumulativeState)
    (output : BoundedCorridorCutProfile 2 0 4)
    (localFactor : SourceLocalLayerSerialCellPhysicalBoolLocalFactor
      output.faceFragmentCount) : Bool :=
  SourceLocalLayerSerialCarrierColorsCompatibleBool state.colorCode
      localFactor.trackedCellColor &&
    SourceLocalLayerSerialCellFiniteSupportsBool
      (reassemblePhysicalBoolSupportLetter state output localFactor)

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance nativeFactorizationOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- At literal source data, finite-colour reconstruction is exactly the
formerly stored proof-facing transition code, including carrier and named
point coordinates. -/
theorem sourceLocalLayerSerialTrackedCodeOfFiniteColorsAt_eq
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color) :
    sourceLocalLayerSerialTrackedCodeOfFiniteColors
      (sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
        coloring web corridor hunique offset)
      (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique offset
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        coloring)
      (sourceLocalLayerSerialCarrierColorCodeAt graphData caps coloring web
        corridor hunique offset
        (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor) =
      sourceLocalLayerSerialTrackedTransitionCodeForColorAt graphData minimal
        caps coloring web corridor hunique offset
        (sourceLocalLayerSerialCellSplicedColorAt corridor hunique offset
          coloring cellColor) := by
  rw [BoundedCarrierGraphFamilyCode.mk.injEq]
  refine ⟨rfl, HEq.rfl, ?_⟩
  apply heq_of_eq
  funext factor
  exact sourceLocalLayerSerialTrackedCodeOfFiniteColorsAt_graph_eq graphData
    minimal caps coloring web corridor hunique offset cellColor factor

/-- The exact state/output/physical-Cell factor extracted from one compatible
literal source Cell. -/
noncomputable def sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0) :
    SourceLocalLayerSerialCellPhysicalBoolFactoredLetter := by
  let letter := sourceLocalLayerSerialSplicedCellFiniteSupportLetterAt graphData
    minimal caps coloring web corridor hunique offset cellColor hcellColor
  exact ⟨{
      input := letter.input
      tracked := letter.trackedState
      face := letter.faceState
      colorCode := sourceLocalLayerSerialCarrierColorCodeAt graphData caps
        coloring web corridor hunique offset
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        coloring
    }, letter.output, {
      outputColor := letter.outputColor
      trackedGeometry := ofGraphFamilyCode
        (sourceLocalLayerSerialTrackedGeometryCodeAt graphData minimal caps
          coloring web corridor hunique offset)
      trackedCellColor := sourceLocalLayerSerialCarrierColorCodeAt graphData caps
        coloring web corridor hunique offset
        (sourceLocalLayerCellRegionAt corridor hunique offset) cellColor
      trackedOutputSlot := letter.trackedOutputSlot
      faceCode := ofGraphFamilyCode letter.faceCode
      faceEdgeState := letter.faceEdgeState
      faceOutputSlot := letter.faceOutputSlot
      facePortSlot := letter.facePortSlot
      faceRole := letter.faceRole
    }⟩

/-- Applying the extracted physical factor to its cumulative state reconstructs
the exact native reflection of the source's five-field spliced letter. -/
theorem sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt_reassembles
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0) :
    let factored := sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
      graphData minimal caps coloring web corridor hunique offset cellColor
        hcellColor
    reassemblePhysicalBoolSupportLetter factored.1 factored.2.1 factored.2.2 =
      ofFiniteSupportLetter
        (sourceLocalLayerSerialSplicedCellFiniteSupportLetterAt graphData minimal
          caps coloring web corridor hunique offset cellColor hcellColor) := by
  dsimp only [sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt,
    reassemblePhysicalBoolSupportLetter]
  rw [sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry_eq_reflection,
    sourceLocalLayerSerialTrackedCodeOfFiniteColorsAt_eq]
  rfl

/-- Every compatible literal prefix/Cell splice satisfies the new physical
transition predicate.  No prefix-specialized seam table is stored in the Cell
factor used by this statement. -/
theorem sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt_supports
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (cellColor :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcompatible : SourceLocalLayerSerialCellColorsCompatibleAt corridor
      hunique offset coloring cellColor)
    (hcellColor : ∀ step,
      cellColor (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠
        0) :
    let factored := sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
      graphData minimal caps coloring web corridor hunique offset cellColor
        hcellColor
    SourceLocalLayerSerialCellPhysicalSupportsBool factored.1 factored.2.1
      factored.2.2 = true := by
  dsimp only [SourceLocalLayerSerialCellPhysicalSupportsBool]
  rw [Bool.and_eq_true]
  constructor
  · rw [sourceLocalLayerSerialCarrierColorsCompatibleBool_eq_true_iff]
    simpa only [sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt] using
      (sourceLocalLayerSerialCarrierColorsCompatible_iff graphData minimal caps
        coloring web corridor hunique offset cellColor).2 hcompatible
  · rw [sourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt_reassembles,
      finiteSupportsBool_ofFiniteSupportLetter_eq_true_iff]
    exact sourceLocalLayerSerialSplicedCellFiniteSupportLetterAt_supports
      graphData minimal caps coloring web corridor hunique offset cellColor
        hcompatible hcellColor

end

end GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization

end Mettapedia.GraphTheory.FourColor
