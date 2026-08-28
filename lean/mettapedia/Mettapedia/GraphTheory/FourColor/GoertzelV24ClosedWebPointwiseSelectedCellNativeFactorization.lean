import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedRootedInteractionState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedCellFiniteSupportLetter

/-!
# Prefix-independent native factors for a selected literal Cell

The pointwise-selected finite support letter is proof-facing: its tracked
graph table has already combined the cumulative-prefix colours with the
literal Cell colours.  The executable rolling machine instead consumes a
physical Cell factor which stores only uncoloured local geometry and the Cell
colour table.

This file proves the exact factorization.  Recombining the selected rooted
prefix with the extracted physical factor is literally the Boolean reflection
of the original selected support letter.  Thus the local alphabet carries no
hidden dependency on the prefix from which it was observed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedCellNativeFactorization

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteBoolSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteColorCompatibility
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteTrackedBoolColorCode
open GoertzelV24ClosedWebLocalLayerSerialCellNativeFactorization
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24ClosedWebPointwiseSelectedCellFiniteSupportLetter
open GoertzelV24ClosedWebPointwiseSelectedRootedInteractionState
open GoertzelV24CorridorProfile
open GoertzelV24HexSlabConnectivityProfile

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedCellNativeFactorizationEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The physical, prefix-independent local factor extracted from one selected
literal Cell.  The dependent output count is the one already certified by the
proof-facing selected letter. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolLocalFactorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor : G.edgeSet → Color)
    (hprefix : ∀ step,
      prefixColor (pointwiseSelectedSourceLocalLayerLeftCrossingAt
        web.toFormation corridor hinterior offset step) ≠ 0)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset) :
    let letter :=
      pointwiseSelectedSourceLocalLayerSerialCellFiniteSupportLetterAt web.toFormation
        corridor hinterior offset hcell prefixColor hprefix cellColoring
    SourceLocalLayerSerialCellPhysicalBoolLocalFactor
      letter.output.faceFragmentCount := by
  let letter :=
    pointwiseSelectedSourceLocalLayerSerialCellFiniteSupportLetterAt web.toFormation
      corridor hinterior offset hcell prefixColor hprefix cellColoring
  let cellColor := pointwiseSelectedSourceLocalLayerCellLiteralColorAt
    web.toFormation corridor hinterior offset cellColoring
  exact {
    outputColor := letter.outputColor
    trackedGeometry := ofGraphFamilyCode
      (pointwiseSelectedSourceLocalLayerSerialTrackedGeometryCodeAt web.toFormation corridor
        hinterior offset hcell)
    trackedCellColor :=
      pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt web.toFormation
        corridor hinterior offset
          (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
            corridor hinterior offset) cellColor
    trackedOutputSlot := letter.trackedOutputSlot
    faceCode := ofGraphFamilyCode letter.faceCode
    faceEdgeState := letter.faceEdgeState
    faceOutputSlot := letter.faceOutputSlot
    facePortSlot := letter.facePortSlot
    faceRole := letter.faceRole }

/-- The selected rooted prefix, certified output, and physical local factor
as one graph-free factored letter. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor : G.edgeSet → Color)
    (hprefix : ∀ step,
      prefixColor (pointwiseSelectedSourceLocalLayerLeftCrossingAt
        web.toFormation corridor hinterior offset step) ≠ 0)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset) :
    SourceLocalLayerSerialCellPhysicalBoolFactoredLetter := by
  let root :=
    pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt web.toFormation
      corridor hinterior offset hnext hcell prefixColor hprefix
  let letter :=
    pointwiseSelectedSourceLocalLayerSerialCellFiniteSupportLetterAt web.toFormation
      corridor hinterior offset hcell prefixColor hprefix cellColoring
  exact ⟨root.toSourceLocalLayerSerialColoredCumulativeState, letter.output,
    pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolLocalFactorAt web
      corridor hinterior offset hcell prefixColor hprefix cellColoring⟩

/-- Native recombination is exactly the Boolean reflection of the selected
proof-facing Cell receipt. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt_reassembles
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor : G.edgeSet → Color)
    (hprefix : ∀ step,
      prefixColor (pointwiseSelectedSourceLocalLayerLeftCrossingAt
        web.toFormation corridor hinterior offset step) ≠ 0)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset) :
    let factored :=
      pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring
    reassemblePhysicalBoolSupportLetter factored.1 factored.2.1 factored.2.2 =
      ofFiniteSupportLetter
        (pointwiseSelectedSourceLocalLayerSerialCellFiniteSupportLetterAt web.toFormation
          corridor hinterior offset hcell prefixColor hprefix cellColoring) := by
  dsimp only
    [pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt,
      pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolLocalFactorAt,
      reassemblePhysicalBoolSupportLetter]
  rw [sourceLocalLayerSerialTrackedBoolCodeOfNativeGeometry_eq_reflection]
  rfl

/-- Every compatible arbitrary prefix and positive selected literal Cell
passes the executable physical support test. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt_supports
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor : G.edgeSet → Color)
    (hprefix : ∀ step,
      prefixColor (pointwiseSelectedSourceLocalLayerLeftCrossingAt
        web.toFormation corridor hinterior offset step) ≠ 0)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset)
    (hcompatible :
      PointwiseSelectedSourceLocalLayerSerialTerminalCellColorsCompatibleAt
        web.toFormation corridor hinterior offset prefixColor
          (pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
            corridor hinterior offset cellColoring)) :
    let factored :=
      pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt
        web corridor hinterior offset hnext hcell prefixColor hprefix
          cellColoring
    SourceLocalLayerSerialCellPhysicalSupportsBool factored.1 factored.2.1
      factored.2.2 = true := by
  dsimp only [SourceLocalLayerSerialCellPhysicalSupportsBool]
  rw [Bool.and_eq_true]
  constructor
  · rw [sourceLocalLayerSerialCarrierColorsCompatibleBool_eq_true_iff]
    exact
      (pointwiseSelectedSourceLocalLayerSerialCarrierColorsCompatible_iff web.toFormation
        corridor hinterior offset hcell prefixColor
          (pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
            corridor hinterior offset cellColoring)).2 hcompatible
  · rw [pointwiseSelectedSourceLocalLayerSerialCellPhysicalBoolFactoredLetterAt_reassembles,
      finiteSupportsBool_ofFiniteSupportLetter_eq_true_iff]
    exact
      pointwiseSelectedSourceLocalLayerSerialCellFiniteSupportLetterAt_supports
        web.toFormation corridor hinterior offset hcell prefixColor hprefix cellColoring
          hcompatible

end

end GoertzelV24ClosedWebPointwiseSelectedCellNativeFactorization

end Mettapedia.GraphTheory.FourColor
