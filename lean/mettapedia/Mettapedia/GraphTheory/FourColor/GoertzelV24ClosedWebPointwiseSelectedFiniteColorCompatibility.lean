import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedTrackedSeamCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedSerialCellCountWitness

/-!
# Exact finite colour compatibility for a pointwise-selected Cell

The terminal-aware cumulative prefix and a positive literal Cell witness may
carry different colour functions.  Their selected transition codes are
compatible exactly when those functions agree on every retained edge in the
literal overlap.

The twenty-one-slot table below is decoded from the pointwise-selected carrier
itself.  It therefore retains the shared rung required by the rooted machine
without reintroducing the historical global shared-edge selector.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFiniteColorCompatibilityEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Formation

/-- Embed a represented selected transition edge into the stable
twenty-one-slot coordinate system. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation
      corridor hinterior offset).card ≤ 6) :
    {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        formation corridor hinterior offset} → Fin 21 :=
  fun edge => Fin.castLE
    (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt_card_le_twentyOne
      formation corridor hinterior offset hcell)
    (carrierCoordinate
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        formation corridor hinterior offset) edge)

/-- Partial inverse of the stable-slot embedding.  Padding slots decode to
`none`. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialTrackedTransitionEdgeAtSlot?
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) : Fin 21 →
      Option {edge // edge ∈
        pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
          formation corridor hinterior offset} :=
  fun slot =>
    if hslot : slot.val <
        (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
          formation corridor hinterior offset).card then
      some ((carrierCoordinate
        (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
          formation corridor hinterior offset)).symm ⟨slot.val, hslot⟩)
    else none

/-- Decoding a represented edge at its own stable slot is exact. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialTrackedTransitionEdgeAtSlot?_slot
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation
      corridor hinterior offset).card ≤ 6)
    (edge : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        formation corridor hinterior offset}) :
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionEdgeAtSlot?
        formation corridor hinterior offset
        (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt formation
          corridor hinterior offset hcell edge) = some edge := by
  simp [pointwiseSelectedSourceLocalLayerSerialTrackedTransitionEdgeAtSlot?,
    pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt]

/-- Partial colour data on the stable selected transition ABI. -/
abbrev PointwiseSelectedSourceLocalLayerSerialCarrierColorCode :=
  Fin 21 → Option Color

/-- Decode the represented edge at a stable slot and record its colour exactly
when it belongs to `region`. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) (region : Finset G.edgeSet)
    (color : G.edgeSet → Color) :
    PointwiseSelectedSourceLocalLayerSerialCarrierColorCode :=
  fun slot =>
    (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionEdgeAtSlot?
      formation corridor hinterior offset slot).bind fun edge =>
        if edge.1 ∈ region then some (color edge.1) else none

/-- A represented edge is read back at its stable slot without loss of
regional activity or colour. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt_slot
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation
      corridor hinterior offset).card ≤ 6)
    (region : Finset G.edgeSet) (color : G.edgeSet → Color)
    (edge : {edge // edge ∈
      pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
        formation corridor hinterior offset}) :
    pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt formation
        corridor hinterior offset region color
        (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt formation
          corridor hinterior offset hcell edge) =
      if edge.1 ∈ region then some (color edge.1) else none := by
  simp [pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt]

/-- Two selected partial colour tables agree at every jointly active slot. -/
def PointwiseSelectedSourceLocalLayerSerialCarrierColorsCompatible
    (oldCode newCode :
      PointwiseSelectedSourceLocalLayerSerialCarrierColorCode) : Prop :=
  ∀ slot prefixColor cellColor,
    oldCode slot = some prefixColor →
    newCode slot = some cellColor →
    prefixColor = cellColor

noncomputable instance
    (oldCode newCode :
      PointwiseSelectedSourceLocalLayerSerialCarrierColorCode) :
    Decidable
      (PointwiseSelectedSourceLocalLayerSerialCarrierColorsCompatible oldCode
        newCode) :=
  Classical.propDecidable _

/-- The finite table test is sound and complete for compatibility on the
actual terminal-aware prefix/Cell overlap. -/
theorem pointwiseSelectedSourceLocalLayerSerialCarrierColorsCompatible_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation
      corridor hinterior offset).card ≤ 6)
    (prefixColor cellColor : G.edgeSet → Color) :
    PointwiseSelectedSourceLocalLayerSerialCarrierColorsCompatible
        (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt
          formation corridor hinterior offset
          (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
            formation corridor hinterior offset) prefixColor)
        (pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt
          formation corridor hinterior offset
          (pointwiseSelectedSourceLocalLayerCellRegionAt formation
            corridor hinterior offset) cellColor) ↔
      PointwiseSelectedSourceLocalLayerSerialTerminalCellColorsCompatibleAt
        formation corridor hinterior offset prefixColor cellColor := by
  constructor
  · intro hfinite edge hprefix hcellMem
    let carrierEdge : {edge // edge ∈
        pointwiseSelectedSourceLocalLayerSerialTrackedTransitionCarrierAt
          formation corridor hinterior offset} :=
      ⟨edge, Finset.mem_union_left _ (Finset.mem_union_left _ hcellMem)⟩
    apply hfinite
      (pointwiseSelectedSourceLocalLayerSerialTrackedTransitionSlotAt formation
        corridor hinterior offset hcell carrierEdge)
      (prefixColor edge) (cellColor edge)
    · simpa [carrierEdge, hprefix] using
        pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt_slot formation
          corridor hinterior offset hcell
          (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
            formation corridor hinterior offset) prefixColor carrierEdge
    · simpa [carrierEdge, hcellMem] using
        pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt_slot formation
          corridor hinterior offset hcell
          (pointwiseSelectedSourceLocalLayerCellRegionAt formation
            corridor hinterior offset) cellColor carrierEdge
  · intro hactual slot prefixColorValue cellColorValue hprefix hcellCode
    unfold pointwiseSelectedSourceLocalLayerSerialCarrierColorCodeAt at hprefix hcellCode
    cases hdecode :
        pointwiseSelectedSourceLocalLayerSerialTrackedTransitionEdgeAtSlot?
          formation corridor hinterior offset slot with
    | none => simp [hdecode] at hprefix
    | some edge =>
        simp only [hdecode, Option.bind_some] at hprefix hcellCode
        split at hprefix <;> rename_i hprefixMem
        · simp only [Option.some.injEq] at hprefix
          split at hcellCode <;> rename_i hcellMem
          · simp only [Option.some.injEq] at hcellCode
            exact hprefix.symm.trans
              ((hactual _ hprefixMem hcellMem).trans hcellCode)
          · simp at hcellCode
        · simp at hprefix

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
