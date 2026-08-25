import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedFaceSource

/-!
# Recovering predecessor slots from the fixed facial occurrence receipt

The fixed forty-eight-slot facial receipt records literal ambient-dart
equality.  Consequently, the partial map back to the rolling predecessor
carrier is executable from the receipt itself: search the twenty-four old
slots for an occupied equal occurrence.

This file proves that finite search sound and complete on every actual source
receipt.  It does not assume that every occupied collar occurrence is old;
genuinely promoted collar occurrences are correctly returned as `none`.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellRebaseExpandedFaceOldSlotEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- Search the old twenty-four-slot summand for an occupied occurrence equal
to the requested expanded occurrence. -/
def SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldSlot?
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface) :
    Option (Fin 24) :=
  Fin.find? fun oldSlot =>
    state.occupied (.inl oldSlot) &&
      state.vertexEq occurrence (.inl oldSlot)

/-- A slot returned by finite search is occupied and equal to the requested
occurrence according to the receipt. -/
theorem SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldSlot?_sound
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (oldSlot : Fin 24) (hslot : state.oldSlot? occurrence = some oldSlot) :
    state.occupied (.inl oldSlot) = true ∧
      state.vertexEq occurrence (.inl oldSlot) = true := by
  have hfound := Fin.eq_true_of_find?_eq_some hslot
  simpa [SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldSlot?]
    using hfound

/-- On an actual source receipt, a returned old slot decodes to the same
ambient dart as the requested expanded occurrence. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldSlot?_sound
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (dart : web.annular.RS.D)
    (hdecode : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor
      hunique offset hnext hcell occurrence = some dart)
    (oldSlot : Fin 24)
    (hslot :
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).oldSlot? occurrence = some oldSlot) :
    ∃ oldDart : {dart // dart ∈
        sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset},
      sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique offset
          hcell oldSlot = some oldDart ∧
        oldDart.1 = dart := by
  classical
  have hrows :=
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldSlot?_sound
      _ occurrence oldSlot hslot
  have holdOccupied :
      ∃ oldDart,
        sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor hunique
          offset hnext hcell (.inl oldSlot) = some oldDart :=
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_occupied_iff
      corridor hunique offset hnext hcell (.inl oldSlot)).1 hrows.1
  rcases holdOccupied with ⟨oldAmbientDart, holdDecode⟩
  have heq :=
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_vertexEq_iff_of_decode
      corridor hunique offset hnext hcell occurrence (.inl oldSlot) dart
        oldAmbientDart hdecode holdDecode).1 hrows.2
  unfold sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? at holdDecode
  cases hsource : sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor
      hunique offset hcell oldSlot with
  | none => simp [hsource] at holdDecode
  | some oldDart =>
      simp only [hsource, Option.map_some, Option.some.injEq] at holdDecode
      exact ⟨oldDart, rfl, holdDecode.trans heq.symm⟩

/-- Every expanded occurrence which decodes to a predecessor-carrier dart is
found by the finite old-slot search. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldSlot?_isSome_of_old
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (oldDart : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset})
    (hdecode : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor
      hunique offset hnext hcell occurrence = some oldDart.1) :
    ((sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell).oldSlot? occurrence).isSome := by
  classical
  change (Fin.find? fun oldSlot : Fin 24 =>
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell).occupied (.inl oldSlot) &&
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell).vertexEq occurrence (.inl oldSlot)).isSome
  rw [Fin.isSome_find?_iff]
  let oldSlot := sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique
    offset hcell oldDart
  refine ⟨oldSlot, ?_⟩
  apply Bool.and_eq_true_iff.mpr
  constructor
  · rw [sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_occupied_iff]
    exact ⟨oldDart.1, by simp [oldSlot]⟩
  · rw [sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_vertexEq_iff_of_decode
      corridor hunique offset hnext hcell occurrence (.inl oldSlot) oldDart.1
        oldDart.1 hdecode (by simp [oldSlot])]

/-- For an occupied actual occurrence, finite search succeeds exactly when its
ambient dart belongs to the rolling predecessor carrier. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldSlot?_isSome_iff_mem
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (dart : web.annular.RS.D)
    (hdecode : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor
      hunique offset hnext hcell occurrence = some dart) :
    ((sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).oldSlot? occurrence).isSome ↔
      dart ∈ sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        offset := by
  constructor
  · intro hisSome
    rcases Option.isSome_iff_exists.mp hisSome with ⟨oldSlot, hslot⟩
    rcases
      sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldSlot?_sound
        corridor hunique offset hnext hcell occurrence dart hdecode oldSlot
          hslot with
      ⟨oldDart, _holdDecode, heq⟩
    rw [← heq]
    exact oldDart.2
  · intro hdart
    exact
      sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldSlot?_isSome_of_old
        corridor hunique offset hnext hcell occurrence ⟨dart, hdart⟩ hdecode

/-- On an actual source receipt, finite search is exactly the semantic partial
map to the predecessor carrier, transported to its canonical padded slot.
This removes the last choice of representative from the old-coordinate
decoder: aliases in the expanded occurrence presentation all return the same
unique predecessor slot. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldSlot?_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface) :
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).oldSlot? occurrence =
      (sourceLocalLayerSerialCellRebaseExpandedFaceOldSourceAt corridor hunique
        offset hnext hcell occurrence).map fun slot =>
          sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
            hcell
            ((carrierCoordinate
              (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
                offset)).symm slot) := by
  classical
  let state := sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt
    corridor hunique offset hnext hcell
  let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
    hunique offset
  let oldSource := sourceLocalLayerSerialCellRebaseExpandedFaceOldSourceAt
    corridor hunique offset hnext hcell
  change state.oldSlot? occurrence =
    (oldSource occurrence).map fun slot =>
      sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset hcell
        ((carrierCoordinate oldCarrier).symm slot)
  cases hsource : oldSource occurrence with
  | none =>
      simp only [Option.map_none]
      cases hsearch : state.oldSlot? occurrence with
      | none => rfl
      | some slot =>
          exfalso
          have hnone :=
            (sourceLocalLayerSerialCellRebaseExpandedFaceOldSourceAt_eq_none_iff
              corridor hunique offset hnext hcell occurrence).1 hsource
          rcases hnone with hdecodeNone | ⟨dart, hdecode, hdartOutside⟩
          · have hrows :=
              SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldSlot?_sound
                state occurrence slot hsearch
            have holdOccupied :=
              (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_occupied_iff
                corridor hunique offset hnext hcell (.inl slot)).1 hrows.1
            rcases holdOccupied with ⟨oldDart, holdDecode⟩
            have hfalse : False := by
              simpa [state,
                sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt,
                hdecodeNone, holdDecode] using hrows.2
            exact hfalse.elim
          · rcases
              sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldSlot?_sound
                corridor hunique offset hnext hcell occurrence dart hdecode
                  slot hsearch with
              ⟨oldDart, _holdDecode, heq⟩
            exact hdartOutside (heq ▸ oldDart.2)
  | some sourceSlot =>
      let oldDart : {dart // dart ∈ oldCarrier} :=
        (carrierCoordinate oldCarrier).symm sourceSlot
      have hdecode :
          sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor
              hunique offset hnext hcell occurrence = some oldDart.1 := by
        simpa [oldSource, oldCarrier, oldDart] using
          (sourceLocalLayerSerialCellRebaseExpandedFaceOldSourceAt_dart_eq
            corridor hunique offset hnext hcell occurrence sourceSlot hsource)
      have hisSome : (state.oldSlot? occurrence).isSome := by
        exact
          sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldSlot?_isSome_of_old
            corridor hunique offset hnext hcell occurrence oldDart hdecode
      cases hsearch : state.oldSlot? occurrence with
      | none => simp [hsearch] at hisSome
      | some slot =>
          rcases
              sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldSlot?_sound
                corridor hunique offset hnext hcell occurrence oldDart.1
                  hdecode slot hsearch with
            ⟨foundDart, hfoundDecode, heq⟩
          have hfoundEq : foundDart = oldDart := Subtype.ext heq
          subst foundDart
          have hslot : slot =
              sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique
                offset hcell oldDart :=
            (sourceLocalLayerSerialFaceTransitionDartAtSlot?_eq_some_iff
              corridor hunique offset hcell slot oldDart).1 hfoundDecode
          simp only [Option.map_some]
          simpa [oldCarrier, oldDart] using hslot

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
