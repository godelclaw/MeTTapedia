import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedFaceOldSlot
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedFaceValidity

/-!
# Executable boundary queries on the expanded facial receipt

The fixed facial receipt distinguishes three different situations which must
not be conflated during interface enlargement: inactive padding, an occurrence
already represented by the rolling predecessor carrier, and a genuinely new
present occurrence.  This file makes the last case executable and separately
searches for a direct facial neighbour in the old carrier.

On a literal source receipt both searches have exact ambient-graph meanings.
No global boundary-locality assertion is made here: the final theorem reduces
that geometric question to one finite Boolean implication on the receipt.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellRebaseExpandedFaceBoundaryEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- A present occurrence which is not an alias of any old rolling coordinate
is genuinely promoted by the expanded facial interface. -/
def SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.promoted
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface) : Bool :=
  state.preRebasePresent occurrence && !(state.oldSlot? occurrence).isSome

/-- Search the old rolling coordinates for one directly adjacent to the
requested expanded occurrence in the pre-rebase facial graph. -/
def SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldNeighbor?
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface) :
    Option (Fin 24) :=
  Fin.find? fun oldSlot => state.directAdj (.inl oldSlot) occurrence

/-- A returned old neighbour satisfies the receipt's direct-adjacency row. -/
theorem SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldNeighbor?_sound
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (oldSlot : Fin 24)
    (hslot : state.oldNeighbor? occurrence = some oldSlot) :
    state.directAdj (.inl oldSlot) occurrence = true := by
  exact Fin.eq_true_of_find?_eq_some hslot

/-- Finite old-neighbour search succeeds exactly when an old coordinate has
the requested direct-adjacency bit. -/
theorem SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldNeighbor?_isSome_iff
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface) :
    (state.oldNeighbor? occurrence).isSome ↔
      ∃ oldSlot : Fin 24,
        state.directAdj (.inl oldSlot) occurrence = true := by
  exact Fin.isSome_find?_iff

/-- On a literal source receipt, the promoted bit says exactly that the
decoded dart is regionally present but absent from the old rolling carrier. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_promoted_iff_of_decode
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
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).promoted occurrence = true ↔
      web.annular.RS.edgeOf dart ∈
          sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset ∧
        dart ∉ sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
          offset := by
  rw [SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.promoted,
    Bool.and_eq_true]
  rw [sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_preRebasePresent_iff_of_decode
    corridor hunique offset hnext hcell occurrence dart hdecode]
  have hold :=
    sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldSlot?_isSome_iff_mem
      corridor hunique offset hnext hcell occurrence dart hdecode
  constructor
  · rintro ⟨hpresent, hnotOld⟩
    refine ⟨hpresent, ?_⟩
    intro hdart
    have hisSome := hold.2 hdart
    simp [hisSome] at hnotOld
  · rintro ⟨hpresent, hnew⟩
    refine ⟨hpresent, ?_⟩
    have hnotSome :
        ((sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
          hunique offset hnext hcell).oldSlot? occurrence).isSome = false := by
      apply Bool.eq_false_iff.mpr
      intro hisSome
      exact hnew (hold.1 hisSome)
    simp [hnotSome]

/-- On a literal source receipt, finite old-neighbour search recognizes
exactly adjacency to some dart of the rolling predecessor carrier. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldNeighbor?_isSome_iff_of_decode
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
        hunique offset hnext hcell).oldNeighbor? occurrence).isSome ↔
      ∃ oldDart : {dart // dart ∈
          sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset},
        (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
            offset)).Adj oldDart.1 dart := by
  classical
  let state := sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt
    corridor hunique offset hnext hcell
  rw [SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldNeighbor?_isSome_iff]
  constructor
  · rintro ⟨oldSlot, hadj⟩
    have hpresent :=
      sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_present_of_directAdj
        corridor hunique offset hnext hcell (.inl oldSlot) occurrence hadj
    have hoccupied :=
      sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_occupied_of_present
        corridor hunique offset hnext hcell (.inl oldSlot) hpresent.1
    rcases
        (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_occupied_iff
          corridor hunique offset hnext hcell (.inl oldSlot)).1 hoccupied with
      ⟨oldAmbientDart, holdDecode⟩
    unfold sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? at holdDecode
    cases hsource : sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor
        hunique offset hcell oldSlot with
    | none => simp [hsource] at holdDecode
    | some oldDart =>
        simp only [hsource, Option.map_some, Option.some.injEq] at holdDecode
        refine ⟨oldDart, ?_⟩
        apply
          (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_directAdj_iff_of_decode
            corridor hunique offset hnext hcell (.inl oldSlot) occurrence
              oldDart.1 dart ?_ hdecode).1 hadj
        simp [sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot?, hsource]
  · rintro ⟨oldDart, hadj⟩
    let oldSlot := sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique
      offset hcell oldDart
    refine ⟨oldSlot, ?_⟩
    apply
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_directAdj_iff_of_decode
        corridor hunique offset hnext hcell (.inl oldSlot) occurrence
          oldDart.1 dart ?_ hdecode).2 hadj
    simp [oldSlot]

/-- The exact source boundary-locality obligation is a finite implication on
the fixed receipt: every genuinely promoted occurrence has an old neighbour.
This theorem is an equivalence, not an assumption of the geometric side. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_boundaryLocal_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    (∀ occurrence,
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
          hunique offset hnext hcell).promoted occurrence = true →
        ((sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
          hunique offset hnext hcell).oldNeighbor? occurrence).isSome) ↔
      ∀ occurrence dart,
        sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor
            hunique offset hnext hcell occurrence = some dart →
        web.annular.RS.edgeOf dart ∈
            sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
              offset →
        dart ∉ sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset →
        ∃ oldDart : {dart // dart ∈
            sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
              offset},
          (faceRegionalDartGraph web.annular.RS
            (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
              offset)).Adj oldDart.1 dart := by
  constructor
  · intro hfinite occurrence dart hdecode hpresent hnew
    have hpromoted :=
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_promoted_iff_of_decode
        corridor hunique offset hnext hcell occurrence dart hdecode).2
        ⟨hpresent, hnew⟩
    exact
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldNeighbor?_isSome_iff_of_decode
        corridor hunique offset hnext hcell occurrence dart hdecode).1
        (hfinite occurrence hpromoted)
  · intro hambient occurrence hpromoted
    have hoccupied :=
      sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_occupied_of_present
        corridor hunique offset hnext hcell occurrence
        (Bool.and_eq_true_iff.mp hpromoted).1
    rcases
        (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_occupied_iff
          corridor hunique offset hnext hcell occurrence).1 hoccupied with
      ⟨dart, hdecode⟩
    have hsemantic :=
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_promoted_iff_of_decode
        corridor hunique offset hnext hcell occurrence dart hdecode).1 hpromoted
    apply
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldNeighbor?_isSome_iff_of_decode
        corridor hunique offset hnext hcell occurrence dart hdecode).2
    exact hambient occurrence dart hdecode hsemantic.1 hsemantic.2

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
