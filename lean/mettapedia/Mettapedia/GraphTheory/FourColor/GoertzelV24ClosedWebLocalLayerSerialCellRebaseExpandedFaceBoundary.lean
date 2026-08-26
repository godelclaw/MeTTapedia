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

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
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

/-- Search the forty-eight oriented predecessor face incidences for one whose
exterior vertex is the requested expanded occurrence.  The returned index
retains the face side, which `oldNeighbor?` deliberately forgets. -/
def
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldIncidenceIndex?
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface) :
    Option (Fin 48) :=
  Fin.find? fun index => state.oldIncidenceVertexEq index occurrence

/-- A returned old neighbour satisfies the receipt's direct-adjacency row. -/
theorem SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldNeighbor?_sound
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (oldSlot : Fin 24)
    (hslot : state.oldNeighbor? occurrence = some oldSlot) :
    state.directAdj (.inl oldSlot) occurrence = true := by
  exact Fin.eq_true_of_find?_eq_some hslot

/-- A returned oriented incidence satisfies the receipt's literal incidence
vertex-equality row. -/
theorem
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldIncidenceIndex?_sound
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (index : Fin 48)
    (hindex : state.oldIncidenceIndex? occurrence = some index) :
    state.oldIncidenceVertexEq index occurrence = true := by
  exact Fin.eq_true_of_find?_eq_some hindex

/-- Finite old-neighbour search succeeds exactly when an old coordinate has
the requested direct-adjacency bit. -/
theorem SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldNeighbor?_isSome_iff
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface) :
    (state.oldNeighbor? occurrence).isSome ↔
      ∃ oldSlot : Fin 24,
        state.directAdj (.inl oldSlot) occurrence = true := by
  exact Fin.isSome_find?_iff

/-- Oriented predecessor-incidence search succeeds exactly when one row bit is
set. -/
theorem
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldIncidenceIndex?_isSome_iff
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface) :
    (state.oldIncidenceIndex? occurrence).isSome ↔
      ∃ index : Fin 48,
        state.oldIncidenceVertexEq index occurrence = true := by
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

/-- On a literal source receipt, oriented-incidence search succeeds exactly
when one predecessor face incidence has the decoded occurrence as its exterior
vertex.  This is the finite side-sensitive ABI needed by the capped deletion
recurrence. -/
theorem
    sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldIncidenceIndex?_isSome_iff_of_decode
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
        hunique offset hnext hcell).oldIncidenceIndex? occurrence).isSome ↔
      ∃ (index : Fin 48)
        (oldDart : {dart // dart ∈
          sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset}),
        sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique offset
            hcell
            (sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt index).1 =
          some oldDart ∧
        let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
          hunique offset
        let oldDartAt := fun slot : Fin oldCarrier.card =>
          ((carrierCoordinate oldCarrier).symm slot).1
        faceInterfaceIncidenceVertex web.annular.RS oldDartAt
            (carrierCoordinate oldCarrier oldDart,
              (sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt
                index).2) = dart := by
  classical
  rw [SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldIncidenceIndex?_isSome_iff]
  constructor
  · rintro ⟨index, hrow⟩
    cases holdDecode : sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor
        hunique offset hcell
        (sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt index).1 with
    | none =>
        simp [sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt,
          holdDecode, hdecode] at hrow
    | some oldDart =>
        refine ⟨index, oldDart, holdDecode, ?_⟩
        exact
          (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldIncidenceVertexEq_iff_of_decode
            corridor hunique offset hnext hcell index oldDart holdDecode
              occurrence dart hdecode).1 hrow
  · rintro ⟨index, oldDart, holdDecode, hvertex⟩
    refine ⟨index, ?_⟩
    exact
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldIncidenceVertexEq_iff_of_decode
        corridor hunique offset hnext hcell index oldDart holdDecode occurrence
          dart hdecode).2 hvertex

/-- A genuinely promoted occurrence adjacent to the predecessor carrier has
one of the forty-eight oriented predecessor incidences as its literal entry
address.  The converse additionally needs the predecessor incidence-present
bit: padded seam lookahead may have the same ambient incidence vertex without
being active in the pre-rebase region. -/
theorem
    sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldIncidenceIndex?_isSome_of_oldNeighbor?_isSome_of_promoted
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
    (hpromoted :
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).promoted occurrence = true)
    (hneighbor :
      ((sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).oldNeighbor? occurrence).isSome) :
    ((sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell).oldIncidenceIndex? occurrence).isSome := by
  classical
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
  rcases
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldNeighbor?_isSome_iff_of_decode
        corridor hunique offset hnext hcell occurrence dart hdecode).1
        hneighbor with
    ⟨oldDart, hadj⟩
  let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
    hunique offset
  let oldDartAt := fun slot : Fin oldCarrier.card =>
    ((carrierCoordinate oldCarrier).symm slot).1
  have houtside : OutsideInterface oldDartAt dart := by
    intro slot heq
    apply hsemantic.2
    have hslot : ((carrierCoordinate oldCarrier).symm slot).1 ∈ oldCarrier :=
      ((carrierCoordinate oldCarrier).symm slot).2
    rw [heq]
    exact hslot
  rcases exists_faceInterfaceIncidence_of_adj_outside web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      oldDartAt (carrierCoordinate oldCarrier oldDart) dart
        (by simpa [oldDartAt, oldCarrier] using hadj) houtside with
    ⟨direction, hvertex, _hpresent⟩
  let index := sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceEquiv
    (sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset hcell
      oldDart, direction)
  apply
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldIncidenceIndex?_isSome_iff_of_decode
      corridor hunique offset hnext hcell occurrence dart hdecode).2
  refine ⟨index, oldDart, ?_, ?_⟩
  · simp [index, sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt]
  · simpa [index, sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt,
      oldDartAt, oldCarrier] using hvertex

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
