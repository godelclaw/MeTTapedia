import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedFaceBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableParametricCapState

/-!
# Active predecessor incidences on the expanded facial receipt

The expanded Cell--rebase receipt remembers which oriented predecessor face
incidence has a requested occurrence as its exterior vertex.  The cumulative
cap table separately remembers which predecessor incidences are active in the
current regional graph and the cap-six weight of the exterior component they
enter.

This file joins those two finite records without ambient graph data.  The
query is parameterized by the embedding of the cap table's live dependent
carrier into the stable twenty-four predecessor slots.  It returns an active
oriented incidence, and therefore an executable predecessor cap, only when
both records agree.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableParametricCapState
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellRebaseExpandedFaceActiveIncidenceEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- Canonical finite indexing of the two oriented incidences at every live
predecessor coordinate. -/
def sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceEquiv
    (count : Nat) : (Fin count × Bool) ≃ Fin (count * 2) :=
  (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv

/-- Decode an oriented incidence of the live dependent predecessor carrier. -/
def sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt
    {count : Nat} (index : Fin (count * 2)) : Fin count × Bool :=
  (sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceEquiv count).symm
    index

/-- Embed a live dependent incidence into the stable forty-eight-coordinate
predecessor incidence ABI. -/
def sourceLocalLayerSerialCellRebaseExpandedFacePaddedIncidenceIndex
    {count : Nat} (toPadded : Fin count → Fin 24)
    (incidence : Fin count × Bool) : Fin 48 :=
  sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceEquiv
    (toPadded incidence.1, incidence.2)

/-- Embed the source's live predecessor coordinate into its fixed twenty-four
slot ABI. -/
noncomputable def
    sourceLocalLayerSerialCellRebaseExpandedFaceActualToPaddedAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6) :
    Fin (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
      ).card → Fin 24 :=
  Fin.castLE
    (sourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
      corridor hunique offset hcell)

/-- On a live source dart, the dependent-to-padded embedding is exactly the
existing fixed transition slot. -/
@[simp] theorem
    sourceLocalLayerSerialCellRebaseExpandedFaceActualToPaddedAt_coordinate
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (oldDart : {dart // dart ∈
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset}) :
    sourceLocalLayerSerialCellRebaseExpandedFaceActualToPaddedAt corridor
        hunique offset hcell
        (carrierCoordinate
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset) oldDart) =
      sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset hcell
        oldDart := by
  apply Fin.ext
  simp [sourceLocalLayerSerialCellRebaseExpandedFaceActualToPaddedAt,
    sourceLocalLayerSerialFaceTransitionSlotAt,
    GoertzelV24FramedTrail.boundedFiniteSlot, carrierCoordinate]

/-- Search for an incidence which is active in the cumulative cap table and
whose exterior vertex is the requested expanded occurrence. -/
def
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldActiveIncidenceIndex?
    {count cap : Nat}
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (code : BoundedInterfaceExteriorLabelCapCode
      (Fin count) (Fin count × Bool) cap)
    (toPadded : Fin count → Fin 24)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface) :
    Option (Fin (count * 2)) :=
  Fin.find? fun index =>
    let incidence :=
      sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt index
    code.incidencePresent incidence &&
      state.oldIncidenceVertexEq
        (sourceLocalLayerSerialCellRebaseExpandedFacePaddedIncidenceIndex
          toPadded incidence)
        occurrence

/-- A returned active-incidence index satisfies both finite rows. -/
theorem
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldActiveIncidenceIndex?_sound
    {count cap : Nat}
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (code : BoundedInterfaceExteriorLabelCapCode
      (Fin count) (Fin count × Bool) cap)
    (toPadded : Fin count → Fin 24)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (index : Fin (count * 2))
    (hindex : state.oldActiveIncidenceIndex? code toPadded occurrence =
      some index) :
    let incidence :=
      sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt index
    code.incidencePresent incidence = true ∧
      state.oldIncidenceVertexEq
          (sourceLocalLayerSerialCellRebaseExpandedFacePaddedIncidenceIndex
            toPadded incidence)
          occurrence = true := by
  exact Bool.and_eq_true_iff.mp (Fin.eq_true_of_find?_eq_some hindex)

/-- Active-incidence search succeeds exactly when one live dependent
incidence satisfies both finite rows. -/
theorem
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldActiveIncidenceIndex?_isSome_iff
    {count cap : Nat}
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (code : BoundedInterfaceExteriorLabelCapCode
      (Fin count) (Fin count × Bool) cap)
    (toPadded : Fin count → Fin 24)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface) :
    (state.oldActiveIncidenceIndex? code toPadded occurrence).isSome ↔
      ∃ index : Fin (count * 2),
        let incidence :=
          sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt index
        code.incidencePresent incidence = true ∧
          state.oldIncidenceVertexEq
              (sourceLocalLayerSerialCellRebaseExpandedFacePaddedIncidenceIndex
                toPadded incidence)
              occurrence = true := by
  unfold SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldActiveIncidenceIndex?
  simpa only [Bool.and_eq_true_iff] using
    (Fin.isSome_find?_iff :
      (Fin.find? fun index : Fin (count * 2) =>
        let incidence :=
          sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt index
        code.incidencePresent incidence &&
          state.oldIncidenceVertexEq
            (sourceLocalLayerSerialCellRebaseExpandedFacePaddedIncidenceIndex
              toPadded incidence)
            occurrence).isSome ↔ _)

/-- Read the predecessor component weight at the first matching active
incidence. -/
def
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldActiveIncidenceCap?
    {count cap : Nat}
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (code : BoundedInterfaceExteriorLabelCapCode
      (Fin count) (Fin count × Bool) cap)
    (toPadded : Fin count → Fin 24)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface) :
    Option (Fin (cap + 1)) :=
  (state.oldActiveIncidenceIndex? code toPadded occurrence).map fun index =>
    code.incidenceCap
      (sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt index)

/-- Once active-incidence search has returned an index, the cap query reads
the cumulative table at precisely that decoded incidence. -/
theorem
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldActiveIncidenceCap?_eq_some_of_index
    {count cap : Nat}
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (code : BoundedInterfaceExteriorLabelCapCode
      (Fin count) (Fin count × Bool) cap)
    (toPadded : Fin count → Fin 24)
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (index : Fin (count * 2))
    (hindex : state.oldActiveIncidenceIndex? code toPadded occurrence =
      some index) :
    state.oldActiveIncidenceCap? code toPadded occurrence =
      some (code.incidenceCap
        (sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt
          index)) := by
  simp [SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldActiveIncidenceCap?,
    hindex]

/-- On a literal source receipt, an active predecessor incidence exists
exactly when a genuinely promoted occurrence has a predecessor neighbour.
The occurrence row supplies the oriented endpoint equality; the cumulative
cap row supplies regional activity. -/
theorem
    sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldActiveIncidenceIndex?_isSome_iff_oldNeighbor?_isSome_of_decode_of_promoted
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength cap : Nat}
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
    (hpromoted :
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).promoted occurrence = true) :
    let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let oldDartAt := fun slot : Fin oldCarrier.card ↦
      ((carrierCoordinate oldCarrier).symm slot).1
    let state :=
      sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell
    let code := exactFaceInterfaceExteriorLabelCapCode web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      oldDartAt cap
    let toPadded :=
      sourceLocalLayerSerialCellRebaseExpandedFaceActualToPaddedAt corridor
        hunique offset hcell
    (state.oldActiveIncidenceIndex? code toPadded occurrence).isSome ↔
      (state.oldNeighbor? occurrence).isSome := by
  classical
  dsimp only
  let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
    hunique offset
  let oldDartAt := fun slot : Fin oldCarrier.card ↦
    ((carrierCoordinate oldCarrier).symm slot).1
  let state :=
    sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell
  let code := exactFaceInterfaceExteriorLabelCapCode web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    oldDartAt cap
  let toPadded :=
    sourceLocalLayerSerialCellRebaseExpandedFaceActualToPaddedAt corridor
      hunique offset hcell
  have hsemantic :=
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_promoted_iff_of_decode
      corridor hunique offset hnext hcell occurrence dart hdecode).1 hpromoted
  rw [SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.oldActiveIncidenceIndex?_isSome_iff,
    sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldNeighbor?_isSome_iff_of_decode
      corridor hunique offset hnext hcell occurrence dart hdecode]
  constructor
  · rintro ⟨index, hpresent, hrow⟩
    let incidence :=
      sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt index
    let oldDart : {dart // dart ∈ oldCarrier} :=
      (carrierCoordinate oldCarrier).symm incidence.1
    let paddedIndex :=
      sourceLocalLayerSerialCellRebaseExpandedFacePaddedIncidenceIndex
        toPadded incidence
    have htoPadded :
        toPadded incidence.1 =
          sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
            hcell oldDart := by
      calc
        toPadded incidence.1 =
            toPadded (carrierCoordinate oldCarrier oldDart) := by
              simp [oldDart]
        _ = sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
              hcell oldDart := by
            exact
              sourceLocalLayerSerialCellRebaseExpandedFaceActualToPaddedAt_coordinate
                corridor hunique offset hcell oldDart
    have holdDecode :
        sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique offset
            hcell
            (sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt
              paddedIndex).1 =
          some oldDart := by
      simp [paddedIndex,
        sourceLocalLayerSerialCellRebaseExpandedFacePaddedIncidenceIndex,
        sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt, oldDart,
        incidence, htoPadded]
    have hvertex :
        faceInterfaceIncidenceVertex web.annular.RS oldDartAt incidence =
          dart := by
      have hvertex' :=
        (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldIncidenceVertexEq_iff_of_decode
          corridor hunique offset hnext hcell paddedIndex oldDart holdDecode
            occurrence dart hdecode).1
          (by simpa [paddedIndex] using hrow)
      simpa [paddedIndex,
        sourceLocalLayerSerialCellRebaseExpandedFacePaddedIncidenceIndex,
        sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt,
        oldDart, oldDartAt, oldCarrier] using hvertex'
    have hactive :=
      (exactFaceInterfaceExteriorLabelCapCode_incidencePresent_iff
        web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        oldDartAt incidence cap).1 hpresent
    refine ⟨oldDart, ?_⟩
    rw [hvertex] at hactive
    simpa [oldDartAt, oldDart] using hactive.2
  · rintro ⟨oldDart, hadj⟩
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
      ⟨direction, hvertex, hpresent⟩
    let incidence : Fin oldCarrier.card × Bool :=
      (carrierCoordinate oldCarrier oldDart, direction)
    let index :=
      sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceEquiv
        oldCarrier.card incidence
    have hactual :
        sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt index =
          incidence := by
      simp [index,
        sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt]
    refine ⟨index, ?_, ?_⟩
    · have hcode :=
        (exactFaceInterfaceExteriorLabelCapCode_incidencePresent_iff
          web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
          oldDartAt incidence cap).2 hpresent
      change code.incidencePresent
          (sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt
            index) = true
      rw [hactual]
      exact hcode
    · let paddedIndex :=
        sourceLocalLayerSerialCellRebaseExpandedFacePaddedIncidenceIndex
          toPadded incidence
      have htoPadded :
          toPadded incidence.1 =
            sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
              hcell oldDart := by
        calc
          toPadded incidence.1 =
              toPadded (carrierCoordinate oldCarrier oldDart) := by
                simp [incidence]
          _ = sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique
                offset hcell oldDart := by
              exact
                sourceLocalLayerSerialCellRebaseExpandedFaceActualToPaddedAt_coordinate
                  corridor hunique offset hcell oldDart
      have holdDecode :
          sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique
              offset hcell
              (sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt
                paddedIndex).1 =
            some oldDart := by
        simp [paddedIndex,
          sourceLocalLayerSerialCellRebaseExpandedFacePaddedIncidenceIndex,
          sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt,
          incidence, htoPadded]
      have hrow :
          state.oldIncidenceVertexEq paddedIndex occurrence = true := by
        apply
          (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldIncidenceVertexEq_iff_of_decode
            corridor hunique offset hnext hcell paddedIndex oldDart holdDecode
              occurrence dart hdecode).2
        simpa [paddedIndex,
          sourceLocalLayerSerialCellRebaseExpandedFacePaddedIncidenceIndex,
          sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt,
          incidence, oldDartAt, oldCarrier] using hvertex
      change state.oldIncidenceVertexEq
          (sourceLocalLayerSerialCellRebaseExpandedFacePaddedIncidenceIndex
            toPadded
            (sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt
              index)) occurrence = true
      rw [hactual]
      exact hrow

/-- The cumulative cap-parametric predecessor state exposes exactly the same
active-incidence search.  This is the stored-state form consumed by the
finite Cell rebase. -/
theorem
    sourceLocalLayerSerialFaceDeletionStableParametricCapPreRebaseAt_oldActiveIncidenceIndex?_isSome_iff_oldNeighbor?_isSome_of_decode_of_promoted
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength cap : Nat}
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
    (hpromoted :
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).promoted occurrence = true) :
    let capState :=
      sourceLocalLayerSerialFaceDeletionStableParametricCapPreRebaseAt corridor
        hunique offset hcell cap
    let state :=
      sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell
    let toPadded :=
      sourceLocalLayerSerialCellRebaseExpandedFaceActualToPaddedAt corridor
        hunique offset hcell
    (state.oldActiveIncidenceIndex? (capState.code ()) toPadded occurrence
        ).isSome ↔
      (state.oldNeighbor? occurrence).isSome := by
  dsimp only
  rw [sourceLocalLayerSerialFaceDeletionStableParametricCapPreRebaseAt_code_eq]
  exact
    sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldActiveIncidenceIndex?_isSome_iff_oldNeighbor?_isSome_of_decode_of_promoted
      corridor hunique offset hnext hcell occurrence dart hdecode hpromoted

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
