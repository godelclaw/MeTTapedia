import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedFaceActiveIncidence
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedFaceBlocks

/-!
# Finite promoted-label counts at predecessor face components

The cumulative cap table identifies old strict-exterior face components by
oriented live incidences.  The expanded occurrence receipt identifies the
short blocks of newly promoted darts and equality of their underlying primal
edges.  This file combines those two finite records.

A promoted block is attached to an anchor incidence when it reaches an
occurrence whose active predecessor incidence belongs to the anchor's old
exterior component.  The promoted-label graph then joins attached occurrence
coordinates carrying the same primal edge.  Its connected-component count is
the graph-free candidate for the number of distinct labels removed from that
old component.

No ambient graph enters these definitions.  Source theorems below establish
their literal meaning before the count is used by the capped rebase.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellRebaseExpandedFacePromotedLabelCountEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- Test whether the active predecessor incidence found at an occurrence
belongs to the same old exterior component as a fixed anchor incidence. -/
def
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.activeIncidenceConnectedTo
    {count cap : Nat}
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (code : BoundedInterfaceExteriorLabelCapCode
      (Fin count) (Fin count × Bool) cap)
    (toPadded : Fin count → Fin 24)
    (anchor : Fin (count * 2))
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface) : Bool :=
  match state.oldActiveIncidenceIndex? code toPadded occurrence with
  | some target =>
      code.incidenceConnected
        (sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt anchor)
        (sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt target)
  | none => false

/-- Exact option-level semantics of the connected-incidence test. -/
theorem
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.activeIncidenceConnectedTo_eq_true_iff
    {count cap : Nat}
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (code : BoundedInterfaceExteriorLabelCapCode
      (Fin count) (Fin count × Bool) cap)
    (toPadded : Fin count → Fin 24)
    (anchor : Fin (count * 2))
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface) :
    state.activeIncidenceConnectedTo code toPadded anchor occurrence = true ↔
      ∃ target : Fin (count * 2),
        state.oldActiveIncidenceIndex? code toPadded occurrence = some target ∧
          code.incidenceConnected
            (sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt
              anchor)
            (sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt
              target) = true := by
  unfold SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.activeIncidenceConnectedTo
  cases htarget : state.oldActiveIncidenceIndex? code toPadded occurrence with
  | none => simp
  | some target => simp

/-- A promoted occurrence is attached to an anchor old component when its
finite promoted block reaches an occurrence with a connected active
predecessor incidence. -/
def
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.PromotedAttachedToIncidence
    {count cap : Nat}
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (code : BoundedInterfaceExteriorLabelCapCode
      (Fin count) (Fin count × Bool) cap)
    (toPadded : Fin count → Fin 24)
    (anchor : Fin (count * 2))
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface) : Prop :=
  ∃ (start endpoint :
      SourceLocalLayerSerialCellRebaseExpandedFacePromotedSlot state),
    start.1 = occurrence ∧
      state.promotedBlockGraph.Reachable start endpoint ∧
        state.activeIncidenceConnectedTo code toPadded anchor endpoint.1 = true

/-- Boolean reflection of attachment to one anchored old component. -/
noncomputable def
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.promotedAttachedToIncidence
    {count cap : Nat}
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (code : BoundedInterfaceExteriorLabelCapCode
      (Fin count) (Fin count × Bool) cap)
    (toPadded : Fin count → Fin 24)
    (anchor : Fin (count * 2))
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface) : Bool := by
  classical
  exact decide
    (state.PromotedAttachedToIncidence code toPadded anchor occurrence)

@[simp] theorem
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.promotedAttachedToIncidence_eq_true_iff
    {count cap : Nat}
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (code : BoundedInterfaceExteriorLabelCapCode
      (Fin count) (Fin count × Bool) cap)
    (toPadded : Fin count → Fin 24)
    (anchor : Fin (count * 2))
    (occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface) :
    state.promotedAttachedToIncidence code toPadded anchor occurrence = true ↔
      state.PromotedAttachedToIncidence code toPadded anchor occurrence := by
  classical
  simp [SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.promotedAttachedToIncidence]

/-- Occurrence coordinates attached to one anchored predecessor component. -/
abbrev SourceLocalLayerSerialCellRebaseExpandedFacePromotedAttachedSlot
    {count cap : Nat}
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (code : BoundedInterfaceExteriorLabelCapCode
      (Fin count) (Fin count × Bool) cap)
    (toPadded : Fin count → Fin 24)
    (anchor : Fin (count * 2)) :=
  {occurrence : SourceLocalLayerSerialCellRebaseExpandedFaceInterface //
    state.promotedAttachedToIncidence code toPadded anchor occurrence = true}

/-- Equality of underlying primal edges, restricted to the promoted
occurrences attached to one old component.  `fromRel` removes reflexive loops
and symmetrizes malformed finite inputs; on source states it presents exactly
the label-equality classes. -/
def
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.promotedLabelGraph
    {count cap : Nat}
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (code : BoundedInterfaceExteriorLabelCapCode
      (Fin count) (Fin count × Bool) cap)
    (toPadded : Fin count → Fin 24)
    (anchor : Fin (count * 2)) :
    SimpleGraph
      (SourceLocalLayerSerialCellRebaseExpandedFacePromotedAttachedSlot state
        code toPadded anchor) :=
  SimpleGraph.fromRel fun left right =>
    state.samePrimalEdge left.1 right.1 = true

/-- Executable number of promoted primal-edge classes attached to one old
component anchor. -/
noncomputable def
    SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState.promotedLabelCount
    {count cap : Nat}
    (state : SourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceState)
    (code : BoundedInterfaceExteriorLabelCapCode
      (Fin count) (Fin count × Bool) cap)
    (toPadded : Fin count → Fin 24)
    (anchor : Fin (count * 2)) : Nat :=
  Fintype.card (state.promotedLabelGraph code toPadded anchor).ConnectedComponent

/-- A finite promoted-block path maps to a path in the predecessor strict
exterior graph.  Every promoted source dart lies outside the rolling carrier,
so the induced ambient facial path survives the exterior restriction. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFace_promotedBlock_exterior_reachable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (start endpoint : SourceLocalLayerSerialCellRebaseExpandedFacePromotedSlot
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell))
    (hreachable :
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).promotedBlockGraph.Reachable start endpoint) :
    let oldCarrier :=
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
    let oldDartAt := fun slot : Fin oldCarrier.card ↦
      ((carrierCoordinate oldCarrier).symm slot).1
    (exteriorGraph
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset))
      oldDartAt).Reachable
        (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
          hunique offset hnext hcell start)
        (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
          hunique offset hnext hcell endpoint) := by
  classical
  dsimp only
  let oldCarrier :=
    sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
  let oldDartAt := fun slot : Fin oldCarrier.card ↦
    ((carrierCoordinate oldCarrier).symm slot).1
  let promotedToExterior :
      sourceLocalLayerSerialCellRebasePromotedFaceGraphAt corridor hunique
          offset hnext →g
        exteriorGraph
          (faceRegionalDartGraph web.annular.RS
            (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
              offset)) oldDartAt :=
    { toFun := fun vertex => vertex.1
      map_rel' := by
        intro left right hadj
        refine ⟨hadj, ?_, ?_⟩
        · intro slot heq
          apply left.2.2.1
          have hslot :
              ((carrierCoordinate oldCarrier).symm slot).1 ∈ oldCarrier :=
            ((carrierCoordinate oldCarrier).symm slot).2
          rw [heq]
          exact hslot
        · intro slot heq
          apply right.2.2.1
          have hslot :
              ((carrierCoordinate oldCarrier).symm slot).1 ∈ oldCarrier :=
            ((carrierCoordinate oldCarrier).symm slot).2
          rw [heq]
          exact hslot }
  have hambient :=
    sourceLocalLayerSerialCellRebaseExpandedFace_promotedBlock_reachable
      corridor hunique offset hnext hcell start endpoint hreachable
  have hmapped := hambient.map promotedToExterior
  change (exteriorGraph
    (faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset))
    oldDartAt).Reachable
      (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
        hunique offset hnext hcell start)
      (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
        hunique offset hnext hcell endpoint) at hmapped
  exact hmapped

/-- On a literal source receipt, finite attachment to an active predecessor
incidence is sound for membership in that predecessor exterior component.
The promoted-block path is transported through genuinely promoted darts; the
active-incidence row identifies its endpoint with the exact exterior entry.
-/
theorem
    sourceLocalLayerSerialCellRebaseExpandedFace_promotedAttachedToIncidence_reachable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength cap : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (anchor : Fin
      ((sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
        ).card * 2))
    (start : SourceLocalLayerSerialCellRebaseExpandedFacePromotedSlot
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell))
    (hattached :
      let oldCarrier :=
        sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
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
      state.PromotedAttachedToIncidence code toPadded anchor start.1) :
    let oldCarrier :=
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
    let oldDartAt := fun slot : Fin oldCarrier.card ↦
      ((carrierCoordinate oldCarrier).symm slot).1
    let anchorIncidence :=
      sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt anchor
    (exteriorGraph
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset))
      oldDartAt).Reachable
        (faceInterfaceIncidenceVertex web.annular.RS oldDartAt anchorIncidence)
        (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
          hunique offset hnext hcell start) := by
  classical
  dsimp only at hattached ⊢
  let oldCarrier :=
    sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
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
  rcases hattached with
    ⟨attachedStart, endpoint, hstart, hblock, hactive⟩
  have hstartEq : attachedStart = start := Subtype.ext hstart
  subst attachedStart
  rcases
      (state.activeIncidenceConnectedTo_eq_true_iff code toPadded anchor
        endpoint.1).1 hactive with
    ⟨target, htarget, hconnected⟩
  let targetIncidence :=
    sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt target
  let targetOldDart : {dart // dart ∈ oldCarrier} :=
    (carrierCoordinate oldCarrier).symm targetIncidence.1
  let paddedTarget :=
    sourceLocalLayerSerialCellRebaseExpandedFacePaddedIncidenceIndex toPadded
      targetIncidence
  have htargetRows := state.oldActiveIncidenceIndex?_sound code toPadded
    endpoint.1 target htarget
  have htoPadded :
      toPadded targetIncidence.1 =
        sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
          hcell targetOldDart := by
    calc
      toPadded targetIncidence.1 =
          toPadded (carrierCoordinate oldCarrier targetOldDart) := by
            simp [targetOldDart]
      _ = sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
            hcell targetOldDart := by
          exact
            sourceLocalLayerSerialCellRebaseExpandedFaceActualToPaddedAt_coordinate
              corridor hunique offset hcell targetOldDart
  have holdDecode :
      sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique offset
          hcell
          (sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt
            paddedTarget).1 =
        some targetOldDart := by
    simp [paddedTarget,
      sourceLocalLayerSerialCellRebaseExpandedFacePaddedIncidenceIndex,
      sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt,
      targetOldDart, targetIncidence, htoPadded]
  have htargetVertex :
      faceInterfaceIncidenceVertex web.annular.RS oldDartAt targetIncidence =
        sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
          hunique offset hnext hcell endpoint := by
    have hvertex :=
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldIncidenceVertexEq_iff_of_decode
        corridor hunique offset hnext hcell paddedTarget targetOldDart
          holdDecode endpoint.1
          (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
            hunique offset hnext hcell endpoint)
          (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_spec
            corridor hunique offset hnext hcell endpoint)).1
        (by simpa [paddedTarget] using htargetRows.2)
    simpa [paddedTarget,
      sourceLocalLayerSerialCellRebaseExpandedFacePaddedIncidenceIndex,
      sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt,
      targetOldDart, oldDartAt, oldCarrier] using hvertex
  have hanchorToEndpoint :
      (exteriorGraph
        (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
            offset)) oldDartAt).Reachable
        (faceInterfaceIncidenceVertex web.annular.RS oldDartAt
          (sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt
            anchor))
        (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
          hunique offset hnext hcell endpoint) := by
    have hsemantic :=
      (exactInterfaceExteriorLabelCapCode_incidenceConnected_iff
        (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
            offset)) oldDartAt
        (fun dart => web.annular.RS.edgeOf dart ∈
          sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        Prod.fst (faceInterfaceIncidenceVertex web.annular.RS oldDartAt)
        web.annular.RS.edgeOf
        (sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt anchor)
        targetIncidence cap).1 hconnected
    rw [htargetVertex] at hsemantic
    exact hsemantic.2.2
  have hstartToEndpoint :=
    sourceLocalLayerSerialCellRebaseExpandedFace_promotedBlock_exterior_reachable
      corridor hunique offset hnext hcell start endpoint hblock
  exact hanchorToEndpoint.trans hstartToEndpoint.symm

/-- Conversely, under the finite non-splitting condition, every promoted dart
in an active anchored predecessor component is detected by the finite
attachment predicate.  This is the completeness direction needed before the
attached label quotient may drive capped subtraction. -/
theorem
    sourceLocalLayerSerialCellRebaseExpandedFace_reachable_promotedAttachedToIncidence
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength cap : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (anchor : Fin
      ((sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
        ).card * 2))
    (start : SourceLocalLayerSerialCellRebaseExpandedFacePromotedSlot
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell))
    (hblocks :
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).PromotedBlocksMeetOld)
    (hanchorPresent :
      let oldCarrier :=
        sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
      let oldDartAt := fun slot : Fin oldCarrier.card ↦
        ((carrierCoordinate oldCarrier).symm slot).1
      let code := exactFaceInterfaceExteriorLabelCapCode web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        oldDartAt cap
      code.incidencePresent
        (sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt anchor) =
          true)
    (hreachable :
      let oldCarrier :=
        sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
      let oldDartAt := fun slot : Fin oldCarrier.card ↦
        ((carrierCoordinate oldCarrier).symm slot).1
      let anchorIncidence :=
        sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt anchor
      (exteriorGraph
        (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
            offset)) oldDartAt).Reachable
          (faceInterfaceIncidenceVertex web.annular.RS oldDartAt
            anchorIncidence)
          (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
            hunique offset hnext hcell start)) :
    let oldCarrier :=
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
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
    state.PromotedAttachedToIncidence code toPadded anchor start.1 := by
  classical
  dsimp only at hanchorPresent hreachable ⊢
  let oldCarrier :=
    sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
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
  rcases hblocks start with ⟨endpoint, hblock, hendpointOld⟩
  refine ⟨start, endpoint, rfl, hblock, ?_⟩
  apply
    (state.activeIncidenceConnectedTo_eq_true_iff code toPadded anchor
      endpoint.1).2
  have hactiveSome :
      (state.oldActiveIncidenceIndex? code toPadded endpoint.1).isSome :=
    (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldActiveIncidenceIndex?_isSome_iff_oldNeighbor?_isSome_of_decode_of_promoted
      corridor hunique offset hnext hcell endpoint.1
        (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
          hunique offset hnext hcell endpoint)
        (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_spec
          corridor hunique offset hnext hcell endpoint) endpoint.2).2
      hendpointOld
  rcases Option.isSome_iff_exists.mp hactiveSome with ⟨target, htarget⟩
  refine ⟨target, htarget, ?_⟩
  let targetIncidence :=
    sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt target
  let targetOldDart : {dart // dart ∈ oldCarrier} :=
    (carrierCoordinate oldCarrier).symm targetIncidence.1
  let paddedTarget :=
    sourceLocalLayerSerialCellRebaseExpandedFacePaddedIncidenceIndex toPadded
      targetIncidence
  have htargetRows := state.oldActiveIncidenceIndex?_sound code toPadded
    endpoint.1 target htarget
  have htoPadded :
      toPadded targetIncidence.1 =
        sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
          hcell targetOldDart := by
    calc
      toPadded targetIncidence.1 =
          toPadded (carrierCoordinate oldCarrier targetOldDart) := by
            simp [targetOldDart]
      _ = sourceLocalLayerSerialFaceTransitionSlotAt corridor hunique offset
            hcell targetOldDart := by
          exact
            sourceLocalLayerSerialCellRebaseExpandedFaceActualToPaddedAt_coordinate
              corridor hunique offset hcell targetOldDart
  have holdDecode :
      sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor hunique offset
          hcell
          (sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt
            paddedTarget).1 =
        some targetOldDart := by
    simp [paddedTarget,
      sourceLocalLayerSerialCellRebaseExpandedFacePaddedIncidenceIndex,
      sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt,
      targetOldDart, targetIncidence, htoPadded]
  have htargetVertex :
      faceInterfaceIncidenceVertex web.annular.RS oldDartAt targetIncidence =
        sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
          hunique offset hnext hcell endpoint := by
    have hvertex :=
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldIncidenceVertexEq_iff_of_decode
        corridor hunique offset hnext hcell paddedTarget targetOldDart
          holdDecode endpoint.1
          (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
            hunique offset hnext hcell endpoint)
          (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_spec
            corridor hunique offset hnext hcell endpoint)).1
        (by simpa [paddedTarget] using htargetRows.2)
    simpa [paddedTarget,
      sourceLocalLayerSerialCellRebaseExpandedFacePaddedIncidenceIndex,
      sourceLocalLayerSerialCellRebaseExpandedFaceOldIncidenceAt,
      targetOldDart, oldDartAt, oldCarrier] using hvertex
  have hstartToEndpoint :=
    sourceLocalLayerSerialCellRebaseExpandedFace_promotedBlock_exterior_reachable
      corridor hunique offset hnext hcell start endpoint hblock
  apply
    (exactInterfaceExteriorLabelCapCode_incidenceConnected_iff
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset))
      oldDartAt
      (fun dart => web.annular.RS.edgeOf dart ∈
        sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      Prod.fst (faceInterfaceIncidenceVertex web.annular.RS oldDartAt)
      web.annular.RS.edgeOf
      (sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt anchor)
      targetIncidence cap).2
  refine ⟨?_, ?_, ?_⟩
  · exact
      (exactFaceInterfaceExteriorLabelCapCode_incidencePresent_iff
        web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        oldDartAt
        (sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt anchor)
        cap).1 hanchorPresent
  · exact
      (exactFaceInterfaceExteriorLabelCapCode_incidencePresent_iff
        web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        oldDartAt targetIncidence cap).1 htargetRows.1
  · rw [htargetVertex]
    exact hreachable.trans hstartToEndpoint

/-- Exact source semantics of the finite attachment predicate.  With one
active anchor and the already required promoted-block condition, attachment
is precisely reachability from the anchored predecessor incidence through the
old strict exterior component. -/
theorem
    sourceLocalLayerSerialCellRebaseExpandedFace_promotedAttachedToIncidence_iff_reachable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength cap : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (anchor : Fin
      ((sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
        ).card * 2))
    (start : SourceLocalLayerSerialCellRebaseExpandedFacePromotedSlot
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell))
    (hblocks :
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).PromotedBlocksMeetOld)
    (hanchorPresent :
      let oldCarrier :=
        sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
      let oldDartAt := fun slot : Fin oldCarrier.card ↦
        ((carrierCoordinate oldCarrier).symm slot).1
      let code := exactFaceInterfaceExteriorLabelCapCode web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        oldDartAt cap
      code.incidencePresent
        (sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt anchor) =
          true) :
    let oldCarrier :=
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
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
    let anchorIncidence :=
      sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt anchor
    state.PromotedAttachedToIncidence code toPadded anchor start.1 ↔
      (exteriorGraph
        (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
            offset)) oldDartAt).Reachable
          (faceInterfaceIncidenceVertex web.annular.RS oldDartAt
            anchorIncidence)
          (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
            hunique offset hnext hcell start) := by
  dsimp only
  constructor
  · exact
      sourceLocalLayerSerialCellRebaseExpandedFace_promotedAttachedToIncidence_reachable
        corridor hunique offset hnext hcell anchor start
  · exact
      sourceLocalLayerSerialCellRebaseExpandedFace_reachable_promotedAttachedToIncidence
        corridor hunique offset hnext hcell anchor start hblocks hanchorPresent

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
