import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedFacePromotedLabelCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedFaceRetainedCap

/-!
# Finite promoted-label subtraction for a facial Cell rebase

The expanded receipt counts the distinct primal-edge labels carried by
promoted occurrences attached to an active predecessor incidence.  This file
identifies that finite support with the literal promoted-label set of the
anchored predecessor exterior component.  It is the adapter between the
finite occurrence state and the already proved cap-six deletion recurrence.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence
open GoertzelV24DegreeTwoExteriorBoundary
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceEnlargementCappedDeletion
open GoertzelV24InterfaceEnlargementRetainedLabels
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellRebaseExpandedFacePromotedLabelCapUpdateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The predecessor strict-exterior component selected by one active oriented
incidence of the live facial interface. -/
noncomputable def
    sourceLocalLayerSerialCellRebaseExpandedFaceAnchoredExteriorComponentAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (anchor : Fin
      ((sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
        ).card * 2)) :
    (exteriorGraph
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset))
      (fun slot : Fin
        (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
          ).card ↦
        ((carrierCoordinate
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset)).symm slot).1)).ConnectedComponent := by
  let oldCarrier :=
    sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
  let oldDartAt := fun slot : Fin oldCarrier.card ↦
    ((carrierCoordinate oldCarrier).symm slot).1
  let anchorIncidence :=
    sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt anchor
  exact
    (exteriorGraph
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset))
      oldDartAt).connectedComponentMk
        (faceInterfaceIncidenceVertex web.annular.RS oldDartAt anchorIncidence)

/-- For an active predecessor incidence, the finite attached-edge support is
exactly the set of promoted labels in its literal exterior component. -/
theorem
    sourceLocalLayerSerialCellRebaseExpandedFace_promotedAttachedEdgeSupport_eq_promotedExteriorComponentLabels
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
    let graph := faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    let oldCarrier :=
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
    let oldDartAt := fun slot : Fin oldCarrier.card ↦
      ((carrierCoordinate oldCarrier).symm slot).1
    let newDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
      hunique offset hnext
    let anchorIncidence :=
      sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt anchor
    let anchorDart :=
      faceInterfaceIncidenceVertex web.annular.RS oldDartAt anchorIncidence
    let component := (exteriorGraph graph oldDartAt).connectedComponentMk
      anchorDart
    sourceLocalLayerSerialCellRebaseExpandedFacePromotedAttachedEdgeSupportAt
        (cap := cap) corridor hunique offset hnext hcell anchor =
      promotedExteriorComponentLabels graph oldDartAt newDartAt
        web.annular.RS.edgeOf component := by
  classical
  dsimp only at hanchorPresent ⊢
  let region :=
    sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset
  let graph := faceRegionalDartGraph web.annular.RS region
  let oldCarrier :=
    sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
  let oldDartAt := fun slot : Fin oldCarrier.card ↦
    ((carrierCoordinate oldCarrier).symm slot).1
  let uniform := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let newDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  let state :=
    sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell
  let code := exactFaceInterfaceExteriorLabelCapCode web.annular.RS region
    oldDartAt cap
  let toPadded :=
    sourceLocalLayerSerialCellRebaseExpandedFaceActualToPaddedAt corridor
      hunique offset hcell
  let anchorIncidence :=
    sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt anchor
  let anchorDart :=
    faceInterfaceIncidenceVertex web.annular.RS oldDartAt anchorIncidence
  let component := (exteriorGraph graph oldDartAt).connectedComponentMk
    anchorDart
  have hanchorSemantic :
      OutsideInterface oldDartAt anchorDart ∧
        graph.Adj (oldDartAt anchorIncidence.1) anchorDart := by
    simpa [graph, code, region, anchorDart, anchorIncidence] using
      ((exactFaceInterfaceExteriorLabelCapCode_incidencePresent_iff
        web.annular.RS region oldDartAt anchorIncidence cap).1
          hanchorPresent)
  apply Finset.ext
  intro edge
  constructor
  · intro hedge
    rcases Finset.mem_image.mp hedge with ⟨attached, _huniv, hattachedEdge⟩
    let promoted := state.promotedSlotOfAttached code toPadded anchor attached
    let dart :=
      sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
        hunique offset hnext hcell promoted
    have hattached :
        state.PromotedAttachedToIncidence code toPadded anchor attached.1 :=
      (state.promotedAttachedToIncidence_eq_true_iff code toPadded anchor
        attached.1).1 attached.2
    have hreachable :
        (exteriorGraph graph oldDartAt).Reachable anchorDart dart := by
      simpa [graph, region, oldCarrier, oldDartAt, state, code, toPadded,
        anchorIncidence, anchorDart, promoted, dart] using
        (sourceLocalLayerSerialCellRebaseExpandedFace_promotedAttachedToIncidence_reachable
          corridor hunique offset hnext hcell anchor promoted hattached)
    have hdartComponent : dart ∈ component.supp := by
      apply (component.mem_supp_iff dart).2
      simpa [component] using
        (SimpleGraph.ConnectedComponent.sound hreachable).symm
    let vertex : component := ⟨dart, hdartComponent⟩
    have hdartUniform : dart ∈ uniform := by
      exact
        sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot?_mem_uniform
          corridor hunique offset hnext hcell promoted.1 dart
            (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_spec
              corridor hunique offset hnext hcell promoted)
    apply (mem_promotedExteriorComponentLabels_iff graph oldDartAt newDartAt
      web.annular.RS.edgeOf component edge).2
    refine ⟨vertex, ?_, ?_⟩
    · refine ⟨carrierCoordinate uniform ⟨dart, hdartUniform⟩, ?_⟩
      simp [newDartAt,
        sourceLocalLayerSerialCellRebaseUniformFaceDartAt, uniform, vertex]
    · have hdecoded :
          sourceLocalLayerSerialCellRebaseExpandedFacePromotedAttachedEdgeAt
              (cap := cap) corridor hunique offset hnext hcell anchor attached =
            web.annular.RS.edgeOf dart := by
        rfl
      exact hdecoded ▸ hattachedEdge
  · intro hedge
    rcases (mem_promotedExteriorComponentLabels_iff graph oldDartAt newDartAt
      web.annular.RS.edgeOf component edge).1 hedge with
      ⟨vertex, ⟨newSlot, hnewSlot⟩, hlabel⟩
    have hvertexComponent :
        (exteriorGraph graph oldDartAt).connectedComponentMk vertex.1 =
          component :=
      (component.mem_supp_iff vertex.1).1 vertex.2
    have hreachable :
        (exteriorGraph graph oldDartAt).Reachable anchorDart vertex.1 := by
      apply SimpleGraph.ConnectedComponent.exact
      simpa [component] using hvertexComponent.symm
    have hvertexOutside : OutsideInterface oldDartAt vertex.1 :=
      outsideInterface_of_exteriorGraph_reachable graph oldDartAt
        hanchorSemantic.1 hreachable
    let occurrence :=
      sourceLocalLayerSerialCellRebaseExpandedFaceSourceAt corridor hunique
        offset hnext hcell newSlot
    have hdecode :
        sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor hunique
            offset hnext hcell occurrence =
          some vertex.1 := by
      rw [show occurrence =
        sourceLocalLayerSerialCellRebaseExpandedFaceSourceAt corridor hunique
          offset hnext hcell newSlot from rfl]
      rw [sourceLocalLayerSerialCellRebaseExpandedFaceSourceAt_dart_eq]
      exact congrArg some hnewSlot
    have hvertexRegion : web.annular.RS.edgeOf vertex.1 ∈ region := by
      by_cases heq : anchorDart = vertex.1
      · rw [← heq]
        exact hanchorSemantic.2.2.2.2
      · have hsupport : vertex.1 ∈ (exteriorGraph graph oldDartAt).support :=
          SimpleGraph.mem_support_of_reachable (Ne.symm heq)
            hreachable.symm
        rcases hsupport with ⟨neighbor, hadj⟩
        exact hadj.1.2.2.1
    have hpromotedOccurrence : state.promoted occurrence = true := by
      apply
        (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_promoted_iff_of_decode
          corridor hunique offset hnext hcell occurrence vertex.1 hdecode).2
      refine ⟨?_, ?_⟩
      · simpa [region] using hvertexRegion
      · intro hold
        exact hvertexOutside
          (carrierCoordinate oldCarrier ⟨vertex.1, hold⟩)
          (by simp [oldDartAt, oldCarrier])
    let promoted : SourceLocalLayerSerialCellRebaseExpandedFacePromotedSlot
        state := ⟨occurrence, hpromotedOccurrence⟩
    have hpromotedDart :
        sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
            hunique offset hnext hcell promoted = vertex.1 := by
      have hspec :=
        sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_spec corridor
          hunique offset hnext hcell promoted
      simpa [promoted, occurrence, hdecode] using hspec.symm
    have hattachedProp :
        state.PromotedAttachedToIncidence code toPadded anchor occurrence := by
      apply
        sourceLocalLayerSerialCellRebaseExpandedFace_reachable_promotedAttachedToIncidence
          corridor hunique offset hnext hcell anchor promoted hblocks
            hanchorPresent
      simpa [graph, region, oldCarrier, oldDartAt, anchorIncidence, anchorDart,
        promoted, hpromotedDart] using hreachable
    have hattachedBool :
        state.promotedAttachedToIncidence code toPadded anchor occurrence =
          true :=
      (state.promotedAttachedToIncidence_eq_true_iff code toPadded anchor
        occurrence).2 hattachedProp
    let attached : SourceLocalLayerSerialCellRebaseExpandedFacePromotedAttachedSlot
        state code toPadded anchor := ⟨occurrence, hattachedBool⟩
    apply Finset.mem_image.2
    refine ⟨attached, Finset.mem_univ _, ?_⟩
    have hattachedDart :
        sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
            hunique offset hnext hcell
            (state.promotedSlotOfAttached code toPadded anchor attached) =
          vertex.1 := by
      have hslot :
          state.promotedSlotOfAttached code toPadded anchor attached =
            promoted := by
        apply Subtype.ext
        rfl
      rw [hslot]
      exact hpromotedDart
    unfold
      sourceLocalLayerSerialCellRebaseExpandedFacePromotedAttachedEdgeAt
    dsimp only
    rw [hattachedDart]
    exact hlabel

/-- The executable promoted-label count is the literal number of labels
removed from the active anchored predecessor component. -/
theorem
    sourceLocalLayerSerialCellRebaseExpandedFace_promotedLabelCount_eq_card_promotedExteriorComponentLabels
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
    let graph := faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    let oldCarrier :=
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
    let oldDartAt := fun slot : Fin oldCarrier.card ↦
      ((carrierCoordinate oldCarrier).symm slot).1
    let newDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
      hunique offset hnext
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
    let anchorDart :=
      faceInterfaceIncidenceVertex web.annular.RS oldDartAt anchorIncidence
    let component := (exteriorGraph graph oldDartAt).connectedComponentMk
      anchorDart
    state.promotedLabelCount code toPadded anchor =
      (promotedExteriorComponentLabels graph oldDartAt newDartAt
        web.annular.RS.edgeOf component).card := by
  dsimp only at hanchorPresent ⊢
  rw [sourceLocalLayerSerialCellRebaseExpandedFace_promotedLabelCount_eq_card_edgeSupport]
  rw [sourceLocalLayerSerialCellRebaseExpandedFace_promotedAttachedEdgeSupport_eq_promotedExteriorComponentLabels
    corridor hunique offset hnext hcell anchor hblocks hanchorPresent]

/-- The literal cap-six facial recurrence expressed entirely through the
finite predecessor code and expanded occurrence receipt. -/
theorem
    sourceLocalLayerSerialCellRebase_min_newExteriorFaceSupport_six_eq_finiteCap_sub_promotedLabelCount
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
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
    (start :
      sourceLocalLayerSerialCellRebaseExpandedFaceAnchoredExteriorComponentAt
        corridor hunique offset anchor)
    (hstartRetained :
      let graph := faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      let oldCarrier :=
        sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
      let oldDartAt := fun slot : Fin oldCarrier.card ↦
        ((carrierCoordinate oldCarrier).symm slot).1
      let newDartAt :=
        sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique
          offset hnext
      start ∈ retainedExteriorComponentVertices graph oldDartAt newDartAt
        (sourceLocalLayerSerialCellRebaseExpandedFaceAnchoredExteriorComponentAt
          corridor hunique offset anchor))
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
        oldDartAt 6
      code.incidencePresent
        (sourceLocalLayerSerialCellRebaseExpandedFaceActualIncidenceAt anchor) =
          true) :
    let graph := faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    let oldCarrier :=
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
    let oldDartAt := fun slot : Fin oldCarrier.card ↦
      ((carrierCoordinate oldCarrier).symm slot).1
    let newDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
      hunique offset hnext
    let state :=
      sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell
    let code := exactFaceInterfaceExteriorLabelCapCode web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      oldDartAt 6
    let toPadded :=
      sourceLocalLayerSerialCellRebaseExpandedFaceActualToPaddedAt corridor
        hunique offset hcell
    let component :=
      sourceLocalLayerSerialCellRebaseExpandedFaceAnchoredExteriorComponentAt
        corridor hunique offset anchor
    min (exteriorComponentLabelSupport graph newDartAt web.annular.RS.edgeOf
        ((exteriorGraph graph newDartAt).connectedComponentMk start.1)).card 6 =
      min (exteriorComponentLabelSupport graph oldDartAt
          web.annular.RS.edgeOf component).card 6 -
        state.promotedLabelCount code toPadded anchor := by
  classical
  dsimp only at hstartRetained hanchorPresent ⊢
  let graph := faceRegionalDartGraph web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
  let oldCarrier :=
    sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
  let oldDartAt := fun slot : Fin oldCarrier.card ↦
    ((carrierCoordinate oldCarrier).symm slot).1
  let newDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  let state :=
    sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell
  let code := exactFaceInterfaceExteriorLabelCapCode web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    oldDartAt 6
  let toPadded :=
    sourceLocalLayerSerialCellRebaseExpandedFaceActualToPaddedAt corridor
      hunique offset hcell
  let component :=
    sourceLocalLayerSerialCellRebaseExpandedFaceAnchoredExteriorComponentAt
      corridor hunique offset anchor
  have hsemantic :=
    sourceLocalLayerSerialCellRebase_min_newExteriorFaceSupport_six_eq_cap_six
      corridor hunique offset hnext hcell component start hstartRetained hblocks
  have hcount :=
    sourceLocalLayerSerialCellRebaseExpandedFace_promotedLabelCount_eq_card_promotedExteriorComponentLabels
      (cap := 6) corridor hunique offset hnext hcell anchor hblocks
        hanchorPresent
  have hcount' :
      state.promotedLabelCount code toPadded anchor =
        (promotedExteriorComponentLabels graph oldDartAt newDartAt
          web.annular.RS.edgeOf component).card := by
    simpa [graph, oldCarrier, oldDartAt, newDartAt, state, code, toPadded,
      component,
      sourceLocalLayerSerialCellRebaseExpandedFaceAnchoredExteriorComponentAt]
      using hcount
  calc
    min (exteriorComponentLabelSupport graph newDartAt web.annular.RS.edgeOf
        ((exteriorGraph graph newDartAt).connectedComponentMk start.1)).card 6 =
        min (exteriorComponentLabelSupport graph oldDartAt
            web.annular.RS.edgeOf component).card 6 -
          (promotedExteriorComponentLabels graph oldDartAt newDartAt
            web.annular.RS.edgeOf component).card := by
      simpa [graph, oldCarrier, oldDartAt, newDartAt, component] using hsemantic
    _ = min (exteriorComponentLabelSupport graph oldDartAt
            web.annular.RS.edgeOf component).card 6 -
          state.promotedLabelCount code toPadded anchor := by
      rw [hcount']

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
