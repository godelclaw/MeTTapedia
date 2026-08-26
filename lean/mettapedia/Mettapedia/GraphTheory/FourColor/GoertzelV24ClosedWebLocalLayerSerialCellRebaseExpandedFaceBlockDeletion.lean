import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedFaceBlocks
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceEnlargementCappedDeletion
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationFaceExteriorBoundary

/-!
# Non-splitting facial rebase from the finite promoted-block receipt

The exact facial occurrence receipt can certify interface enlargement at the
right granularity.  If each connected block of promoted occurrences reaches
one occurrence adjacent to the predecessor carrier, deleting the promoted
darts cannot split an old strict-exterior face component.  An occurrence
outside the literal pre-rebase region is harmless: it is isolated, so naming
it erases its entire old singleton component.

This file connects the finite block graph to the generic degree-two deletion
theorem.  No per-role or corridor-history case split remains in the statement.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence
open GoertzelV24DegreeTwoExteriorBoundary
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceEnlargementCappedDeletion
open GoertzelV24LowDegreeVertexDeletion
open GoertzelV24RotationFaceExteriorBoundary
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellRebaseExpandedFaceBlockDeletionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The exact finite promoted-block condition implies that deleting every
uniform-interface dart newly promoted from one old strict-exterior component
is non-splitting. -/
theorem sourceLocalLayerSerialCellRebase_promotedFaceInducePreconnected_of_blocks
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (component :
      (exteriorGraph
        (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
            offset))
        (fun slot : Fin
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset).card =>
          ((carrierCoordinate
            (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
              offset)).symm slot).1)).ConnectedComponent)
    {root : web.annular.RS.D} (hroot : root ∈ component.supp)
    (hrootOutside : OutsideInterface
      (fun slot : Fin
        (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
          offset).card =>
        ((carrierCoordinate
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset)).symm slot).1) root)
    (hblocks :
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
        hunique offset hnext hcell).PromotedBlocksMeetOld) :
    let graph := faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let oldDartAt := fun slot : Fin oldCarrier.card =>
      ((carrierCoordinate oldCarrier).symm slot).1
    let newDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
      hunique offset hnext
    (component.toSimpleGraph.induce
      (↑(promotedExteriorComponentVertices graph oldDartAt newDartAt
        component) : Set component)ᶜ).Preconnected := by
  dsimp only
  classical
  let region := sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
    offset
  let graph := faceRegionalDartGraph web.annular.RS region
  let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
    hunique offset
  let uniform := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let oldDartAt := fun slot : Fin oldCarrier.card =>
    ((carrierCoordinate oldCarrier).symm slot).1
  let newDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  let promoted := promotedExteriorComponentVertices graph oldDartAt newDartAt
    component
  let state :=
    sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
      hunique offset hnext hcell
  have houtsideOfNotMem : ∀ {dart : web.annular.RS.D},
      dart ∉ oldCarrier → OutsideInterface oldDartAt dart := by
    intro dart hnot slot heq
    apply hnot
    have hslot : ((carrierCoordinate oldCarrier).symm slot).1 ∈ oldCarrier :=
      ((carrierCoordinate oldCarrier).symm slot).2
    rw [heq]
    exact hslot
  apply promotedExteriorComponentInducePreconnected_of_boundaryBlocks_or_erased
    graph oldDartAt newDartAt component hroot hrootOutside
  · intro dart
    exact faceRegionalDartGraph_neighborSet_ncard_le_two web.annular.RS region
      dart
  · by_cases hallPresent : ∀ vertex : component, vertex ∈ promoted →
        web.annular.RS.edgeOf vertex.1 ∈ region
    · left
      intro block
      let start : {vertex // vertex ∈ promoted} :=
        Classical.choose block.nonempty_supp
      have hstartBlock : start ∈ block.supp :=
        Classical.choose_spec block.nonempty_supp
      have hstartPromoted : start.1 ∈ promoted := start.2
      rcases (mem_promotedExteriorComponentVertices_iff graph oldDartAt
          newDartAt component start.1).1 hstartPromoted with
        ⟨uniformSlot, huniformSlot⟩
      have hcomponentRoot :
          (exteriorGraph graph oldDartAt).connectedComponentMk root =
            component :=
        (component.mem_supp_iff root).1 hroot
      have hcomponentStart :
          (exteriorGraph graph oldDartAt).connectedComponentMk start.1.1 =
            component :=
        (component.mem_supp_iff start.1.1).1 start.1.2
      have hrootStart :
          (exteriorGraph graph oldDartAt).Reachable root start.1.1 :=
        SimpleGraph.ConnectedComponent.exact
          (hcomponentRoot.trans hcomponentStart.symm)
      have hstartOutside : OutsideInterface oldDartAt start.1.1 :=
        outsideInterface_of_exteriorGraph_reachable graph oldDartAt
          hrootOutside hrootStart
      have hstartNotOld : start.1.1 ∉ oldCarrier := by
        intro hold
        let oldSlot := carrierCoordinate oldCarrier ⟨start.1.1, hold⟩
        exact hstartOutside oldSlot (by simp [oldDartAt, oldSlot])
      let occurrence :=
        sourceLocalLayerSerialCellRebaseExpandedFaceSourceAt corridor hunique
          offset hnext hcell uniformSlot
      have hdecodeOccurrence :
          sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor
              hunique offset hnext hcell occurrence = some start.1.1 := by
        have hdecode :=
          sourceLocalLayerSerialCellRebaseExpandedFaceSourceAt_dart_eq corridor
            hunique offset hnext hcell uniformSlot
        rw [← huniformSlot]
        exact hdecode
      have hoccurrencePromoted : state.promoted occurrence = true :=
        (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_promoted_iff_of_decode
          corridor hunique offset hnext hcell occurrence start.1.1
            hdecodeOccurrence).2
          ⟨hallPresent start.1 hstartPromoted, hstartNotOld⟩
      let receiptStart :
          SourceLocalLayerSerialCellRebaseExpandedFacePromotedSlot state :=
        ⟨occurrence, hoccurrencePromoted⟩
      rcases hblocks receiptStart with
        ⟨receiptEndpoint, hreceiptReachable, hendpointOld⟩
      let endpointDart :=
        sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
          hunique offset hnext hcell receiptEndpoint
      have hreceiptStartDart :
          sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt corridor
              hunique offset hnext hcell receiptStart = start.1.1 := by
        have hspec :=
          sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_spec
            corridor hunique offset hnext hcell receiptStart
        rw [hdecodeOccurrence] at hspec
        exact Option.some.inj hspec.symm
      have hambientPromotedReachable :=
        sourceLocalLayerSerialCellRebaseExpandedFace_promotedBlock_reachable
          corridor hunique offset hnext hcell receiptStart receiptEndpoint
            hreceiptReachable
      let kept : Set web.annular.RS.D :=
        {dart |
          web.annular.RS.edgeOf dart ∈ region ∧
            dart ∉ oldCarrier ∧ dart ∈ uniform}
      let promotedAmbient :=
        sourceLocalLayerSerialCellRebasePromotedFaceGraphAt corridor hunique
          offset hnext
      let promotedToExterior : promotedAmbient →g exteriorGraph graph oldDartAt :=
        { toFun := fun vertex => vertex.1
          map_rel' := by
            intro left right hadj
            exact ⟨hadj,
              houtsideOfNotMem left.2.2.1,
              houtsideOfNotMem right.2.2.1⟩ }
      let promotedToExteriorKept :
          promotedAmbient →g (exteriorGraph graph oldDartAt).induce kept :=
        { toFun := fun vertex => ⟨vertex.1, by exact vertex.2⟩
          map_rel' := by
            intro left right hadj
            exact ⟨hadj,
              houtsideOfNotMem left.2.2.1,
              houtsideOfNotMem right.2.2.1⟩ }
      have hkeptAmbientReachable :=
        hambientPromotedReachable.map promotedToExteriorKept
      have hexteriorReachable :
          (exteriorGraph graph oldDartAt).Reachable start.1.1 endpointDart := by
        have hmapped := hambientPromotedReachable.map promotedToExterior
        have hstartMap :
            promotedToExterior
                (sourceLocalLayerSerialCellRebaseExpandedFacePromotedVertexAt
                  corridor hunique offset hnext hcell receiptStart) =
              start.1.1 := by
          exact hreceiptStartDart
        have hendpointMap :
            promotedToExterior
                (sourceLocalLayerSerialCellRebaseExpandedFacePromotedVertexAt
                  corridor hunique offset hnext hcell receiptEndpoint) =
              endpointDart := rfl
        rw [hstartMap, hendpointMap] at hmapped
        exact hmapped
      have hendpointComponent : endpointDart ∈ component.supp := by
        apply (component.mem_supp_iff endpointDart).2
        exact (SimpleGraph.ConnectedComponent.sound hexteriorReachable).symm.trans
          hcomponentStart
      have hendpointUniform : endpointDart ∈ uniform :=
        (sourceLocalLayerSerialCellRebaseExpandedFacePromotedVertexAt corridor
          hunique offset hnext hcell receiptEndpoint).2.2.2
      let endpointUniformSlot := carrierCoordinate uniform
        ⟨endpointDart, hendpointUniform⟩
      have hendpointPromoted :
          (⟨endpointDart, hendpointComponent⟩ : component) ∈ promoted := by
        apply (mem_promotedExteriorComponentVertices_iff graph oldDartAt
          newDartAt component ⟨endpointDart, hendpointComponent⟩).2
        refine ⟨endpointUniformSlot, ?_⟩
        simp [newDartAt,
          sourceLocalLayerSerialCellRebaseUniformFaceDartAt,
          endpointUniformSlot, uniform]
      let endpoint : {vertex // vertex ∈ promoted} :=
        ⟨⟨endpointDart, hendpointComponent⟩, hendpointPromoted⟩
      have hreceiptStartComponent :
          (sourceLocalLayerSerialCellRebaseExpandedFacePromotedVertexAt corridor
            hunique offset hnext hcell receiptStart).1 ∈ component.supp := by
        simp [sourceLocalLayerSerialCellRebaseExpandedFacePromotedVertexAt,
          hreceiptStartDart]
      have hkeptReachable :=
        induce_reachable_lift_connectedComponent component kept
          (sourceLocalLayerSerialCellRebaseExpandedFacePromotedVertexAt corridor
            hunique offset hnext hcell receiptStart)
          (sourceLocalLayerSerialCellRebaseExpandedFacePromotedVertexAt corridor
            hunique offset hnext hcell receiptEndpoint)
          hreceiptStartComponent hendpointComponent hkeptAmbientReachable
      let keptToPromoted :
          (component.toSimpleGraph.induce
              {vertex : component | vertex.1 ∈ kept}) →g
            (component.toSimpleGraph.induce
              (↑promoted : Set component)) :=
        { toFun := fun vertex =>
            ⟨vertex.1, by
              apply (mem_promotedExteriorComponentVertices_iff graph oldDartAt
                newDartAt component vertex.1).2
              let slot := carrierCoordinate uniform
                ⟨vertex.1.1, vertex.2.2.2⟩
              refine ⟨slot, ?_⟩
              simp [newDartAt,
                sourceLocalLayerSerialCellRebaseUniformFaceDartAt,
                slot, uniform]⟩
          map_rel' := by
            intro left right hadj
            exact hadj }
      have hcomponentPromotedReachable :
          (component.toSimpleGraph.induce (↑promoted : Set component)
            ).Reachable start endpoint := by
        have hmapped := hkeptReachable.map keptToPromoted
        have hstartMap :
            keptToPromoted
                ⟨⟨(sourceLocalLayerSerialCellRebaseExpandedFacePromotedVertexAt
                  corridor hunique offset hnext hcell receiptStart).1,
                    hreceiptStartComponent⟩,
                  (sourceLocalLayerSerialCellRebaseExpandedFacePromotedVertexAt
                    corridor hunique offset hnext hcell receiptStart).2⟩ =
              start := by
          apply Subtype.ext
          apply Subtype.ext
          exact hreceiptStartDart
        have hendpointMap :
            keptToPromoted
                ⟨⟨(sourceLocalLayerSerialCellRebaseExpandedFacePromotedVertexAt
                  corridor hunique offset hnext hcell receiptEndpoint).1,
                    hendpointComponent⟩,
                  (sourceLocalLayerSerialCellRebaseExpandedFacePromotedVertexAt
                    corridor hunique offset hnext hcell receiptEndpoint).2⟩ =
              endpoint := by
          rfl
        rw [hstartMap, hendpointMap] at hmapped
        exact hmapped
      have hendpointBlock : endpoint ∈ block.supp := by
        apply (block.mem_supp_iff endpoint).2
        have hstartComponent :
            (component.toSimpleGraph.induce (↑promoted : Set component)
              ).connectedComponentMk start = block :=
          (block.mem_supp_iff start).1 hstartBlock
        exact (SimpleGraph.ConnectedComponent.sound hcomponentPromotedReachable
          ).symm.trans hstartComponent
      refine ⟨endpoint, hendpointBlock, ?_⟩
      rcases
          (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_oldNeighbor?_isSome_iff_of_decode
          corridor hunique offset hnext hcell receiptEndpoint.1 endpointDart
            (sourceLocalLayerSerialCellRebaseExpandedFacePromotedDartAt_spec
              corridor hunique offset hnext hcell receiptEndpoint)).1
          hendpointOld with ⟨oldDart, hadj⟩
      refine ⟨carrierCoordinate oldCarrier oldDart, ?_⟩
      simpa [graph, oldDartAt, region] using hadj
    · right
      push Not at hallPresent
      rcases hallPresent with ⟨vertex, hpromoted, hnotPresent⟩
      have hisolatedAmbient : graph.IsIsolated vertex.1 := by
        intro other hadj
        exact hnotPresent hadj.2.2.1
      exact all_mem_promotedExteriorComponentVertices_of_isolated graph
        oldDartAt newDartAt component vertex hpromoted
          (exteriorComponent_isIsolated_of_ambient graph oldDartAt component
            vertex hisolatedAmbient)

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
