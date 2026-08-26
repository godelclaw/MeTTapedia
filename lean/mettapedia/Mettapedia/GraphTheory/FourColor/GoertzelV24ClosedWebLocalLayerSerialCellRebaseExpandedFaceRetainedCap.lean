import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseExpandedFaceBlockDeletion
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLayerSeparation
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebInteriorFaceGeometry
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceEnlargementRetainedLabels

/-!
# Retained exterior labels across the literal facial Cell rebase

The literal Cell rebase enlarges the rolling facial interface and masks the
four switch-edge occurrences.  This file identifies the strict-exterior graph
on the enlarged interface and specializes the generic retained-label theorem
to the forty-eight-dart occurrence receipt.

The label invariant is deliberately occurrence-safe.  A primal edge label is
removed only when it has no retained dart occurrence in the old exterior
component.  No global two-sidedness or injectivity of `edgeOf` is assumed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence
open GoertzelV24DegreeTwoExteriorBoundary
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorMaskUpdate
open GoertzelV24InterfaceDeletionComponentFactorUpdate
open GoertzelV24InterfaceEnlargementCappedDeletion
open GoertzelV24InterfaceEnlargementRetainedLabels
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellRebaseExpandedFaceRetainedCapEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- Every face incident to an incoming crossing of a literal Cell is an
annular-interior face.  The crossed edge places the face in the local dual
walk, whose whole support is internal. -/
theorem sourceLocalLayerLeftCrossingAt_incidentFace_internal
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (step : Fin 2)
    (face : OrbitFace web.annular.RS)
    (hface : sourceLocalLayerLeftCrossingAt corridor hunique offset step ∈
      orbitFaceBoundary web.annular.RS face) :
    face ∈ web.annular.cellulation.interiorFaces := by
  let layers := sourceLocalLayerPairAt corridor hunique offset
  let crossingStep : Fin layers.firstLayer.walk.length :=
    ⟨step.val, by
      simpa [LocalLayerPair.firstLayer, LocalLayerPair.firstWalk] using
        step.isLt⟩
  have hedge : sourceLocalLayerLeftCrossingAt corridor hunique offset step ∈
      layers.firstLayer.crossingEdges hunique := by
    apply (layers.firstLayer.mem_crossingEdges_iff hunique _).2
    refine ⟨crossingStep, ?_⟩
    simp [sourceLocalLayerLeftCrossingAt, layers, crossingStep]
  have hsupport :
      (⟨face, Finset.mem_univ face⟩ : AmbientFace
        (Finset.univ : Finset (OrbitFace web.annular.RS))) ∈
        layers.firstLayer.walk.support :=
    layers.firstLayer.face_mem_walk_support_of_mem_crossingEdge_of_mem_boundary
      hunique hedge hface
  apply layers.localLayerLoop_support_internal
    ⟨face, Finset.mem_univ face⟩
  change (⟨face, Finset.mem_univ face⟩ : AmbientFace
    (Finset.univ : Finset (OrbitFace web.annular.RS))) ∈
      layers.localLayerLoop.support
  simp only [LocalLayerPair.localLayerLoop,
    SimpleGraph.Walk.support_append, List.mem_append]
  exact Or.inl hsupport

/-- Every face incident to the shared outgoing corridor rung of a literal
Cell is internal.  The global at-most-two incidence bound leaves only the two
consecutive corridor faces, both of which are boundary-clean. -/
theorem sourceLocalLayerSharedRungAt_incidentFace_internal
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (face : OrbitFace web.annular.RS)
    (hface : sourceLocalLayerSharedRungAt corridor hunique offset ∈
      orbitFaceBoundary web.annular.RS face) :
    face ∈ web.annular.cellulation.interiorFaces := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let rung := (sourceLocalLayerInteriorAt offset).outgoing
  let left := skeleton.faceAt rung.left
  let right := skeleton.faceAt rung.right
  have hleftRight : left.1 ≠ right.1 := by
    intro heq
    exact (skeleton.consecutive_adjacent rung.left rung.right rfl).ne
      (Subtype.ext heq)
  have hleft : sourceLocalLayerSharedRungAt corridor hunique offset ∈
      orbitFaceBoundary web.annular.RS left.1 := by
    simpa [sourceLocalLayerSharedRungAt, skeleton, rung, left] using
      skeleton.rungEdge_mem_left hunique rung
  have hright : sourceLocalLayerSharedRungAt corridor hunique offset ∈
      orbitFaceBoundary web.annular.RS right.1 := by
    simpa [sourceLocalLayerSharedRungAt, skeleton, rung, right] using
      skeleton.rungEdge_mem_right hunique rung
  have hcases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (orbitFace_incidence_le_two web.annular.RS) left.2 right.2
      (Finset.mem_univ face) hleftRight hleft hright hface
  rcases hcases with rfl | rfl
  · exact corridor.face_internal rung.left
  · exact corridor.face_internal rung.right

/-- Every face incident to one of the four literal rebase-switch edges is
annular-interior.  This is the role-by-role geometric fact needed below; it
uses neither global face two-sidedness nor a closed-carrier hypothesis. -/
theorem sourceLocalLayerBoundaryRebaseSwitchAt_incidentFace_internal
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (edge : G.edgeSet) (face : OrbitFace web.annular.RS)
    (hedge : edge ∈ sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique
      offset hnext)
    (hface : edge ∈ orbitFaceBoundary web.annular.RS face) :
    face ∈ web.annular.cellulation.interiorFaces := by
  rcases (mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff corridor hunique
    offset hnext edge).1 hedge with ⟨role, rfl⟩
  rcases role with role | role
  · exact sourceLocalLayerSharedRungAt_incidentFace_internal corridor hunique
      offset face (by
        simpa [sourceLocalLayerBoundaryRebaseEdgeAt] using hface)
  · rcases role with step | role
    · exact sourceLocalLayerLeftCrossingAt_incidentFace_internal corridor
        hunique (sourceLocalLayerNextOffset offset hnext) step face (by
          simpa [sourceLocalLayerBoundaryRebaseEdgeAt] using hface)
    · exact sourceLocalLayerSharedRungAt_incidentFace_internal corridor hunique
        (sourceLocalLayerNextOffset offset hnext) face (by
          simpa [sourceLocalLayerBoundaryRebaseEdgeAt] using hface)

/-- The orbit face of every changed dart occurrence is interior. -/
theorem sourceLocalLayerBoundaryRebaseChangedFaceDartAt_face_internal
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (dart : web.annular.RS.D)
    (hdart : dart ∈ sourceLocalLayerBoundaryRebaseChangedFaceDartsAt
      corridor hunique offset hnext) :
    dartOrbitFace web.annular.RS dart ∈
      web.annular.cellulation.interiorFaces := by
  apply sourceLocalLayerBoundaryRebaseSwitchAt_incidentFace_internal corridor
    hunique offset hnext (web.annular.RS.edgeOf dart)
      (dartOrbitFace web.annular.RS dart)
  · exact (mem_sourceLocalLayerBoundaryRebaseChangedFaceDartsAt_iff corridor
      hunique offset hnext dart).1 hdart
  · rw [mem_orbitFaceBoundary_iff]
    exact ⟨dart,
      (mem_orbitFaceDarts_iff web.annular.RS
        (dartOrbitFace web.annular.RS dart) dart).2 rfl,
      rfl⟩

/-- The whole one-step facial collar remains on interior orbit faces. -/
theorem sourceLocalLayerBoundaryRebaseFaceCollarAt_face_internal
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (dart : web.annular.RS.D)
    (hdart : dart ∈ sourceLocalLayerBoundaryRebaseFaceCollarAt corridor
      hunique offset hnext) :
    dartOrbitFace web.annular.RS dart ∈
      web.annular.cellulation.interiorFaces := by
  rw [sourceLocalLayerBoundaryRebaseFaceCollarAt, Finset.mem_biUnion] at hdart
  rcases hdart with ⟨changed, hchanged, hdart⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdart
  rcases hdart with hdart | hdart | hdart
  · subst dart
    exact sourceLocalLayerBoundaryRebaseChangedFaceDartAt_face_internal
      corridor hunique offset hnext changed hchanged
  · subst dart
    rw [dartOrbitFace_phi_eq]
    exact sourceLocalLayerBoundaryRebaseChangedFaceDartAt_face_internal corridor
      hunique offset hnext changed hchanged
  · subst dart
    have hface :=
      (sourceLocalLayerBoundaryRebaseChangedFaceDartAt_face_internal corridor
        hunique offset hnext changed hchanged)
    have hsame := dartOrbitFace_phi_eq web.annular.RS
      (web.annular.RS.phi.symm changed)
    have hsame' : dartOrbitFace web.annular.RS changed =
        dartOrbitFace web.annular.RS (web.annular.RS.phi.symm changed) := by
      simpa using hsame
    rw [← hsame']
    exact hface

/-- Every predecessor facial-interface dart has a coordinate in the enlarged
uniform facial interface. -/
theorem sourceLocalLayerSerialCellRebase_oldFaceDartAt_covered_uniform
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let oldDartAt := fun slot : Fin oldCarrier.card =>
      ((carrierCoordinate oldCarrier).symm slot).1
    let newDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
      hunique offset hnext
    ∀ old, ∃ new, newDartAt new = oldDartAt old := by
  dsimp only
  intro old
  let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
    hunique offset
  let uniform := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let oldDartAt := fun slot : Fin oldCarrier.card =>
    ((carrierCoordinate oldCarrier).symm slot).1
  have holdMem : oldDartAt old ∈ uniform := by
    apply Finset.mem_union_left
    exact ((carrierCoordinate oldCarrier).symm old).2
  refine ⟨carrierCoordinate uniform ⟨oldDartAt old, holdMem⟩, ?_⟩
  simp [sourceLocalLayerSerialCellRebaseUniformFaceDartAt, uniform, oldDartAt,
    oldCarrier]

/-- On the enlarged uniform interface, the literal successor and the
cumulative pre-rebase facial graph have exactly the same strict exterior.

The four switch occurrences are on the interface, so masking them cannot
change the strict exterior.  The genuinely local successor residue is also
supported on the interface, so adjoining it cannot change that exterior. -/
theorem sourceLocalLayerSerialCellRebase_exteriorGraph_successor_eq_preRebase
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    let newDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
      hunique offset hnext
    let preRebase := faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    exteriorGraph
        (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique
          offset hnext) newDartAt =
      exteriorGraph preRebase newDartAt := by
  dsimp only
  let uniform := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let newDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  let preRebase := faceRegionalDartGraph web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
  let core := sourceLocalLayerBoundaryRebaseCoreFaceGraphAt corridor hunique
    offset hnext
  let localGraph := sourceLocalLayerBoundaryRebaseLocalFaceGraphAt corridor hunique
    offset hnext
  have hlocalSupport : localGraph.support ⊆ Set.range newDartAt := by
    intro dart hdart
    have hmem : dart ∈ uniform :=
      (sourceLocalLayerSerialCell_faceRebase_support_subset_uniformInterface
        corridor hunique offset hnext).2 hdart
    refine ⟨carrierCoordinate uniform ⟨dart, hmem⟩, ?_⟩
    simp [newDartAt, sourceLocalLayerSerialCellRebaseUniformFaceDartAt, uniform]
  rw [← sourceLocalLayerBoundaryRebaseCore_sup_local_eq_successor corridor
    hunique offset hnext]
  rw [exteriorGraph_sup_eq_left_of_right_support_subset_interface core localGraph
    newDartAt hlocalSupport]
  change exteriorGraph
      (sourceLocalLayerBoundaryRebaseCoreFaceGraphAt corridor hunique offset
        hnext) newDartAt =
    exteriorGraph preRebase newDartAt
  rw [← restrictedPreRebaseFaceGraph_uniformSwitchMask_eq_core corridor
    hunique offset hnext]
  exact exteriorGraph_restrictedByMask_eq preRebase newDartAt
    (sourceLocalLayerSerialCellRebaseUniformFaceSwitchMaskAt corridor hunique
      offset hnext)

/-- If one old exterior component is touched by the enlarged facial
interface, then its dart-to-edge labelling is injective.  A promoted dart lies
in the bounded face collar, hence on an interior face.  Regional
reachability keeps the whole component on that face, whose source-certified
simple boundary forbids a repeated primal edge. -/
theorem
    sourceLocalLayerSerialCellRebase_edgeOf_injective_of_promoted_nonempty
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
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
    (root : component)
    (hrootOutside : OutsideInterface
      (fun slot : Fin
        (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
          offset).card =>
        ((carrierCoordinate
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset)).symm slot).1)
      root.1)
    (hpromoted : (promotedExteriorComponentVertices
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset))
      (fun slot : Fin
        (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
          offset).card =>
        ((carrierCoordinate
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset)).symm slot).1)
      (sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique offset
        hnext) component).Nonempty) :
    Function.Injective (fun vertex : component =>
      web.annular.RS.edgeOf vertex.1) := by
  classical
  let region :=
    sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset
  let graph := faceRegionalDartGraph web.annular.RS region
  let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
    hunique offset
  let oldDartAt := fun slot : Fin oldCarrier.card =>
    ((carrierCoordinate oldCarrier).symm slot).1
  let uniform := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let newDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  rcases hpromoted with ⟨promoted, hpromoted⟩
  rcases (mem_promotedExteriorComponentVertices_iff graph oldDartAt newDartAt
    component promoted).1 hpromoted with ⟨newSlot, hnewSlot⟩
  have hrootComponent :
      (exteriorGraph graph oldDartAt).connectedComponentMk root.1 = component :=
    (component.mem_supp_iff root.1).1 root.2
  have hpromotedReach :
      (exteriorGraph graph oldDartAt).Reachable root.1 promoted.1 := by
    apply SimpleGraph.ConnectedComponent.exact
    exact hrootComponent.trans
      ((component.mem_supp_iff promoted.1).1 promoted.2).symm
  have hpromotedOutside : OutsideInterface oldDartAt promoted.1 :=
    outsideInterface_of_exteriorGraph_reachable graph oldDartAt hrootOutside
      hpromotedReach
  have hpromotedUniform : promoted.1 ∈ uniform := by
    have hcoordinate : newDartAt newSlot ∈ uniform := by
      exact ((carrierCoordinate uniform).symm newSlot).2
    simpa [newDartAt,
      sourceLocalLayerSerialCellRebaseUniformFaceDartAt, uniform, hnewSlot]
      using hcoordinate
  have hpromotedCollar : promoted.1 ∈
      sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset
        hnext := by
    rcases Finset.mem_union.mp hpromotedUniform with hold | hcollar
    · exact (hpromotedOutside
        (carrierCoordinate oldCarrier ⟨promoted.1, hold⟩) (by
          simp [oldDartAt, oldCarrier])).elim
    · exact hcollar
  have hpromotedFace : dartOrbitFace web.annular.RS promoted.1 ∈
      web.annular.cellulation.interiorFaces :=
    sourceLocalLayerBoundaryRebaseFaceCollarAt_face_internal corridor hunique
      offset hnext promoted.1 hpromotedCollar
  intro left right hedge
  have hleftReach : (exteriorGraph graph oldDartAt).Reachable promoted.1
      left.1 := by
    apply SimpleGraph.ConnectedComponent.exact
    exact ((component.mem_supp_iff promoted.1).1 promoted.2).trans
      ((component.mem_supp_iff left.1).1 left.2).symm
  have hrightReach : (exteriorGraph graph oldDartAt).Reachable promoted.1
      right.1 := by
    apply SimpleGraph.ConnectedComponent.exact
    exact ((component.mem_supp_iff promoted.1).1 promoted.2).trans
      ((component.mem_supp_iff right.1).1 right.2).symm
  have hexteriorLe : exteriorGraph graph oldDartAt ≤ graph := by
    intro first second hadj
    exact hadj.1
  have hleftFace : dartOrbitFace web.annular.RS promoted.1 =
      dartOrbitFace web.annular.RS left.1 :=
    faceRegionalDartGraph_reachable_dartOrbitFace_eq web.annular.RS region
      (hleftReach.mono hexteriorLe)
  have hrightFace : dartOrbitFace web.annular.RS promoted.1 =
      dartOrbitFace web.annular.RS right.1 :=
    faceRegionalDartGraph_reachable_dartOrbitFace_eq web.annular.RS region
      (hrightReach.mono hexteriorLe)
  have hinjective : Set.InjOn web.annular.RS.edgeOf
      (orbitFaceDarts web.annular.RS
        (dartOrbitFace web.annular.RS promoted.1)) := by
    apply Finset.card_image_iff.mp
    exact InteriorFace.boundary_card_eq_darts_card web promoted.1
      hpromotedFace
  apply Subtype.ext
  exact hinjective
    ((mem_orbitFaceDarts_iff web.annular.RS
      (dartOrbitFace web.annular.RS promoted.1) left.1).2 hleftFace.symm)
    ((mem_orbitFaceDarts_iff web.annular.RS
      (dartOrbitFace web.annular.RS promoted.1) right.1).2 hrightFace.symm)
    hedge

/-- A finite promoted-block receipt identifies the successor exterior
component rooted at any retained predecessor dart: its distinct primal-edge
labels are exactly the retained labels of the old component. -/
theorem
    sourceLocalLayerSerialCellRebase_exteriorComponentLabelSupport_eq_retained
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
    (start : component)
    (hstartRetained : start ∈ retainedExteriorComponentVertices
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset))
      (fun slot : Fin
        (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
          offset).card =>
        ((carrierCoordinate
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset)).symm slot).1)
      (sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique offset
        hnext) component)
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
    exteriorComponentLabelSupport graph newDartAt web.annular.RS.edgeOf
        ((exteriorGraph graph newDartAt).connectedComponentMk start.1) =
      retainedExteriorComponentLabels graph oldDartAt newDartAt
        web.annular.RS.edgeOf component := by
  dsimp only
  let graph := faceRegionalDartGraph web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
  let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
    hunique offset
  let oldDartAt := fun slot : Fin oldCarrier.card =>
    ((carrierCoordinate oldCarrier).symm slot).1
  let newDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  have holdCovered : ∀ old, ∃ new, newDartAt new = oldDartAt old :=
    sourceLocalLayerSerialCellRebase_oldFaceDartAt_covered_uniform corridor
      hunique offset hnext
  have hstartOutsideOld : OutsideInterface oldDartAt start.1 := by
    have hnotNew : ¬ ∃ slot, newDartAt slot = start.1 :=
      (mem_retainedExteriorComponentVertices_iff graph oldDartAt newDartAt
        component start).1 hstartRetained
    intro old heq
    rcases holdCovered old with ⟨new, hnew⟩
    exact hnotNew ⟨new, hnew.trans heq.symm⟩
  have hpreconnected :
      (component.toSimpleGraph.induce
        (↑(promotedExteriorComponentVertices graph oldDartAt newDartAt
          component) : Set component)ᶜ).Preconnected :=
    sourceLocalLayerSerialCellRebase_promotedFaceInducePreconnected_of_blocks
      corridor hunique offset hnext hcell component start.2 hstartOutsideOld
        hblocks
  exact exteriorComponentLabelSupport_eq_retained_of_preconnected graph
    oldDartAt newDartAt web.annular.RS.edgeOf holdCovered component start
      hstartRetained hpreconnected

/-- The old cap at fifty-three and the exact set of completely lost primal
edge labels determine the retained cap at five.  Unlike promoted-label
subtraction, this remains exact when one primal edge has both a promoted and a
retained dart occurrence in the old face component. -/
theorem sourceLocalLayerSerialCellRebase_min_retainedFaceLabels_five_eq_lost
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
              offset)).symm slot).1)).ConnectedComponent) :
    let graph := faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let oldDartAt := fun slot : Fin oldCarrier.card =>
      ((carrierCoordinate oldCarrier).symm slot).1
    let newDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
      hunique offset hnext
    min (retainedExteriorComponentLabels graph oldDartAt newDartAt
        web.annular.RS.edgeOf component).card 5 =
      min (min (exteriorComponentLabelSupport graph oldDartAt
          web.annular.RS.edgeOf component).card 53 -
        (lostExteriorComponentLabels graph oldDartAt newDartAt
          web.annular.RS.edgeOf component).card) 5 := by
  dsimp only
  let uniform := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let graph := faceRegionalDartGraph web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
  let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
    hunique offset
  let oldDartAt := fun slot : Fin oldCarrier.card =>
    ((carrierCoordinate oldCarrier).symm slot).1
  let newDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  have hcover : ∀ vertex : component,
      (∃ slot, newDartAt slot = vertex.1) →
        ∃ added : Fin uniform.card, newDartAt added = vertex.1 := by
    intro vertex hvertex
    exact hvertex
  have hcard : Fintype.card (Fin uniform.card) ≤ 48 := by
    simpa [uniform] using
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt_card_le_fortyEight_of_cell
        corridor hunique offset hnext hcell)
  simpa using
    (min_card_retainedExteriorComponentLabels_five_eq_lost_of_card_added_le
      graph oldDartAt newDartAt newDartAt web.annular.RS.edgeOf component 48
        hcover hcard)

/-- Exact cap-five recurrence for a retained-root exterior component.  The
finite promoted-block condition supplies non-splitting; the arithmetic uses
the cap at fifty-three and subtracts only completely lost edge labels. -/
theorem sourceLocalLayerSerialCellRebase_min_newExteriorFaceSupport_five_eq
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
    (start : component)
    (hstartRetained : start ∈ retainedExteriorComponentVertices
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset))
      (fun slot : Fin
        (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
          offset).card =>
        ((carrierCoordinate
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset)).symm slot).1)
      (sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique offset
        hnext) component)
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
    min (exteriorComponentLabelSupport graph newDartAt web.annular.RS.edgeOf
        ((exteriorGraph graph newDartAt).connectedComponentMk start.1)).card 5 =
      min (min (exteriorComponentLabelSupport graph oldDartAt
          web.annular.RS.edgeOf component).card 53 -
        (lostExteriorComponentLabels graph oldDartAt newDartAt
          web.annular.RS.edgeOf component).card) 5 := by
  dsimp only
  rw [sourceLocalLayerSerialCellRebase_exteriorComponentLabelSupport_eq_retained
    corridor hunique offset hnext hcell component start hstartRetained hblocks]
  exact sourceLocalLayerSerialCellRebase_min_retainedFaceLabels_five_eq_lost
    corridor hunique offset hnext hcell component

/-- Executable cap-five recurrence in terms of the finite set of promoted
edge labels.  If promotion touches the component, local interior-face
simplicity supplies label injectivity.  If it does not, both the promoted and
completely-lost label sets are empty. -/
theorem
    sourceLocalLayerSerialCellRebase_min_newExteriorFaceSupport_five_eq_promoted
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
    (start : component)
    (hstartRetained : start ∈ retainedExteriorComponentVertices
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset))
      (fun slot : Fin
        (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
          offset).card =>
        ((carrierCoordinate
          (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset)).symm slot).1)
      (sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique offset
        hnext) component)
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
    min (exteriorComponentLabelSupport graph newDartAt web.annular.RS.edgeOf
        ((exteriorGraph graph newDartAt).connectedComponentMk start.1)).card 5 =
      min (min (exteriorComponentLabelSupport graph oldDartAt
          web.annular.RS.edgeOf component).card 53 -
        (promotedExteriorComponentLabels graph oldDartAt newDartAt
          web.annular.RS.edgeOf component).card) 5 := by
  dsimp only
  classical
  let graph := faceRegionalDartGraph web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
  let oldCarrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
    hunique offset
  let oldDartAt := fun slot : Fin oldCarrier.card =>
    ((carrierCoordinate oldCarrier).symm slot).1
  let uniform := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let newDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor
    hunique offset hnext
  rw [sourceLocalLayerSerialCellRebase_exteriorComponentLabelSupport_eq_retained
    corridor hunique offset hnext hcell component start hstartRetained hblocks]
  have holdCovered : ∀ old, ∃ new, newDartAt new = oldDartAt old :=
    sourceLocalLayerSerialCellRebase_oldFaceDartAt_covered_uniform corridor
      hunique offset hnext
  have hcover : ∀ vertex : component,
      (∃ slot, newDartAt slot = vertex.1) →
        ∃ added : Fin uniform.card, newDartAt added = vertex.1 := by
    intro vertex hvertex
    exact hvertex
  have hcard : Fintype.card (Fin uniform.card) ≤ 48 := by
    simpa [uniform] using
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt_card_le_fortyEight_of_cell
        corridor hunique offset hnext hcell)
  by_cases hpromoted : (promotedExteriorComponentVertices graph oldDartAt
      newDartAt component).Nonempty
  · have hnotNew : ¬ ∃ slot, newDartAt slot = start.1 :=
      (mem_retainedExteriorComponentVertices_iff graph oldDartAt newDartAt
        component start).1 hstartRetained
    have hstartOutside : OutsideInterface oldDartAt start.1 := by
      intro old heq
      rcases holdCovered old with ⟨new, hnew⟩
      exact hnotNew ⟨new, hnew.trans heq.symm⟩
    have hinjective : Function.Injective (fun vertex : component =>
        web.annular.RS.edgeOf vertex.1) :=
      sourceLocalLayerSerialCellRebase_edgeOf_injective_of_promoted_nonempty
        corridor hunique offset hnext component start hstartOutside hpromoted
    exact min_card_retainedExteriorComponentLabels_five_eq_of_card_added_le
      graph oldDartAt newDartAt newDartAt web.annular.RS.edgeOf component 48
        hinjective hcover hcard
  · have hpromotedVerticesEmpty :
        promotedExteriorComponentVertices graph oldDartAt newDartAt component =
          ∅ := Finset.not_nonempty_iff_eq_empty.mp hpromoted
    have hpromotedLabelsEmpty :
        promotedExteriorComponentLabels graph oldDartAt newDartAt
          web.annular.RS.edgeOf component = ∅ := by
      simp [promotedExteriorComponentLabels, hpromotedVerticesEmpty]
    have hlostEmpty : lostExteriorComponentLabels graph oldDartAt newDartAt
        web.annular.RS.edgeOf component = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨value, hvalue⟩
      have hsubset := lostExteriorComponentLabels_subset_promotedExteriorComponentLabels
        graph oldDartAt newDartAt web.annular.RS.edgeOf component hvalue
      rw [hpromotedLabelsEmpty] at hsubset
      simp at hsubset
    calc
      min (retainedExteriorComponentLabels graph oldDartAt newDartAt
          web.annular.RS.edgeOf component).card 5 =
          min (min (exteriorComponentLabelSupport graph oldDartAt
            web.annular.RS.edgeOf component).card 53 -
            (lostExteriorComponentLabels graph oldDartAt newDartAt
              web.annular.RS.edgeOf component).card) 5 :=
        min_card_retainedExteriorComponentLabels_five_eq_lost_of_card_added_le
          graph oldDartAt newDartAt newDartAt web.annular.RS.edgeOf component
            48 hcover hcard
      _ = min (min (exteriorComponentLabelSupport graph oldDartAt
            web.annular.RS.edgeOf component).card 53 -
          (promotedExteriorComponentLabels graph oldDartAt newDartAt
            web.annular.RS.edgeOf component).card) 5 := by
        rw [hlostEmpty, hpromotedLabelsEmpty]

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
