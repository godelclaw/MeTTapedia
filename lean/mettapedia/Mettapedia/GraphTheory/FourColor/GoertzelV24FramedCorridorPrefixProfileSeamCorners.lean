import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorCanonicalInterface
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileSeam

/-!
# Source coordinates of a corridor-prefix seam

The two crossings of each source layer are selected abstractly as the unique
primal edges attached to its two facial-dual steps.  A corner-aligned source
interface identifies those four choices with the literal side edges before
and after the shared rung, and with the two third edges at the rung endpoints.

This is the coordinate layer needed to describe the residual term in the
one-Cell profile update.  No coverage or determinism statement is made here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorColorTransfer
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexCorridorSlab
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrientedHexSlab
open GoertzelV24TerminalProfileSeamResidual
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance corridorPrefixProfileSeamCornersEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceCornerAlignedSlabInterface

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- A literal side edge is the unique primal edge shared by its central face
and its selected external neighbour. -/
private theorem placementSideEdge_mem_shared
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (position : {position // position ∈ placementSidePositions placement}) :
    (placementSideEdge htwoSided placement position).1 ∈
      sharedInteriorEdges
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))
        (realization.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton.faceAt interior.center).1
        (placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton
          htwoSided hunique placement position).1 := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let corridor := realization.toCleanOrbitHexCorridorSkeleton
    |>.toOrbitHexCorridorSkeleton
  let side := placementSideEdge htwoSided placement position
  have hcenter : side.1 ∈ orbitFaceBoundary RS
      (corridor.faceAt interior.center).1 :=
    ((mem_internalSideEdges_iff corridor hunique interior side.1).1 side.2).1
  let witness := orbitFaceAcrossEdgeWitness RS htwoSided
    (corridor.faceAt interior.center) side.1 hcenter
  apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS))).2
  refine ⟨witness.edge_interior, hcenter, ?_⟩
  exact witness.edge_mem_across

/-- The same literal shared-edge fact with the two incident faces reversed. -/
private theorem placementSideEdge_mem_shared_rev
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (position : {position // position ∈ placementSidePositions placement}) :
    (placementSideEdge htwoSided placement position).1 ∈
      sharedInteriorEdges
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))
        (placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton
          htwoSided hunique placement position).1
        (realization.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton.faceAt interior.center).1 := by
  rw [mem_sharedInteriorEdges_iff]
  have hshared := (mem_sharedInteriorEdges_iff _ _).1
    (placementSideEdge_mem_shared (realization := realization)
      (htwoSided := htwoSided) (hunique := hunique) placement position)
  exact ⟨hshared.1, hshared.2.2, hshared.2.1⟩

/-- The first crossing of the left source layer is its literal side edge
immediately before the outgoing rung. -/
theorem localLayerPrefixCrossing_zero_eq_leftBeforeEdge
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    aligned.toInterface.localLayerPrefixCrossing (0 : Fin 2) =
      aligned.toInterface.leftBeforeEdge.1 := by
  unfold SourceConsecutiveSlabInterface.localLayerPrefixCrossing
    SimpleDualCrosscut.crossingEdge dualWalkCrossingEdge
  apply sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_mem_sharedInteriorEdges
  have hshared := placementSideEdge_mem_shared_rev
    (htwoSided := htwoSided) (hunique := hunique)
    (realization.slabPlacementAt htwoSided hunique leftInterior)
    aligned.toInterface.leftBeforePos
  simpa [SourceConsecutiveSlabInterface.localLayer,
    SourceConsecutiveSlabInterface.localLayerWalk,
    SourceConsecutiveSlabInterface.firstLayerFace,
    SourceConsecutiveSlabInterface.centerLayerFace,
    SourceConsecutiveSlabInterface.leftBeforeEdge] using
    hshared

/-- The second crossing of the left source layer is its literal side edge
immediately after the outgoing rung. -/
theorem localLayerPrefixCrossing_one_eq_leftAfterEdge
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    aligned.toInterface.localLayerPrefixCrossing (1 : Fin 2) =
      aligned.toInterface.leftAfterEdge.1 := by
  unfold SourceConsecutiveSlabInterface.localLayerPrefixCrossing
    SimpleDualCrosscut.crossingEdge dualWalkCrossingEdge
  apply sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_mem_sharedInteriorEdges
  have hshared := placementSideEdge_mem_shared
    (htwoSided := htwoSided) (hunique := hunique)
    (realization.slabPlacementAt htwoSided hunique leftInterior)
    aligned.toInterface.leftAfterPos
  simpa [SourceConsecutiveSlabInterface.localLayer,
    SourceConsecutiveSlabInterface.localLayerWalk,
    SourceConsecutiveSlabInterface.secondLayerFace,
    SourceConsecutiveSlabInterface.centerLayerFace,
    SourceConsecutiveSlabInterface.leftAfterEdge] using hshared

/-- The first crossing of the right source layer is the literal side edge
chosen on the next corridor hexagon. -/
theorem nextLocalLayerPrefixCrossing_zero_eq_rightBeforeEdge
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    aligned.toInterface.nextLocalLayerPrefixCrossing (0 : Fin 2) =
      (placementSideEdge htwoSided
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext))
        aligned.toInterface.rightBeforePos).1 := by
  unfold SourceConsecutiveSlabInterface.nextLocalLayerPrefixCrossing
    SimpleDualCrosscut.crossingEdge dualWalkCrossingEdge
  apply sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_mem_sharedInteriorEdges
  have hshared := placementSideEdge_mem_shared_rev
    (htwoSided := htwoSided) (hunique := hunique)
    (realization.slabPlacementAt htwoSided hunique
      (nextCorridorInterior leftInterior hnext))
    aligned.toInterface.rightBeforePos
  simpa [SourceConsecutiveSlabInterface.nextLocalLayer,
    SourceConsecutiveSlabInterface.nextLocalLayerWalk,
    SourceConsecutiveSlabInterface.nextCenterLayerFace,
    aligned.toInterface.firstLayerFace_eq_next_firstLayerFace] using hshared

/-- The second crossing of the right source layer is the other literal side
edge chosen on the next corridor hexagon. -/
theorem nextLocalLayerPrefixCrossing_one_eq_rightAfterEdge
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    aligned.toInterface.nextLocalLayerPrefixCrossing (1 : Fin 2) =
      (placementSideEdge htwoSided
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext))
        aligned.toInterface.rightAfterPos).1 := by
  unfold SourceConsecutiveSlabInterface.nextLocalLayerPrefixCrossing
    SimpleDualCrosscut.crossingEdge dualWalkCrossingEdge
  apply sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_mem_sharedInteriorEdges
  have hshared := placementSideEdge_mem_shared
    (htwoSided := htwoSided) (hunique := hunique)
    (realization.slabPlacementAt htwoSided hunique
      (nextCorridorInterior leftInterior hnext))
    aligned.toInterface.rightAfterPos
  simpa [SourceConsecutiveSlabInterface.nextLocalLayer,
    SourceConsecutiveSlabInterface.nextLocalLayerWalk,
    SourceConsecutiveSlabInterface.nextCenterLayerFace,
    aligned.toInterface.secondLayerFace_eq_next_secondLayerFace] using hshared

/-- Corner alignment identifies the first right crossing with the actual
third edge at the first endpoint of the shared rung. -/
theorem nextLocalLayerPrefixCrossing_zero_eq_beforeOutgoingCornerEdge
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    aligned.toInterface.nextLocalLayerPrefixCrossing (0 : Fin 2) =
      beforeOutgoingCornerEdge
        (realization.slabPlacementAt htwoSided hunique leftInterior) := by
  calc
    aligned.toInterface.nextLocalLayerPrefixCrossing (0 : Fin 2) =
        (placementSideEdge htwoSided
          (realization.slabPlacementAt htwoSided hunique
            (nextCorridorInterior leftInterior hnext))
          aligned.toInterface.rightBeforePos).1 :=
      aligned.nextLocalLayerPrefixCrossing_zero_eq_rightBeforeEdge
    _ = beforeOutgoingCornerEdge
        (realization.slabPlacementAt htwoSided hunique leftInterior) :=
      aligned.rightBefore_edge

/-- Corner alignment identifies the second right crossing with the actual
third edge at the other endpoint of the shared rung. -/
theorem nextLocalLayerPrefixCrossing_one_eq_afterOutgoingCornerEdge
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    aligned.toInterface.nextLocalLayerPrefixCrossing (1 : Fin 2) =
      afterOutgoingCornerEdge
        (realization.slabPlacementAt htwoSided hunique leftInterior) := by
  calc
    aligned.toInterface.nextLocalLayerPrefixCrossing (1 : Fin 2) =
        (placementSideEdge htwoSided
          (realization.slabPlacementAt htwoSided hunique
            (nextCorridorInterior leftInterior hnext))
          aligned.toInterface.rightAfterPos).1 :=
      aligned.nextLocalLayerPrefixCrossing_one_eq_rightAfterEdge
    _ = afterOutgoingCornerEdge
        (realization.slabPlacementAt htwoSided hunique leftInterior) :=
      aligned.rightAfter_edge

/-- The two first-coordinate seam edges meet at the first endpoint of the
shared rung. -/
theorem leftBeforeEdge_adj_beforeOutgoingCornerEdge
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem) :
    embedded.cellulation.rotation.toRotationSystem.edgeAdjacencyGraph.Adj
      aligned.toInterface.leftBeforeEdge.1
      (beforeOutgoingCornerEdge
        (realization.slabPlacementAt htwoSided hunique leftInterior)) := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let placement := realization.slabPlacementAt htwoSided hunique leftInterior
  let sideDart := faceCycleDart RS placement.root
    aligned.toInterface.leftBeforePos.1
  let outgoingDart := faceCycleDart RS placement.root
    placement.outgoingPosition
  have hdarts : outgoingDart = RS.phi sideDart :=
    faceCycleDart_successor_of_modEq RS placement.root placement.orbit_card
      aligned.toInterface.leftBeforePos.1 placement.outgoingPosition
      aligned.leftBefore_precedesOutgoing
  have hcorner := cornerEdges_pairwise_ne_and_incident
    RS hcubic hrotation sideDart
  have hadj := RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
    hcorner.2.1 hcorner.2.2.2.1 hcorner.2.2.2.2.2
  change RS.edgeAdjacencyGraph.Adj
    (RS.edgeOf sideDart) (RS.edgeOf (RS.rho outgoingDart))
  rw [hdarts]
  exact hadj

/-- The two second-coordinate seam edges meet at the other endpoint of the
shared rung. -/
theorem leftAfterEdge_adj_afterOutgoingCornerEdge
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem) :
    embedded.cellulation.rotation.toRotationSystem.edgeAdjacencyGraph.Adj
      aligned.toInterface.leftAfterEdge.1
      (afterOutgoingCornerEdge
        (realization.slabPlacementAt htwoSided hunique leftInterior)) := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let placement := realization.slabPlacementAt htwoSided hunique leftInterior
  let outgoingDart := faceCycleDart RS placement.root
    placement.outgoingPosition
  let afterDart := faceCycleDart RS placement.root
    aligned.toInterface.leftAfterPos.1
  have hdarts : afterDart = RS.phi outgoingDart :=
    faceCycleDart_successor_of_modEq RS placement.root placement.orbit_card
      placement.outgoingPosition aligned.toInterface.leftAfterPos.1
      aligned.leftAfter_followsOutgoing
  have hcorner := cornerEdges_pairwise_ne_and_incident
    RS hcubic hrotation outgoingDart
  have hadj := RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
    hcorner.2.2.1 hcorner.2.2.2.2.1 hcorner.2.2.2.2.2
  change RS.edgeAdjacencyGraph.Adj
    (RS.edgeOf afterDart) (RS.edgeOf (RS.rho (RS.phi outgoingDart)))
  rw [hdarts]
  exact hadj

/-- The two source-ordered prefix crossings are paired by the two literal
endpoint turns around the shared rung. -/
theorem localLayerPrefixCrossing_adj_nextLocalLayerPrefixCrossing
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (step : Fin 2) :
    embedded.cellulation.rotation.toRotationSystem.edgeAdjacencyGraph.Adj
      (aligned.toInterface.localLayerPrefixCrossing step)
      (aligned.toInterface.nextLocalLayerPrefixCrossing step) := by
  fin_cases step
  · simpa [aligned.localLayerPrefixCrossing_zero_eq_leftBeforeEdge,
      aligned.nextLocalLayerPrefixCrossing_zero_eq_beforeOutgoingCornerEdge]
      using aligned.leftBeforeEdge_adj_beforeOutgoingCornerEdge hcubic hrotation
  · simpa [aligned.localLayerPrefixCrossing_one_eq_leftAfterEdge,
      aligned.nextLocalLayerPrefixCrossing_one_eq_afterOutgoingCornerEdge]
      using aligned.leftAfterEdge_adj_afterOutgoingCornerEdge hcubic hrotation

/-- Every left crossing lies in the old cumulative prefix. -/
theorem localLayerPrefixCrossing_mem_leftPrefixRegion
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 2) :
    aligned.toInterface.localLayerPrefixCrossing step ∈
      aligned.toInterface.localLayerLeftPrefixRegion := by
  simpa [SourceConsecutiveSlabInterface.localLayerLeftPrefixRegion] using
    aligned.toInterface.localLayerPrefixCrossing_mem_prefixEdgeRegion step

/-- Every right crossing is a literal side edge of the newly exposed
hexagon, hence belongs to the Cell boundary factor. -/
theorem nextLocalLayerPrefixCrossing_mem_cellBoundaryRegion
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 2) :
    aligned.toInterface.nextLocalLayerPrefixCrossing step ∈
      aligned.toInterface.localLayerCellBoundaryRegion := by
  let corridor := realization.toCleanOrbitHexCorridorSkeleton
    |>.toOrbitHexCorridorSkeleton
  let rightInterior := nextCorridorInterior leftInterior hnext
  let rightPlacement := realization.slabPlacementAt htwoSided hunique
    rightInterior
  fin_cases step
  · change aligned.toInterface.nextLocalLayerPrefixCrossing (0 : Fin 2) ∈
      aligned.toInterface.localLayerCellBoundaryRegion
    rw [aligned.nextLocalLayerPrefixCrossing_zero_eq_rightBeforeEdge]
    have hboundary := ((mem_internalSideEdges_iff corridor hunique rightInterior
      (placementSideEdge htwoSided rightPlacement
        aligned.toInterface.rightBeforePos).1).1
      (placementSideEdge htwoSided rightPlacement
        aligned.toInterface.rightBeforePos).2).1
    simpa [SourceConsecutiveSlabInterface.localLayerCellBoundaryRegion,
      SourceConsecutiveSlabInterface.nextCenterLayerFace, corridor,
      rightInterior, rightPlacement] using hboundary
  · change aligned.toInterface.nextLocalLayerPrefixCrossing (1 : Fin 2) ∈
      aligned.toInterface.localLayerCellBoundaryRegion
    rw [aligned.nextLocalLayerPrefixCrossing_one_eq_rightAfterEdge]
    have hboundary := ((mem_internalSideEdges_iff corridor hunique rightInterior
      (placementSideEdge htwoSided rightPlacement
        aligned.toInterface.rightAfterPos).1).1
      (placementSideEdge htwoSided rightPlacement
        aligned.toInterface.rightAfterPos).2).1
    simpa [SourceConsecutiveSlabInterface.localLayerCellBoundaryRegion,
      SourceConsecutiveSlabInterface.nextCenterLayerFace, corridor,
      rightInterior, rightPlacement] using hboundary

/-- Neither old-prefix crossing is the shared rung itself. -/
theorem localLayerPrefixCrossing_ne_sharedRungEdge
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 2) :
    aligned.toInterface.localLayerPrefixCrossing step ≠
      aligned.toInterface.localLayerSharedRungEdge := by
  let corridor := realization.toCleanOrbitHexCorridorSkeleton
    |>.toOrbitHexCorridorSkeleton
  let placement := realization.slabPlacementAt htwoSided hunique leftInterior
  fin_cases step
  · have hne := ((mem_internalSideEdges_iff corridor hunique leftInterior
      (placementSideEdge htwoSided placement
        aligned.toInterface.leftBeforePos).1).1
      (placementSideEdge htwoSided placement
        aligned.toInterface.leftBeforePos).2).2.2
    intro heq
    apply hne
    simpa [SourceConsecutiveSlabInterface.leftBeforeEdge,
      SourceConsecutiveSlabInterface.localLayerSharedRungEdge,
      corridor, placement] using
      aligned.localLayerPrefixCrossing_zero_eq_leftBeforeEdge.symm.trans heq
  · have hne := ((mem_internalSideEdges_iff corridor hunique leftInterior
      (placementSideEdge htwoSided placement
        aligned.toInterface.leftAfterPos).1).1
      (placementSideEdge htwoSided placement
        aligned.toInterface.leftAfterPos).2).2.2
    intro heq
    apply hne
    simpa [SourceConsecutiveSlabInterface.leftAfterEdge,
      SourceConsecutiveSlabInterface.localLayerSharedRungEdge,
      corridor, placement] using
      aligned.localLayerPrefixCrossing_one_eq_leftAfterEdge.symm.trans heq

/-- Neither newly exposed crossing is the shared rung itself. -/
theorem nextLocalLayerPrefixCrossing_ne_sharedRungEdge
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 2) :
    aligned.toInterface.nextLocalLayerPrefixCrossing step ≠
      aligned.toInterface.localLayerSharedRungEdge := by
  let corridor := realization.toCleanOrbitHexCorridorSkeleton
    |>.toOrbitHexCorridorSkeleton
  let rightInterior := nextCorridorInterior leftInterior hnext
  let rightPlacement := realization.slabPlacementAt htwoSided hunique
    rightInterior
  have hrungs : rightInterior.incoming = leftInterior.outgoing :=
    nextCorridorInterior_incoming_eq_outgoing leftInterior hnext
  fin_cases step
  · have hne := ((mem_internalSideEdges_iff corridor hunique rightInterior
      (placementSideEdge htwoSided rightPlacement
        aligned.toInterface.rightBeforePos).1).1
      (placementSideEdge htwoSided rightPlacement
        aligned.toInterface.rightBeforePos).2).2.1
    intro heq
    apply hne
    simpa [SourceConsecutiveSlabInterface.localLayerSharedRungEdge,
      corridor, rightInterior, rightPlacement, hrungs] using
      aligned.nextLocalLayerPrefixCrossing_zero_eq_rightBeforeEdge.symm.trans heq
  · have hne := ((mem_internalSideEdges_iff corridor hunique rightInterior
      (placementSideEdge htwoSided rightPlacement
        aligned.toInterface.rightAfterPos).1).1
      (placementSideEdge htwoSided rightPlacement
        aligned.toInterface.rightAfterPos).2).2.1
    intro heq
    apply hne
    simpa [SourceConsecutiveSlabInterface.localLayerSharedRungEdge,
      corridor, rightInterior, rightPlacement, hrungs] using
      aligned.nextLocalLayerPrefixCrossing_one_eq_rightAfterEdge.symm.trans heq

/-- A left crossing cannot also belong to the new Cell boundary: the two
factors intersect only in the shared rung. -/
theorem localLayerPrefixCrossing_not_mem_cellBoundaryRegion
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 2) :
    aligned.toInterface.localLayerPrefixCrossing step ∉
      aligned.toInterface.localLayerCellBoundaryRegion := by
  intro hcell
  have hinter : aligned.toInterface.localLayerPrefixCrossing step ∈
      aligned.toInterface.localLayerLeftPrefixRegion ∩
        aligned.toInterface.localLayerCellBoundaryRegion :=
    Finset.mem_inter.2
      ⟨aligned.localLayerPrefixCrossing_mem_leftPrefixRegion step, hcell⟩
  rw [aligned.toInterface.localLayerLeftPrefixRegion_inter_cellBoundary_eq_singleton]
    at hinter
  exact aligned.localLayerPrefixCrossing_ne_sharedRungEdge step
    (Finset.mem_singleton.1 hinter)

/-- A right crossing cannot already belong to the old prefix, by the same
singleton-intersection calculation. -/
theorem nextLocalLayerPrefixCrossing_not_mem_leftPrefixRegion
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 2) :
    aligned.toInterface.nextLocalLayerPrefixCrossing step ∉
      aligned.toInterface.localLayerLeftPrefixRegion := by
  intro hleft
  have hinter : aligned.toInterface.nextLocalLayerPrefixCrossing step ∈
      aligned.toInterface.localLayerLeftPrefixRegion ∩
        aligned.toInterface.localLayerCellBoundaryRegion :=
    Finset.mem_inter.2
      ⟨hleft, aligned.nextLocalLayerPrefixCrossing_mem_cellBoundaryRegion step⟩
  rw [aligned.toInterface.localLayerLeftPrefixRegion_inter_cellBoundary_eq_singleton]
    at hinter
  exact aligned.nextLocalLayerPrefixCrossing_ne_sharedRungEdge step
    (Finset.mem_singleton.1 hinter)

/-- When the paired source crossings carry the tracked colors, their literal
endpoint turn is an edge of the exact residual seam graph. -/
theorem localLayerTrackedSeamGraph_adj_crossings
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (C : G.edgeSet → Color) (a b : Color) (step : Fin 2)
    (hleft : IsTrackedColor a b
      (C (aligned.toInterface.localLayerPrefixCrossing step)))
    (hright : IsTrackedColor a b
      (C (aligned.toInterface.nextLocalLayerPrefixCrossing step))) :
    (aligned.toInterface.localLayerTrackedSeamGraph C a b).Adj
      (aligned.toInterface.localLayerPrefixCrossing step)
      (aligned.toInterface.nextLocalLayerPrefixCrossing step) := by
  apply (regionalTrackedSeamGraph_adj_iff
    embedded.cellulation.rotation.toRotationSystem
    aligned.toInterface.localLayerLeftPrefixRegion
    aligned.toInterface.localLayerCellBoundaryRegion C a b _ _).2
  exact ⟨
    ⟨aligned.localLayerPrefixCrossing_adj_nextLocalLayerPrefixCrossing
        hcubic hrotation step, hleft, hright⟩,
    Or.inl ⟨
      aligned.localLayerPrefixCrossing_mem_leftPrefixRegion step,
      aligned.localLayerPrefixCrossing_not_mem_cellBoundaryRegion step,
      aligned.nextLocalLayerPrefixCrossing_mem_cellBoundaryRegion step,
      aligned.nextLocalLayerPrefixCrossing_not_mem_leftPrefixRegion step⟩⟩

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
