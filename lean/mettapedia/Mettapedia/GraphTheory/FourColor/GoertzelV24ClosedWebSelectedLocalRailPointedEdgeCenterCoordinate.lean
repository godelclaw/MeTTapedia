import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeFaceAllocation

/-!
# L1: orient old-centre pointed receipts at a non-centre collision

The proof-relevant terminal receipt has three source origins.  In the
`oldCenter` case its two faces are the old Cell--3 centre and one selected side
face.  At a pointed collision known not to be that centre, the unordered-edge
ambiguity therefore disappears: an incoming old-centre receipt comes from the
centre, while an outgoing one returns to the centre.

In particular, a simple rail cannot use old-centre receipts on both sides of
the same non-centre collision, because its predecessor and successor would
coincide.  This removes one literal source-origin pair.  It does not classify
either forward-origin corner against a replacement-square bond, discard an
exterior fan, construct a rolling repair, attach end caps, or close Fable flag
L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathPointedOccurrence
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

private abbrev SelectedFace
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}

/-- At a non-centre collision, an incoming old-centre receipt is oriented from
the old Cell--3 centre to the collision side face. -/
theorem InteriorOccurrence.predecessor_eq_leftCenter_of_incoming_oldCenter
    {start finish current : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) walk)
    (position :
      {position // position ∈ selectedPlacementSidePositions leftPlacement})
    (step : SelectedPlacementCenterSideEdgeReceipt
      leftPlacement position occurrence.incomingEdge)
    (hcurrent : current ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        leftInterior.center) :
    occurrence.predecessor =
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        leftInterior.center := by
  have hfaces :
      (occurrence.predecessor =
          corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            leftInterior.center ∧
        current = selectedPlacementSideFace leftPlacement position) ∨
      (occurrence.predecessor = selectedPlacementSideFace leftPlacement position ∧
        current =
          corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            leftInterior.center) := by
    apply Sym2.eq_iff.mp
    simpa [InteriorOccurrence.incomingEdge] using step.edge_eq
  rcases hfaces with hforward | hreverse
  · exact hforward.1
  · exact False.elim (hcurrent hreverse.2)

/-- At the same non-centre collision, an outgoing old-centre receipt is
oriented back from the collision side face to the old Cell--3 centre. -/
theorem InteriorOccurrence.successor_eq_leftCenter_of_outgoing_oldCenter
    {start finish current : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) walk)
    (position :
      {position // position ∈ selectedPlacementSidePositions leftPlacement})
    (step : SelectedPlacementCenterSideEdgeReceipt
      leftPlacement position occurrence.outgoingEdge)
    (hcurrent : current ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        leftInterior.center) :
    occurrence.successor =
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        leftInterior.center := by
  have hfaces :
      (current =
          corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            leftInterior.center ∧
        occurrence.successor = selectedPlacementSideFace leftPlacement position) ∨
      (current = selectedPlacementSideFace leftPlacement position ∧
        occurrence.successor =
          corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            leftInterior.center) := by
    apply Sym2.eq_iff.mp
    simpa [InteriorOccurrence.outgoingEdge] using step.edge_eq
  rcases hfaces with hforward | hreverse
  · exact False.elim (hcurrent hforward.1)
  · exact hreverse.2

/-- A simple pointed rail through a non-centre collision cannot use an
old-centre connector for both incident edges. -/
theorem InteriorOccurrence.not_both_incident_edges_oldCenter
    {start finish current : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) walk)
    (hpath : walk.IsPath)
    (incomingPosition :
      {position // position ∈ selectedPlacementSidePositions leftPlacement})
    (incomingStep : SelectedPlacementCenterSideEdgeReceipt
      leftPlacement incomingPosition occurrence.incomingEdge)
    (outgoingPosition :
      {position // position ∈ selectedPlacementSidePositions leftPlacement})
    (outgoingStep : SelectedPlacementCenterSideEdgeReceipt
      leftPlacement outgoingPosition occurrence.outgoingEdge)
    (hcurrent : current ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        leftInterior.center) : False := by
  apply occurrence.predecessor_ne_successor hpath
  exact (InteriorOccurrence.predecessor_eq_leftCenter_of_incoming_oldCenter
      occurrence incomingPosition incomingStep hcurrent).trans
    (InteriorOccurrence.successor_eq_leftCenter_of_outgoing_oldCenter
      occurrence outgoingPosition outgoingStep hcurrent).symm

/-- More strongly, the two incident dual edges cannot even both carry
old-centre receipts.  This representation-independent form is the public
consumer theorem: it does not depend on which constructor a later origin
packet happened to retain. -/
theorem InteriorOccurrence.not_both_incident_edges_have_oldCenterReceipt
    {start finish current : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) walk)
    (hpath : walk.IsPath)
    (hcurrent : current ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        leftInterior.center) :
    ¬ ((∃ position :
          {position // position ∈ selectedPlacementSidePositions leftPlacement},
          SelectedPlacementCenterSideEdgeReceipt
            leftPlacement position occurrence.incomingEdge) ∧
      (∃ position :
          {position // position ∈ selectedPlacementSidePositions leftPlacement},
          SelectedPlacementCenterSideEdgeReceipt
            leftPlacement position occurrence.outgoingEdge)) := by
  rintro ⟨⟨incomingPosition, incomingStep⟩,
    ⟨outgoingPosition, outgoingStep⟩⟩
  exact InteriorOccurrence.not_both_incident_edges_oldCenter
    occurrence hpath incomingPosition incomingStep
      outgoingPosition outgoingStep hcurrent

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
