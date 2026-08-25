import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeForwardCornerCoordinate

/-!
# L1: exclude selected rungs from a pointed forward corner

A forward source receipt crosses the third edge at a corner between two
consecutive non-rung slots of one displayed Cell--3 face.  Consequently its
two boundary arms are the literal face-cycle edges at those two side slots,
and neither arm can be either selected rung of that placement.

This is a negative coordinate result for the finite source-square audit.  In
particular, the two arms must not be identified with the placement's two
source rungs merely because all four edges occur in the same local picture.
It does not classify either arm as a collision-side crossing, discard an
exterior-fan alternative, construct a rolling repair or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open SimpleGraphDartRotation

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    {placement : SelectedInternalHexRungPlacement corridor rungs interior}
    {left right :
      {position // position ∈ selectedPlacementSidePositions placement}}
    {edge : Sym2 (AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS)))}

/-- The entering arm is definitionally the boundary edge at the receipt's
left side coordinate. -/
theorem SelectedPlacementSideForwardEdgeReceipt.firstArm_eq_boundaryEdge
    (_receipt : SelectedPlacementSideForwardEdgeReceipt
      placement left right edge) :
    selectedPlacementSideForwardFirstArm placement left =
      faceCycleEdge web.annular.RS placement.root left.1 := by
  rfl

/-- The leaving arm is the boundary edge at the receipt's right side
coordinate.  This uses the proof-relevant successor-dart equation retained by
the crossing receipt. -/
theorem SelectedPlacementSideForwardEdgeReceipt.secondArm_eq_boundaryEdge
    (receipt : SelectedPlacementSideForwardEdgeReceipt
      placement left right edge) :
    selectedPlacementSideForwardSecondArm placement left =
      faceCycleEdge web.annular.RS placement.root right.1 := by
  change web.annular.RS.edgeOf
      (web.annular.RS.phi
        (selectedPlacementSideForwardDart placement left)) =
    web.annular.RS.edgeOf
      (selectedPlacementSideForwardDart placement right)
  rw [receipt.right_dart_eq]

/-- Both boundary arms of a forward receipt avoid both selected corridor
rungs.  The result uses boundary-edge injectivity of the certified interior
face and the fact that `left` and `right` inhabit the non-rung side-slot
subtype; it assumes no global cubicity or face-intersection uniqueness. -/
theorem SelectedPlacementSideForwardEdgeReceipt.arms_ne_selectedRungs
    (receipt : SelectedPlacementSideForwardEdgeReceipt
      placement left right edge) :
    selectedPlacementSideForwardFirstArm placement left ≠
        rungs.edge interior.incoming ∧
      selectedPlacementSideForwardFirstArm placement left ≠
        rungs.edge interior.outgoing ∧
      selectedPlacementSideForwardSecondArm placement left ≠
        rungs.edge interior.incoming ∧
      selectedPlacementSideForwardSecondArm placement left ≠
        rungs.edge interior.outgoing := by
  have hrootInternal : dartOrbitFace web.annular.RS placement.root ∈
      web.annular.cellulation.interiorFaces := by
    rw [placement.root_face]
    exact corridor.face_internal interior.center
  have hinjective := Instance.InteriorFace.faceCycleEdge_injective
    web placement.root hrootInternal
  have hleft :=
    (mem_selectedPlacementSidePositions_iff placement left.1).1 left.2
  have hright :=
    (mem_selectedPlacementSidePositions_iff placement right.1).1 right.2
  have hfirst :=
    Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.firstArm_eq_boundaryEdge
      receipt
  have hsecond :=
    Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.secondArm_eq_boundaryEdge
      receipt
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hedge
    apply hleft.1
    apply hinjective
    exact hfirst.symm.trans (hedge.trans placement.incoming_edge.symm)
  · intro hedge
    apply hleft.2
    apply hinjective
    exact hfirst.symm.trans (hedge.trans placement.outgoing_edge.symm)
  · intro hedge
    apply hright.1
    apply hinjective
    exact hsecond.symm.trans (hedge.trans placement.incoming_edge.symm)
  · intro hedge
    apply hright.2
    apply hinjective
    exact hsecond.symm.trans (hedge.trans placement.outgoing_edge.symm)

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
