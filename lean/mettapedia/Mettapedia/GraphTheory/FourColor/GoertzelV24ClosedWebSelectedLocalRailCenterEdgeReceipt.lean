import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailStepEdgeReceipt

/-!
# L1: crossing receipts on selected Cell-3 centre connectors

Terminal selected-rail repairs may use the literal two-edge walk from one
selected side face to another through the Cell-3 centre.  This module records
the source crossing carried by each of those connector edges: the selected
side slot determines a concrete dart, and its primal edge belongs to the two
incident interior face boundaries.

This closes the bounded provenance gap for the explicit centre connector.  It
does not construct an arbitrary-length crosscut or assert global uniqueness of
shared face-boundary edges.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation

/-- A centre-to-side dual edge together with its literal selected primal
crossing. -/
structure SelectedPlacementCenterSideEdgeReceipt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (position : {position // position ∈ selectedPlacementSidePositions placement})
    (edge : Sym2 (AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS)))) : Prop where
  edge_eq : edge = s(
    (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
      interior.center,
    selectedPlacementSideFace placement position)
  side_dart_internal :
    dartOrbitFace web.annular.RS
        (faceCycleDart web.annular.RS placement.root position.1) ∈
      web.annular.cellulation.interiorFaces
  sideEdge_mem_shared :
    web.annular.RS.edgeOf
        (faceCycleDart web.annular.RS placement.root position.1) ∈
      sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          interior.center).1
        (selectedPlacementSideFace placement position).1

/-- The displayed centre-to-side dual edge has the source receipt determined
by its selected side slot. -/
theorem selectedPlacementCenterSideEdgeReceipt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (position : {position // position ∈ selectedPlacementSidePositions placement}) :
    SelectedPlacementCenterSideEdgeReceipt placement position
      (s(
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          interior.center,
        selectedPlacementSideFace placement position)) := by
  let sideDart := faceCycleDart web.annular.RS placement.root position.1
  have hinternal : dartOrbitFace web.annular.RS sideDart ∈
      web.annular.cellulation.interiorFaces :=
    selectedPlacementSideDart_internal (corridor := corridor) placement position
  have hcenter : web.annular.RS.edgeOf sideDart ∈
      orbitFaceBoundary web.annular.RS
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          interior.center).1 := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      web.annular.RS sideDart
    rw [dartOrbitFace_faceCycleDart, placement.root_face] at hraw
    exact hraw
  have hside : web.annular.RS.edgeOf sideDart ∈
      orbitFaceBoundary web.annular.RS
        (selectedPlacementSideFace placement position).1 := by
    change web.annular.RS.edgeOf sideDart ∈ orbitFaceBoundary web.annular.RS
      (dartOrbitFace web.annular.RS (web.annular.RS.alpha sideDart))
    rw [← web.annular.RS.edge_alpha sideDart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS
      (web.annular.RS.alpha sideDart)
  exact {
    edge_eq := rfl
    side_dart_internal := hinternal
    sideEdge_mem_shared :=
      (mem_sharedInteriorEdges_iff (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).2
          ⟨Instance.InteriorFace.edge_mem_interiorEdgeSupport web sideDart hinternal,
            hcenter, hside⟩ }

/-- The literal one-edge dual walk from a selected side face to its Cell-3
centre.  Centre-residue repairs use this half-connector when they stop at the
centre instead of crossing to the opposite selected side. -/
def selectedPlacementSideToCenter
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (position : {position // position ∈ selectedPlacementSidePositions placement}) :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        (selectedPlacementSideFace placement position)
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          interior.center) :=
  .cons
    (selectedPlacementSideFace_adjacent_center
      (corridor := corridor) placement position).symm
    .nil

/-- The reverse one-edge connector from the Cell-3 centre to a selected side
face. -/
def selectedPlacementCenterToSide
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (position : {position // position ∈ selectedPlacementSidePositions placement}) :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          interior.center)
        (selectedPlacementSideFace placement position) :=
  .cons
    (selectedPlacementSideFace_adjacent_center
      (corridor := corridor) placement position)
    .nil

/-- The unique edge of a selected side-to-centre half-connector retains the
same literal primal crossing receipt as the full centre bridge. -/
theorem selectedPlacementSideToCenter_edge_receipt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (position : {position // position ∈ selectedPlacementSidePositions placement})
    (edge : Sym2 (AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))))
    (hedge : edge ∈ (selectedPlacementSideToCenter placement position).edges) :
    SelectedPlacementCenterSideEdgeReceipt placement position edge := by
  have hedge_eq : edge = s(
      selectedPlacementSideFace placement position,
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        interior.center) := by
    simpa [selectedPlacementSideToCenter] using hedge
  rw [hedge_eq]
  simpa [Sym2.eq_swap] using
    selectedPlacementCenterSideEdgeReceipt placement position

/-- The reverse half-connector has the identical undirected crossing
receipt. -/
theorem selectedPlacementCenterToSide_edge_receipt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (position : {position // position ∈ selectedPlacementSidePositions placement})
    (edge : Sym2 (AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))))
    (hedge : edge ∈ (selectedPlacementCenterToSide placement position).edges) :
    SelectedPlacementCenterSideEdgeReceipt placement position edge := by
  have hedge_eq : edge = s(
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        interior.center,
      selectedPlacementSideFace placement position) := by
    simpa [selectedPlacementCenterToSide] using hedge
  rw [hedge_eq]
  exact selectedPlacementCenterSideEdgeReceipt placement position

/-- The literal two-edge connector through a selected Cell-3 centre. -/
def selectedPlacementCenterBridge
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (after before :
      {position // position ∈ selectedPlacementSidePositions placement}) :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        (selectedPlacementSideFace placement after)
        (selectedPlacementSideFace placement before) :=
  .cons
    (selectedPlacementSideFace_adjacent_center
      (corridor := corridor) placement after).symm
    (.cons
      (selectedPlacementSideFace_adjacent_center
        (corridor := corridor) placement before)
      .nil)

/-- Every edge of the literal centre connector is one of its two selected
centre-to-side crossings. -/
theorem selectedPlacementCenterBridge_edge_receipt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (after before :
      {position // position ∈ selectedPlacementSidePositions placement})
    (edge : Sym2 (AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))))
    (hedge : edge ∈ (selectedPlacementCenterBridge placement after before).edges) :
    SelectedPlacementCenterSideEdgeReceipt placement after edge ∨
      SelectedPlacementCenterSideEdgeReceipt placement before edge := by
  simp only [selectedPlacementCenterBridge, SimpleGraph.Walk.edges_cons,
    SimpleGraph.Walk.edges_nil, List.mem_cons, List.not_mem_nil, or_false] at hedge
  rcases hedge with hedge | hedge
  · left
    rw [hedge]
    simpa [Sym2.eq_swap] using
      selectedPlacementCenterSideEdgeReceipt placement after
  · right
    rw [hedge]
    exact selectedPlacementCenterSideEdgeReceipt placement before

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
