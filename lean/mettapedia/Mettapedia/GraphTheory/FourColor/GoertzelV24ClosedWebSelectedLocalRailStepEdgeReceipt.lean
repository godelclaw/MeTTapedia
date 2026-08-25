import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailStepReceipt

/-!
# L1: crossing receipts on selected local rail edges

The older selected local-rail constructor chooses a simple facial-dual walk
of length at most one.  The source-coordinate receipt proved one layer below
can be attached to every edge of any such walk: a nonempty edge forces the
nonstationary branch, and a path of length at most one has exactly the edge
joining its two endpoints.

This preserves the existing choice-based walk API.  It does not yet propagate
the receipt through a two-step local rail, a bypassed terminal track, a middle
replacement, or the arbitrary-length crosscut assembly required by L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation

private theorem edge_eq_endpoints_and_ne_of_mem_edges_of_length_le_one
    {W : Type*} {H : SimpleGraph W} {start finish : W}
    (walk : H.Walk start finish) (hlength : walk.length ≤ 1)
    (edge : Sym2 W) (hedge : edge ∈ walk.edges) :
    edge = s(start, finish) ∧ start ≠ finish := by
  cases walk with
  | nil => simp at hedge
  | cons hadj tail =>
      cases tail with
      | nil =>
          have hedge' : edge = s(start, finish) := by
            simpa [SimpleGraph.Walk.edges_cons] using hedge
          exact ⟨hedge', hadj.ne⟩
      | cons hnext rest =>
          simp only [SimpleGraph.Walk.length_cons] at hlength
          omega

/-- A literal dual edge of a selected forward side step, together with the
exact third primal edge and cubic corner that realize it. -/
structure SelectedPlacementSideForwardEdgeReceipt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (left right :
      {position // position ∈ selectedPlacementSidePositions placement})
    (edge : Sym2 (AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS)))) : Prop where
  edge_eq : edge = s(selectedPlacementSideFace placement left,
    selectedPlacementSideFace placement right)
  faces_ne : selectedPlacementSideFace placement left ≠
    selectedPlacementSideFace placement right
  right_dart_eq : selectedPlacementSideForwardDart placement right =
    web.annular.RS.phi (selectedPlacementSideForwardDart placement left)
  corner_card_eq_three :
    (web.annular.RS.dartsAt
      (selectedPlacementSideForwardCorner placement left)).card = 3
  thirdEdge_mem_shared :
    selectedPlacementSideForwardThirdEdge placement left ∈
      sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (selectedPlacementSideFace placement left).1
        (selectedPlacementSideFace placement right).1

/-- Every actual edge of an existing selected length-at-most-one forward
walk carries the exact source crossing receipt. -/
theorem selectedPlacementSideForwardEdgeReceipt_of_walk_edge
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (left right :
      {position // position ∈ selectedPlacementSidePositions placement})
    (hsuccessor : right.1.val ≡ left.1.val + 1 [MOD 6])
    (walk : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        (selectedPlacementSideFace placement left)
        (selectedPlacementSideFace placement right))
    (hlength : walk.length ≤ 1)
    (edge : Sym2 (AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))))
    (hedge : edge ∈ walk.edges) :
    SelectedPlacementSideForwardEdgeReceipt placement left right edge := by
  have hedgeData := edge_eq_endpoints_and_ne_of_mem_edges_of_length_le_one
    walk hlength edge hedge
  rcases hedgeData with ⟨hedgeEq, hfacesNe⟩
  rcases selectedPlacementSideForwardStepReceipt placement left right
      hsuccessor with ⟨receipt⟩
  cases receipt with
  | stationary hfaces => exact False.elim (hfacesNe hfaces)
  | crossing _ right_dart_eq corner_card_eq_three thirdEdge_mem_shared =>
      exact {
        edge_eq := hedgeEq
        faces_ne := hfacesNe
        right_dart_eq := right_dart_eq
        corner_card_eq_three := corner_card_eq_three
        thirdEdge_mem_shared := thirdEdge_mem_shared }

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
