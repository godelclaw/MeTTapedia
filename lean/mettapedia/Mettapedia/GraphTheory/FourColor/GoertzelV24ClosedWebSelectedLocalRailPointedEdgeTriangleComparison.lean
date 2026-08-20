import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementBoundedSuffixSharedCollisionFirstWindowPointedEdgeReceipt
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareEndpointTriangles

/-!
# L1: compare pointed rail-edge receipts with square endpoint triangles

The complete adjacent terminal classifier gives every surviving rail edge a
literal selected primal crossing.  A square-bond endpoint triangle also
carries one selected primal crossing at every dual step.  This module compares
the two presentations through that named primal edge.

No global uniqueness of a shared edge between two faces is assumed.  Instead,
the rotation system's incidence-at-most-two theorem shows that one primal edge
shared by the receipted face pair and selected by the endpoint triangle forces
the same unoriented dual edge.  Consequently, if the incoming and outgoing
receipted crossings at a pointed collision both meet one endpoint centre, the
triangle supplies the literal predecessor-to-successor bypass.

This does not yet prove that the two source crossings meet the same endpoint
centre.  Discharging that finite placement comparison, iterating the rolling
transition, and attaching the two end caps remain open; Fable flag L1 is not
closed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathPointedOccurrence
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24SelectedDualCycleSeparator

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

/-- A uniform form of the three adjacent terminal receipt alternatives: the
dual edge is displayed by its two distinct incident faces, and one concrete
primal edge is shared by those faces. -/
structure SelectedAdjacentTerminalEdgeCrossingReceipt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    (edge : Sym2 (SelectedFace web)) where
  first : SelectedFace web
  second : SelectedFace web
  edge_eq : edge = s(first, second)
  faces_ne : first ≠ second
  crossing : G.edgeSet
  crossing_mem_shared : crossing ∈ sharedInteriorEdges
    (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS)) first.1 second.1

section ReceiptNormalization

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

/-- Each old-step, successor-step, or old-centre receipt exposes one common
primal-crossing representation. -/
theorem SelectedAdjacentTerminalEdgeReceipt.toCrossingReceipt
    {edge : Sym2 (SelectedFace web)}
    (receipt : SelectedAdjacentTerminalEdgeReceipt
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      edge) :
    Nonempty (SelectedAdjacentTerminalEdgeCrossingReceipt edge) := by
  rcases receipt with oldForward | successorOrCenter
  · rcases oldForward with ⟨left, right, _hsuccessor, step⟩
    exact ⟨{
      first := selectedPlacementSideFace leftPlacement left
      second := selectedPlacementSideFace leftPlacement right
      edge_eq := step.edge_eq
      faces_ne := step.faces_ne
      crossing := selectedPlacementSideForwardThirdEdge leftPlacement left
      crossing_mem_shared := step.thirdEdge_mem_shared
    }⟩
  · rcases successorOrCenter with successorForward | center
    · rcases successorForward with ⟨left, right, _hsuccessor, step⟩
      exact ⟨{
        first := selectedPlacementSideFace rightPlacement left
        second := selectedPlacementSideFace rightPlacement right
        edge_eq := step.edge_eq
        faces_ne := step.faces_ne
        crossing := selectedPlacementSideForwardThirdEdge rightPlacement left
        crossing_mem_shared := step.thirdEdge_mem_shared
      }⟩
    · rcases center with ⟨position, step⟩
      let centerFace :=
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          leftInterior.center
      have hadj : (SelectedDualGraph web).Adj centerFace
          (selectedPlacementSideFace leftPlacement position) :=
        selectedPlacementSideFace_adjacent_center
          (corridor := corridor) leftPlacement position
      exact ⟨{
        first := centerFace
        second := selectedPlacementSideFace leftPlacement position
        edge_eq := step.edge_eq
        faces_ne := hadj.ne
        crossing := web.annular.RS.edgeOf
          (faceCycleDart web.annular.RS leftPlacement.root position.1)
        crossing_mem_shared := step.sideEdge_mem_shared
      }⟩

end ReceiptNormalization

section TriangleComparison

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}

/-- A primal edge selected by both an arbitrary receipted dual edge and an
endpoint triangle determines the same unoriented dual edge.  Incidence at
most two, rather than global shared-edge uniqueness, is the load-bearing
fact. -/
theorem SelectedAdjacentTerminalEdgeCrossingReceipt.edge_eq_coreDualWalkGraphEdge
    {edge : Sym2 (SelectedFace web)}
    (receipt : SelectedAdjacentTerminalEdgeCrossingReceipt edge)
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : MiddleReplacementShortDualCycle.SquareBondRealization cycle component}
    (triangle : bond.EndpointSelectedTriangle)
    (step : Fin triangle.selectedCycle.walk.length)
    (hcrossing : triangle.selectedCycle.crossingEdge step = receipt.crossing) :
    edge = coreDualWalkGraphEdge
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      triangle.selectedCycle.walk step := by
  let stepLeft := triangle.selectedCycle.walk.getVert step.val
  let stepRight := triangle.selectedCycle.walk.getVert (step.val + 1)
  have hstepAdj := triangle.selectedCycle.walk.adj_getVert_succ step.isLt
  have hstepFacesNe : stepLeft.1 ≠ stepRight.1 := by
    intro hfaces
    exact hstepAdj.ne (Subtype.ext hfaces)
  have hreceipt := (mem_sharedInteriorEdges_iff
    (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))).1
      receipt.crossing_mem_shared
  have hstepLeft : receipt.crossing ∈
      orbitFaceBoundary web.annular.RS stepLeft.1 := by
    rw [← hcrossing]
    exact triangle.selectedCycle.crossingEdge_mem_leftFace step
  have hstepRight : receipt.crossing ∈
      orbitFaceBoundary web.annular.RS stepRight.1 := by
    rw [← hcrossing]
    exact triangle.selectedCycle.crossingEdge_mem_rightFace step
  have hreceiptFacesNe : receipt.first.1 ≠ receipt.second.1 := by
    intro hfaces
    exact receipt.faces_ne (Subtype.ext hfaces)
  have hleft :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (orbitFace_incidence_le_two web.annular.RS)
      receipt.first.2 receipt.second.2 stepLeft.2 hreceiptFacesNe
      hreceipt.2.1 hreceipt.2.2 hstepLeft
  have hright :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (orbitFace_incidence_le_two web.annular.RS)
      receipt.first.2 receipt.second.2 stepRight.2 hreceiptFacesNe
      hreceipt.2.1 hreceipt.2.2 hstepRight
  rw [receipt.edge_eq]
  change s(receipt.first, receipt.second) = s(stepLeft, stepRight)
  rcases hleft with hleft | hleft <;>
    rcases hright with hright | hright
  · exact False.elim (hstepFacesNe (hleft.trans hright.symm))
  · apply Sym2.eq_iff.mpr
    exact Or.inl ⟨Subtype.ext hleft.symm, Subtype.ext hright.symm⟩
  · apply Sym2.eq_iff.mpr
    exact Or.inr ⟨Subtype.ext hright.symm, Subtype.ext hleft.symm⟩
  · exact False.elim (hstepFacesNe (hleft.trans hright.symm))

/-- If the receipt's selected primal crossing occurs on the endpoint
triangle, then the receipted dual edge is literally one of its three walk
edges. -/
theorem SelectedAdjacentTerminalEdgeCrossingReceipt.edge_mem_endpointTriangle
    {edge : Sym2 (SelectedFace web)}
    (receipt : SelectedAdjacentTerminalEdgeCrossingReceipt edge)
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : MiddleReplacementShortDualCycle.SquareBondRealization cycle component}
    (triangle : bond.EndpointSelectedTriangle)
    (hcrossing : receipt.crossing ∈ triangle.selectedCycle.crossingEdges) :
    edge ∈ triangle.selectedCycle.walk.edges := by
  rcases (triangle.selectedCycle.mem_crossingEdges_iff receipt.crossing).1
      hcrossing with ⟨step, hstep⟩
  have hedge := receipt.edge_eq_coreDualWalkGraphEdge triangle step hstep
  let edgeStep : Fin triangle.selectedCycle.walk.edges.length :=
    Fin.cast triangle.selectedCycle.walk.length_edges.symm step
  have hget := edges_get_coreDualWalkGraphEdge
    (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))
    triangle.selectedCycle.walk step
  rw [hedge, ← hget]
  exact List.get_mem triangle.selectedCycle.walk.edges edgeStep

/-- Incidence with the endpoint centre is the convenient local criterion for
membership in that endpoint triangle's selected crossing set. -/
theorem SelectedAdjacentTerminalEdgeCrossingReceipt.edge_mem_endpointTriangle_of_meets_center
    {edge : Sym2 (SelectedFace web)}
    (receipt : SelectedAdjacentTerminalEdgeCrossingReceipt edge)
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : MiddleReplacementShortDualCycle.SquareBondRealization cycle component}
    (triangle : bond.EndpointSelectedTriangle)
    (hcenter : triangle.center ∈ receipt.crossing.1) :
    edge ∈ triangle.selectedCycle.walk.edges := by
  apply receipt.edge_mem_endpointTriangle triangle
  rw [triangle.crossingEdges_eq_incidentEdgeFinset]
  simpa [incidentEdgeFinset] using hcenter

/-- Once both pointed incident crossings meet the same square endpoint, the
endpoint triangle gives the one-edge predecessor-to-successor bypass required
by the rolling rail repair. -/
theorem InteriorOccurrence.endpointTriangle_bypass_of_crossingReceipts
    {start finish current : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) walk)
    (hpath : walk.IsPath)
    (incomingReceipt :
      SelectedAdjacentTerminalEdgeCrossingReceipt occurrence.incomingEdge)
    (outgoingReceipt :
      SelectedAdjacentTerminalEdgeCrossingReceipt occurrence.outgoingEdge)
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : MiddleReplacementShortDualCycle.SquareBondRealization cycle component}
    (triangle : bond.EndpointSelectedTriangle)
    (hincomingCenter : triangle.center ∈ incomingReceipt.crossing.1)
    (houtgoingCenter : triangle.center ∈ outgoingReceipt.crossing.1) :
    (SelectedDualGraph web).Adj occurrence.predecessor occurrence.successor := by
  have hincoming := incomingReceipt
    |>.edge_mem_endpointTriangle_of_meets_center triangle hincomingCenter
  have houtgoing := outgoingReceipt
    |>.edge_mem_endpointTriangle_of_meets_center triangle houtgoingCenter
  have hpredecessor : occurrence.predecessor ∈
      triangle.selectedCycle.walk.support :=
    triangle.selectedCycle.walk.mem_support_of_mem_edges hincoming
      (by simp [InteriorOccurrence.incomingEdge])
  have hsuccessor : occurrence.successor ∈
      triangle.selectedCycle.walk.support :=
    triangle.selectedCycle.walk.mem_support_of_mem_edges houtgoing
      (by simp [InteriorOccurrence.outgoingEdge])
  exact triangle.adj_of_mem_support_of_ne hpredecessor hsuccessor
    (occurrence.predecessor_ne_successor hpath)

end TriangleComparison

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
