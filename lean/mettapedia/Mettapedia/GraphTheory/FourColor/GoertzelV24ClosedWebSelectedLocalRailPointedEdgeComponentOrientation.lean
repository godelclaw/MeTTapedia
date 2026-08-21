import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeOppositeEndpointBypass

/-!
# L1: reduce pointed endpoint orientation to component membership

The selected square residue is a literal two-vertex component.  Consequently
the source-side statement needed by the endpoint-triangle consumer is not an
opaque coordinate equality: it is exactly membership of the named source
corner in that selected component.  Once both pointed corners have this
orientation, the same-endpoint and opposite-endpoint allocations both produce
an explicit replacement walk of length at most two.

This module proves that reduction and consumes the complete allocation.  It
does not yet prove the two source-corner membership facts, splice the bypass
into the retained rail, prove companion separation, iterate the rolling
transition, attach end caps, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathPointedOccurrence
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
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
    {web : Instance data coloring}

/-- A source corner lying in the selected square component is one of the two
literal endpoints of its internal bond. -/
theorem SelectedAdjacentTerminalEdgeCrossingOrigin.corner_eq_first_or_second_of_mem_component
    {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {edge : Sym2 (SelectedFace web)}
    (origin : SelectedAdjacentTerminalEdgeCrossingOrigin
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement) edge)
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : MiddleReplacementShortDualCycle.SquareBondRealization cycle component}
    (hmem : origin.corner ∈ component.supp) :
    origin.corner = bond.first ∨ origin.corner = bond.second := by
  rw [bond.component_supp] at hmem
  simpa [Set.mem_insert_iff] using hmem

/-- Component-side orientation is the exact source premise needed to put a
pointed crossing in the two endpoint triangles' expanded edge packet. -/
theorem SelectedAdjacentTerminalEdgeCrossingOrigin.crossing_mem_endpointTrianglePacket_of_corner_mem_component
    {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {edge : Sym2 (SelectedFace web)}
    (origin : SelectedAdjacentTerminalEdgeCrossingOrigin
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement) edge)
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : MiddleReplacementShortDualCycle.SquareBondRealization cycle component}
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (hmem : origin.corner ∈ component.supp) :
    origin.toCrossingReceipt.crossing ∈
      insert bond.internalEdge cycle.selectedCycle.crossingEdges := by
  exact origin.crossing_mem_endpointTrianglePacket_of_corner_eq_endpoint hroot
    (origin.corner_eq_first_or_second_of_mem_component hmem)

/-- A direct predecessor--successor adjacency is itself a one-edge pointed
bypass. -/
theorem InteriorOccurrence.exists_twoHopBypass_of_adjacent
    {start finish current : SelectedFace web}
    {rail : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) rail)
    (hadj : (SelectedDualGraph web).Adj
      occurrence.predecessor occurrence.successor) :
    Nonempty (InteriorOccurrence.TwoHopBypass occurrence) := by
  exact ⟨{
    walk := .cons hadj .nil
    length_le_two := by simp
    current_not_mem_support := by
      simp [occurrence.predecessor_ne_current.symm,
        occurrence.current_ne_successor]
  }⟩

/-- **L1 component-oriented pointed bypass.**  If both named source corners
lie on the selected two-vertex side, the exact endpoint triangles always
supply a collision-free replacement walk of length at most two.  The theorem
constructively consumes both the same-endpoint and opposite-endpoint cases. -/
theorem InteriorOccurrence.exists_twoHopBypass_of_crossingOrigins_of_corners_mem_component
    {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {start finish current : SelectedFace web}
    {rail : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) rail)
    (hpath : rail.IsPath)
    (incomingOrigin : SelectedAdjacentTerminalEdgeCrossingOrigin
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      occurrence.incomingEdge)
    (outgoingOrigin : SelectedAdjacentTerminalEdgeCrossingOrigin
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      occurrence.outgoingEdge)
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : MiddleReplacementShortDualCycle.SquareBondRealization cycle component}
    (firstTriangle secondTriangle : bond.EndpointSelectedTriangle)
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (hunion :
      firstTriangle.selectedCycle.crossingEdges ∪
          secondTriangle.selectedCycle.crossingEdges =
        insert bond.internalEdge cycle.selectedCycle.crossingEdges)
    (hinter : firstTriangle.selectedCycle.crossingEdges ∩
        secondTriangle.selectedCycle.crossingEdges = {bond.internalEdge})
    (hincomingMem : incomingOrigin.corner ∈ component.supp)
    (houtgoingMem : outgoingOrigin.corner ∈ component.supp) :
    Nonempty (InteriorOccurrence.TwoHopBypass occurrence) := by
  have hallocation :=
    InteriorOccurrence.endpointTriangle_bypass_or_opposite_of_crossingReceipts_of_union
      occurrence hpath incomingOrigin.toCrossingReceipt
      outgoingOrigin.toCrossingReceipt firstTriangle secondTriangle hunion
      (incomingOrigin
        |>.crossing_mem_endpointTrianglePacket_of_corner_mem_component
          hroot hincomingMem)
      (outgoingOrigin
        |>.crossing_mem_endpointTrianglePacket_of_corner_mem_component
          hroot houtgoingMem)
  rcases hallocation with hadj | hopposite
  · exact InteriorOccurrence.exists_twoHopBypass_of_adjacent occurrence hadj
  · exact InteriorOccurrence.exists_twoHopBypass_of_opposite_endpointTriangles
      occurrence hpath firstTriangle secondTriangle hinter hopposite

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
