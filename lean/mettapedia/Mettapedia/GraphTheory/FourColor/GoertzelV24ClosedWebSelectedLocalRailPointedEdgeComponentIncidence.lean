import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeComponentOrientation

/-!
# L1: characterize the square packet by component incidence

The selected square residue has exactly two vertices.  Its endpoint-triangle
packet is therefore characterized without choosing an orientation: a primal
edge lies in the packet exactly when one of its endpoints lies in the selected
component.  This is weaker and more intrinsic than requiring the named source
corner of a pointed crossing to lie on that side.

The characterization lets the complete endpoint-triangle allocation construct
a two-hop bypass from two edge/component incidence receipts.  It does not yet
prove those incidences for the literal first-window crossings, splice the
bypass into the retained rail, prove companion separation, iterate the rolling
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

/-- An edge belongs to the two endpoint triangles' exact packet precisely when
it meets the selected two-vertex component.  The statement chooses neither an
endpoint of the edge nor an orientation of the square bond. -/
theorem MiddleReplacementShortDualCycle.SquareBondRealization.edge_mem_endpointTrianglePacket_iff_meets_component
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : MiddleReplacementShortDualCycle.SquareBondRealization cycle component)
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (edge : G.edgeSet) :
    edge ∈ insert bond.internalEdge cycle.selectedCycle.crossingEdges ↔
      ∃ vertex, vertex ∈ (edge.1 : Sym2 V) ∧ vertex ∈ component.supp := by
  rw [← bond.incidentEdgeFinset_union_eq_insert_internalEdge hroot]
  constructor
  · intro hedge
    rcases Finset.mem_union.1 hedge with hfirst | hsecond
    · refine ⟨bond.first, ?_, ?_⟩
      · simpa [incidentEdgeFinset] using hfirst
      · rw [bond.component_supp]
        simp
    · refine ⟨bond.second, ?_, ?_⟩
      · simpa [incidentEdgeFinset] using hsecond
      · rw [bond.component_supp]
        simp
  · rintro ⟨vertex, hvertexEdge, hvertexComponent⟩
    rw [bond.component_supp] at hvertexComponent
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvertexComponent
    rcases hvertexComponent with rfl | rfl
    · exact Finset.mem_union.2 (.inl (by
        simpa [incidentEdgeFinset] using hvertexEdge))
    · exact Finset.mem_union.2 (.inr (by
        simpa [incidentEdgeFinset] using hvertexEdge))

/-- A pointed crossing that meets the selected square component belongs to the
exact packet consumed by the endpoint-triangle comparison. -/
theorem SelectedAdjacentTerminalEdgeCrossingReceipt.crossing_mem_endpointTrianglePacket_of_meets_component
    {edge : Sym2 (SelectedFace web)}
    (receipt : SelectedAdjacentTerminalEdgeCrossingReceipt edge)
    {face : SelectedFace web}
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    {bond : MiddleReplacementShortDualCycle.SquareBondRealization cycle component}
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (hmeets : ∃ vertex,
      vertex ∈ (receipt.crossing.1 : Sym2 V) ∧ vertex ∈ component.supp) :
    receipt.crossing ∈
      insert bond.internalEdge cycle.selectedCycle.crossingEdges := by
  exact (bond.edge_mem_endpointTrianglePacket_iff_meets_component
    hroot receipt.crossing).2 hmeets

/-- **L1 component-incidence pointed bypass.**  If both literal pointed
crossings meet the selected two-vertex component, the exact endpoint triangles
construct a collision-free replacement walk of length at most two.  No named
corner or bond orientation is assumed. -/
theorem InteriorOccurrence.exists_twoHopBypass_of_crossingReceipts_of_meet_component
    {start finish current : SelectedFace web}
    {rail : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) rail)
    (hpath : rail.IsPath)
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
    (firstTriangle secondTriangle : bond.EndpointSelectedTriangle)
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (hunion :
      firstTriangle.selectedCycle.crossingEdges ∪
          secondTriangle.selectedCycle.crossingEdges =
        insert bond.internalEdge cycle.selectedCycle.crossingEdges)
    (hinter : firstTriangle.selectedCycle.crossingEdges ∩
        secondTriangle.selectedCycle.crossingEdges = {bond.internalEdge})
    (hincomingMeets : ∃ vertex,
      vertex ∈ (incomingReceipt.crossing.1 : Sym2 V) ∧
        vertex ∈ component.supp)
    (houtgoingMeets : ∃ vertex,
      vertex ∈ (outgoingReceipt.crossing.1 : Sym2 V) ∧
        vertex ∈ component.supp) :
    Nonempty (InteriorOccurrence.TwoHopBypass occurrence) := by
  have hallocation :=
    InteriorOccurrence.endpointTriangle_bypass_or_opposite_of_crossingReceipts_of_union
      occurrence hpath incomingReceipt outgoingReceipt firstTriangle
      secondTriangle hunion
      (incomingReceipt
        |>.crossing_mem_endpointTrianglePacket_of_meets_component
          hroot hincomingMeets)
      (outgoingReceipt
        |>.crossing_mem_endpointTrianglePacket_of_meets_component
          hroot houtgoingMeets)
  rcases hallocation with hadj | hopposite
  · exact InteriorOccurrence.exists_twoHopBypass_of_adjacent occurrence hadj
  · exact InteriorOccurrence.exists_twoHopBypass_of_opposite_endpointTriangles
      occurrence hpath firstTriangle secondTriangle hinter hopposite

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
