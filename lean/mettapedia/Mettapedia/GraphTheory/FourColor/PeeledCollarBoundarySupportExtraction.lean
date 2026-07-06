import Mettapedia.GraphTheory.FourColor.PeeledCollarCutLiftBoundarySupport

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V W : Type*} [DecidableEq V]

/--
The vertex carrier cut out by the endpoint support of a finite ambient edge
set.
-/
abbrev BoundaryEdgeSetEndpointVertex {G : SimpleGraph V}
    (edges : Finset G.edgeSet) : Type _ :=
  {v : V // v ∈ boundaryEdgeSetEndpointSupport edges}

/--
The canonical graph carried by the endpoint support of a finite ambient edge
set: the full ambient graph induced on those endpoints.
-/
abbrev BoundaryEdgeSetInducedGraph {G : SimpleGraph V}
    (edges : Finset G.edgeSet) :
    SimpleGraph (BoundaryEdgeSetEndpointVertex (G := G) edges) :=
  G.induce {v : V | v ∈ boundaryEdgeSetEndpointSupport edges}

/--
The natural embedding of the endpoint-support induced graph into the ambient
graph.
-/
def boundaryEdgeSetInducedGraphEmbedding {G : SimpleGraph V}
    (edges : Finset G.edgeSet) :
    BoundaryEdgeSetInducedGraph (G := G) edges ↪g G where
  toFun v := v.1
  inj' u v h := Subtype.ext h
  map_rel_iff' := by
    intro u v
    rfl

@[simp]
theorem boundaryEdgeSetInducedGraphEmbedding_apply {G : SimpleGraph V}
    (edges : Finset G.edgeSet)
    (v : BoundaryEdgeSetEndpointVertex (G := G) edges) :
    boundaryEdgeSetInducedGraphEmbedding (G := G) edges v = v.1 :=
  rfl

@[simp]
theorem boundaryEdgeSetEndpointVertex_mem {G : SimpleGraph V}
    {edges : Finset G.edgeSet}
    (v : BoundaryEdgeSetEndpointVertex (G := G) edges) :
    (v : V) ∈ boundaryEdgeSetEndpointSupport edges :=
  v.2

/--
Every endpoint-support vertex has the tautological preimage under the induced
graph embedding.
-/
theorem exists_preimage_boundaryEdgeSetInducedGraphEmbedding_of_mem_endpointSupport
    {G : SimpleGraph V} {edges : Finset G.edgeSet} {v : V}
    (hv : v ∈ boundaryEdgeSetEndpointSupport edges) :
    ∃ w : BoundaryEdgeSetEndpointVertex (G := G) edges,
      boundaryEdgeSetInducedGraphEmbedding (G := G) edges w = v :=
  ⟨⟨v, hv⟩, rfl⟩

/--
If every endpoint of an ambient edge lies in a finite edge set's endpoint
support, then that ambient edge has a preimage in the endpoint-support induced
graph.
-/
theorem exists_edge_preimage_boundaryEdgeSetInducedGraphEmbedding_of_endpoint_subset
    {G : SimpleGraph V} {edges : Finset G.edgeSet} {e : G.edgeSet}
    (hEndpoints :
      ∀ v : V, v ∈ (e : Sym2 V) →
        v ∈ boundaryEdgeSetEndpointSupport edges) :
    ∃ eH : (BoundaryEdgeSetInducedGraph (G := G) edges).edgeSet,
      (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet eH = e :=
  SimpleGraph.Embedding.edge_preimage_of_forall_mem_range
    (boundaryEdgeSetInducedGraphEmbedding (G := G) edges)
    (fun v hv =>
      exists_preimage_boundaryEdgeSetInducedGraphEmbedding_of_mem_endpointSupport
        (hEndpoints v hv))

/--
Every selected edge of the finite boundary set has a preimage in the
endpoint-support induced graph.
-/
theorem exists_edge_preimage_boundaryEdgeSetInducedGraphEmbedding_of_mem_edges
    {G : SimpleGraph V} {edges : Finset G.edgeSet} {e : G.edgeSet}
    (he : e ∈ edges) :
    ∃ eH : (BoundaryEdgeSetInducedGraph (G := G) edges).edgeSet,
      (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet eH = e :=
  exists_edge_preimage_boundaryEdgeSetInducedGraphEmbedding_of_endpoint_subset
    (G := G) (edges := edges) (e := e)
    (fun _ hv => (mem_boundaryEdgeSetEndpointSupport_iff edges).2 ⟨e, he, hv⟩)

/--
Mapped collar-cut edges have preimages in the canonical graph induced by their
ambient endpoint support.
-/
theorem exists_edge_preimage_boundaryEdgeSetInducedGraphEmbedding_of_mem_mappedCut
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H} {e : G.edgeSet}
    (he : e ∈ cut.edgeCut.map φ.mapEdgeSet) :
    ∃ eK :
      (BoundaryEdgeSetInducedGraph (G := G)
        (cut.edgeCut.map φ.mapEdgeSet)).edgeSet,
      (boundaryEdgeSetInducedGraphEmbedding (G := G)
        (cut.edgeCut.map φ.mapEdgeSet)).mapEdgeSet eK = e :=
  exists_edge_preimage_boundaryEdgeSetInducedGraphEmbedding_of_mem_edges
    (G := G) (edges := cut.edgeCut.map φ.mapEdgeSet) he

/--
Under the finite no-boundary-chord condition, every edge of the
endpoint-support induced graph maps back into the selected finite edge set.
-/
theorem boundaryEdgeSetInducedGraphEmbedding_mapEdgeSet_mem_of_inducedSubgraph
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hInduced : BoundaryEdgeSetInducedSubgraph edges)
    (eH : (BoundaryEdgeSetInducedGraph (G := G) edges).edgeSet) :
    (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet eH ∈ edges := by
  apply hInduced
  intro v hv
  have hpreimage :
      ∃ w : BoundaryEdgeSetEndpointVertex (G := G) edges,
        w ∈ (eH : Sym2 (BoundaryEdgeSetEndpointVertex (G := G) edges)) ∧
          boundaryEdgeSetInducedGraphEmbedding (G := G) edges w = v := by
    simpa [SimpleGraph.Embedding.mapEdgeSet, SimpleGraph.Hom.mapEdgeSet,
      Sym2.mem_map] using hv
  rcases hpreimage with ⟨w, _hw, hw⟩
  rw [← hw]
  exact boundaryEdgeSetEndpointVertex_mem w

/--
Boundary-edge induced graph target: the finite edge set is exactly represented
by the canonical endpoint-support induced graph when selected edges lift and
the no-boundary-chord condition pushes induced edges back into the selection.
-/
def BoundaryEdgeSetInducedGraphRepresents
    {G : SimpleGraph V} (edges : Finset G.edgeSet) : Prop :=
  (∀ e : G.edgeSet, e ∈ edges →
    ∃ eH : (BoundaryEdgeSetInducedGraph (G := G) edges).edgeSet,
      (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet eH = e) ∧
    (∀ eH : (BoundaryEdgeSetInducedGraph (G := G) edges).edgeSet,
      (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet eH ∈ edges)

/--
Finite no-boundary-chord data identify the endpoint-support induced graph with
the selected edge set, in the edge-image sense needed by the collar route.
-/
theorem boundaryEdgeSetInducedGraph_represents_of_inducedSubgraph
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hInduced : BoundaryEdgeSetInducedSubgraph edges) :
    BoundaryEdgeSetInducedGraphRepresents (G := G) edges := by
  constructor
  · intro e he
    exact exists_edge_preimage_boundaryEdgeSetInducedGraphEmbedding_of_mem_edges
      (G := G) (edges := edges) he
  · exact boundaryEdgeSetInducedGraphEmbedding_mapEdgeSet_mem_of_inducedSubgraph
      (G := G) (edges := edges) hInduced

end Mettapedia.GraphTheory.FourColor
