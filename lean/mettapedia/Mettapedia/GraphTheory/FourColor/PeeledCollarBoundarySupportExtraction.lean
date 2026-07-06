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
The finite edge carrier itself, restricted to a chosen boundary edge set.
-/
abbrev BoundaryEdgeSetEdgeVertex {G : SimpleGraph V}
    (edges : Finset G.edgeSet) : Type _ :=
  {e : G.edgeSet // e ∈ edges}

/--
The shared-endpoint graph on a finite selected boundary edge set.

This is the edge-level carrier used to turn boundary-edge connectivity into
walks in the endpoint-support induced graph.
-/
def BoundaryEdgeSetSharedEndpointGraph {G : SimpleGraph V}
    (edges : Finset G.edgeSet) :
    SimpleGraph (BoundaryEdgeSetEdgeVertex (G := G) edges) where
  Adj e f := e ≠ f ∧ ∃ v : V, v ∈ (e.1 : Sym2 V) ∧ v ∈ (f.1 : Sym2 V)
  symm := ⟨by
    intro e f h
    rcases h with ⟨hne, v, hvE, hvF⟩
    exact ⟨hne.symm, v, hvF, hvE⟩
  ⟩
  loopless := ⟨fun e h => h.1 rfl⟩

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
An endpoint of a selected ambient edge is a vertex of the canonical
endpoint-support induced graph.
-/
def boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
    {G : SimpleGraph V} {edges : Finset G.edgeSet} {e : G.edgeSet}
    (he : e ∈ edges) {v : V} (hv : v ∈ (e : Sym2 V)) :
    BoundaryEdgeSetEndpointVertex (G := G) edges :=
  ⟨v, (mem_boundaryEdgeSetEndpointSupport_iff edges).2 ⟨e, he, hv⟩⟩

@[simp]
theorem boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint_val
    {G : SimpleGraph V} {edges : Finset G.edgeSet} {e : G.edgeSet}
    (he : e ∈ edges) {v : V} (hv : v ∈ (e : Sym2 V)) :
    (boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
      (G := G) (edges := edges) he hv : V) = v :=
  rfl

/--
Two distinct endpoints of a selected ambient edge are adjacent in the
canonical endpoint-support induced graph.
-/
theorem boundaryEdgeSetInducedGraph_adj_of_mem_edge_endpoints
    {G : SimpleGraph V} {edges : Finset G.edgeSet} {e : G.edgeSet}
    (he : e ∈ edges) {u v : V}
    (hu : u ∈ (e : Sym2 V)) (hv : v ∈ (e : Sym2 V)) (hne : u ≠ v) :
    (BoundaryEdgeSetInducedGraph (G := G) edges).Adj
      (boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
        (G := G) (edges := edges) he hu)
      (boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
        (G := G) (edges := edges) he hv) := by
  have heq : (e : Sym2 V) = s(u, v) :=
    sym2_eq_mk_of_mem_of_mem_of_ne hu hv hne
  have hadj : G.Adj u v :=
    (SimpleGraph.mem_edgeSet G).1 (by simpa [heq] using e.property)
  exact hadj

/--
Any two endpoints of a selected ambient edge are connected by a carrier walk in
the canonical endpoint-support induced graph.
-/
def boundaryEdgeSetInducedGraph_walk_of_mem_edge_endpoints
    {G : SimpleGraph V} {edges : Finset G.edgeSet} {e : G.edgeSet}
    (he : e ∈ edges) {u v : V}
    (hu : u ∈ (e : Sym2 V)) (hv : v ∈ (e : Sym2 V)) :
    (BoundaryEdgeSetInducedGraph (G := G) edges).Walk
      (boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
        (G := G) (edges := edges) he hu)
      (boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
        (G := G) (edges := edges) he hv) := by
  by_cases hne : u = v
  · subst hne
    exact SimpleGraph.Walk.nil
  · exact SimpleGraph.Walk.cons
      (boundaryEdgeSetInducedGraph_adj_of_mem_edge_endpoints
        (G := G) (edges := edges) he hu hv hne)
      SimpleGraph.Walk.nil

/--
If two selected ambient edges share an endpoint, then the corresponding
endpoint-support carrier vertices are connected through that shared endpoint.
This is the graph-level bridge from the selected-boundary shared-endpoint graph
to walks in the canonical endpoint-support carrier.
-/
def boundaryEdgeSetInducedGraph_walk_of_mem_edges_share_endpoint
    {G : SimpleGraph V} {edges : Finset G.edgeSet} {e f : G.edgeSet}
    (he : e ∈ edges) (hf : f ∈ edges) {u v x : V}
    (hu : u ∈ (e : Sym2 V)) (hxE : x ∈ (e : Sym2 V))
    (hxF : x ∈ (f : Sym2 V)) (hv : v ∈ (f : Sym2 V)) :
    (BoundaryEdgeSetInducedGraph (G := G) edges).Walk
      (boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
        (G := G) (edges := edges) he hu)
      (boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
        (G := G) (edges := edges) hf hv) := by
  have hx :
      boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
          (G := G) (edges := edges) he hxE =
        boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
          (G := G) (edges := edges) hf hxF :=
    Subtype.ext rfl
  cases hx
  exact
    (boundaryEdgeSetInducedGraph_walk_of_mem_edge_endpoints
      (G := G) (edges := edges) he hu hxE).append
      (boundaryEdgeSetInducedGraph_walk_of_mem_edge_endpoints
        (G := G) (edges := edges) hf hxF hv)

/--
A shared-endpoint walk of selected boundary edges induces a walk in the
canonical endpoint-support carrier between any chosen endpoint of the first
edge and any chosen endpoint of the last edge.
-/
theorem exists_boundaryEdgeSetInducedGraph_walk_of_sharedEndpointGraph_walk
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {e f : BoundaryEdgeSetEdgeVertex (G := G) edges}
    (p : (BoundaryEdgeSetSharedEndpointGraph (G := G) edges).Walk e f)
    {u v : V} (hu : u ∈ (e.1 : Sym2 V)) (hv : v ∈ (f.1 : Sym2 V)) :
    ∃ _ : (BoundaryEdgeSetInducedGraph (G := G) edges).Walk
      (boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
        (G := G) (edges := edges) e.2 hu)
      (boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
        (G := G) (edges := edges) f.2 hv), True := by
  induction p generalizing u v with
  | @nil g =>
      exact ⟨boundaryEdgeSetInducedGraph_walk_of_mem_edge_endpoints
        (G := G) (edges := edges) g.2 hu hv, trivial⟩
  | @cons e₀ e₁ e₂ hadj p ih =>
      rcases hadj with ⟨_hne, x, hx₀, hx₁⟩
      rcases ih hx₁ hv with ⟨tail, _⟩
      exact ⟨
        (boundaryEdgeSetInducedGraph_walk_of_mem_edges_share_endpoint
          (G := G) (edges := edges) e₀.2 e₁.2 hu hx₀ hx₁ hx₁).append
          tail,
        trivial⟩

/--
Reachability in the shared-endpoint graph of selected boundary edges induces a
carrier walk between any chosen endpoint of the first edge and any chosen
endpoint of the last edge.
-/
theorem exists_boundaryEdgeSetInducedGraph_walk_of_sharedEndpointGraph_reachable
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {e f : BoundaryEdgeSetEdgeVertex (G := G) edges}
    (hreachable : (BoundaryEdgeSetSharedEndpointGraph (G := G) edges).Reachable e f)
    {u v : V} (hu : u ∈ (e.1 : Sym2 V)) (hv : v ∈ (f.1 : Sym2 V)) :
    ∃ _ : (BoundaryEdgeSetInducedGraph (G := G) edges).Walk
      (boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
        (G := G) (edges := edges) e.2 hu)
      (boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
        (G := G) (edges := edges) f.2 hv), True := by
  rcases hreachable with ⟨p⟩
  exact exists_boundaryEdgeSetInducedGraph_walk_of_sharedEndpointGraph_walk
    (G := G) (edges := edges) p hu hv

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
