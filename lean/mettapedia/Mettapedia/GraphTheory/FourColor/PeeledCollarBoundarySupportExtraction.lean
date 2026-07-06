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
Every carrier edge used by the canonical endpoint walk for one selected
ambient edge maps back to that selected ambient edge.
-/
theorem boundaryEdgeSetInducedGraph_walk_of_mem_edge_endpoints_mapEdgeSet
    {G : SimpleGraph V} {edges : Finset G.edgeSet} {e : G.edgeSet}
    (he : e ∈ edges) {u v : V}
    (hu : u ∈ (e : Sym2 V)) (hv : v ∈ (e : Sym2 V))
    (eH : (BoundaryEdgeSetInducedGraph (G := G) edges).edgeSet)
    (heH :
      (eH : Sym2 (BoundaryEdgeSetEndpointVertex (G := G) edges)) ∈
        (boundaryEdgeSetInducedGraph_walk_of_mem_edge_endpoints
          (G := G) (edges := edges) he hu hv).edges) :
    (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet eH = e := by
  by_cases hne : u = v
  · subst hne
    simp [boundaryEdgeSetInducedGraph_walk_of_mem_edge_endpoints] at heH
  · have hcarrier :
        (eH : Sym2 (BoundaryEdgeSetEndpointVertex (G := G) edges)) =
          s(boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
              (G := G) (edges := edges) he hu,
            boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
              (G := G) (edges := edges) he hv) := by
      simpa [boundaryEdgeSetInducedGraph_walk_of_mem_edge_endpoints, hne,
        SimpleGraph.Walk.edges_cons] using heH
    have hambient : (e : Sym2 V) = s(u, v) :=
      sym2_eq_mk_of_mem_of_mem_of_ne hu hv hne
    apply Subtype.ext
    simp [SimpleGraph.Embedding.mapEdgeSet, SimpleGraph.Hom.mapEdgeSet,
      hcarrier, hambient]

/--
If a selected ambient edge is outside a carrier cut's mapped edge set, then
the canonical endpoint walk for that edge avoids the carrier cut.
-/
theorem boundaryEdgeSetInducedGraph_walk_of_mem_edge_endpoints_avoids_cut
    {G : SimpleGraph V} {edges : Finset G.edgeSet} {e : G.edgeSet}
    (he : e ∈ edges) {u v : V}
    (hu : u ∈ (e : Sym2 V)) (hv : v ∈ (e : Sym2 V))
    (cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges))
    (heAvoid :
      e ∉ cut.edgeCut.map
        (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet) :
    ∀ eH : (BoundaryEdgeSetInducedGraph (G := G) edges).edgeSet,
      eH ∈ cut.edgeCut →
        (eH : Sym2 (BoundaryEdgeSetEndpointVertex (G := G) edges)) ∉
          (boundaryEdgeSetInducedGraph_walk_of_mem_edge_endpoints
            (G := G) (edges := edges) he hu hv).edges := by
  intro eH hcut hmem
  exact heAvoid (Finset.mem_map.2
    ⟨eH, hcut,
      boundaryEdgeSetInducedGraph_walk_of_mem_edge_endpoints_mapEdgeSet
        (G := G) (edges := edges) he hu hv eH hmem⟩)

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
Every carrier edge used by the canonical shared-endpoint step maps back to one
of the two selected ambient edges that form that step.
-/
theorem boundaryEdgeSetInducedGraph_walk_of_mem_edges_share_endpoint_mapEdgeSet
    {G : SimpleGraph V} {edges : Finset G.edgeSet} {e f : G.edgeSet}
    (he : e ∈ edges) (hf : f ∈ edges) {u v x : V}
    (hu : u ∈ (e : Sym2 V)) (hxE : x ∈ (e : Sym2 V))
    (hxF : x ∈ (f : Sym2 V)) (hv : v ∈ (f : Sym2 V))
    (eH : (BoundaryEdgeSetInducedGraph (G := G) edges).edgeSet)
    (heH :
      (eH : Sym2 (BoundaryEdgeSetEndpointVertex (G := G) edges)) ∈
        (boundaryEdgeSetInducedGraph_walk_of_mem_edges_share_endpoint
          (G := G) (edges := edges) he hf hu hxE hxF hv).edges) :
    (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet eH = e ∨
      (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet eH = f := by
  rw [boundaryEdgeSetInducedGraph_walk_of_mem_edges_share_endpoint,
    SimpleGraph.Walk.edges_append] at heH
  rcases List.mem_append.1 heH with heLeft | heRight
  · exact Or.inl
      (boundaryEdgeSetInducedGraph_walk_of_mem_edge_endpoints_mapEdgeSet
        (G := G) (edges := edges) he hu hxE eH heLeft)
  · exact Or.inr
      (boundaryEdgeSetInducedGraph_walk_of_mem_edge_endpoints_mapEdgeSet
        (G := G) (edges := edges) hf hxF hv eH heRight)

/--
If both selected ambient edges in a shared-endpoint step are outside a carrier
cut's mapped edge set, then the generated carrier walk avoids the carrier cut.
-/
theorem boundaryEdgeSetInducedGraph_walk_of_mem_edges_share_endpoint_avoids_cut
    {G : SimpleGraph V} {edges : Finset G.edgeSet} {e f : G.edgeSet}
    (he : e ∈ edges) (hf : f ∈ edges) {u v x : V}
    (hu : u ∈ (e : Sym2 V)) (hxE : x ∈ (e : Sym2 V))
    (hxF : x ∈ (f : Sym2 V)) (hv : v ∈ (f : Sym2 V))
    (cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges))
    (heAvoid :
      e ∉ cut.edgeCut.map
        (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet)
    (hfAvoid :
      f ∉ cut.edgeCut.map
        (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet) :
    ∀ eH : (BoundaryEdgeSetInducedGraph (G := G) edges).edgeSet,
      eH ∈ cut.edgeCut →
        (eH : Sym2 (BoundaryEdgeSetEndpointVertex (G := G) edges)) ∉
          (boundaryEdgeSetInducedGraph_walk_of_mem_edges_share_endpoint
            (G := G) (edges := edges) he hf hu hxE hxF hv).edges := by
  intro eH hcut hmem
  rcases boundaryEdgeSetInducedGraph_walk_of_mem_edges_share_endpoint_mapEdgeSet
      (G := G) (edges := edges) he hf hu hxE hxF hv eH hmem with hmap | hmap
  · exact heAvoid (Finset.mem_map.2 ⟨eH, hcut, hmap⟩)
  · exact hfAvoid (Finset.mem_map.2 ⟨eH, hcut, hmap⟩)

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
A shared-endpoint walk of selected boundary edges whose visited edges avoid a
mapped carrier cut induces a carrier walk avoiding that carrier cut.
-/
theorem
    exists_boundaryEdgeSetInducedGraph_walk_avoids_cut_of_sharedEndpointGraph_walk
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {e f : BoundaryEdgeSetEdgeVertex (G := G) edges}
    (p : (BoundaryEdgeSetSharedEndpointGraph (G := G) edges).Walk e f)
    (cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges))
    (hAvoid :
      ∀ g : BoundaryEdgeSetEdgeVertex (G := G) edges,
        g ∈ p.support →
          g.1 ∉ cut.edgeCut.map
            (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet)
    {u v : V} (hu : u ∈ (e.1 : Sym2 V)) (hv : v ∈ (f.1 : Sym2 V)) :
    ∃ q : (BoundaryEdgeSetInducedGraph (G := G) edges).Walk
      (boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
        (G := G) (edges := edges) e.2 hu)
      (boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
        (G := G) (edges := edges) f.2 hv),
        ∀ eH : (BoundaryEdgeSetInducedGraph (G := G) edges).edgeSet,
          eH ∈ cut.edgeCut →
            (eH : Sym2 (BoundaryEdgeSetEndpointVertex (G := G) edges)) ∉
              q.edges := by
  induction p generalizing u v with
  | @nil g =>
      exact ⟨boundaryEdgeSetInducedGraph_walk_of_mem_edge_endpoints
          (G := G) (edges := edges) g.2 hu hv,
        boundaryEdgeSetInducedGraph_walk_of_mem_edge_endpoints_avoids_cut
          (G := G) (edges := edges) g.2 hu hv cut
          (hAvoid g (by simp))⟩
  | @cons e₀ e₁ e₂ hadj p ih =>
      rcases hadj with ⟨_hne, x, hx₀, hx₁⟩
      have he₀Avoid :
          e₀.1 ∉ cut.edgeCut.map
            (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet :=
        hAvoid e₀ (by simp [SimpleGraph.Walk.support_cons])
      have he₁Avoid :
          e₁.1 ∉ cut.edgeCut.map
            (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet :=
        hAvoid e₁ (by simp [SimpleGraph.Walk.support_cons])
      have htailAvoid :
          ∀ g : BoundaryEdgeSetEdgeVertex (G := G) edges,
            g ∈ p.support →
              g.1 ∉ cut.edgeCut.map
                (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet := by
        intro g hg
        exact hAvoid g (by simp [SimpleGraph.Walk.support_cons, hg])
      rcases ih htailAvoid hx₁ hv with ⟨tail, htail⟩
      refine ⟨
        (boundaryEdgeSetInducedGraph_walk_of_mem_edges_share_endpoint
          (G := G) (edges := edges) e₀.2 e₁.2 hu hx₀ hx₁ hx₁).append
          tail,
        ?_⟩
      intro eH hcut hmem
      rw [SimpleGraph.Walk.edges_append] at hmem
      rcases List.mem_append.1 hmem with hfirst | htailMem
      · exact
          boundaryEdgeSetInducedGraph_walk_of_mem_edges_share_endpoint_avoids_cut
            (G := G) (edges := edges) e₀.2 e₁.2 hu hx₀ hx₁ hx₁
            cut he₀Avoid he₁Avoid eH hcut hfirst
      · exact htail eH hcut htailMem

/--
Cut-avoiding reachability in the shared-endpoint graph of selected boundary
edges: there is a shared-endpoint walk whose visited selected ambient edges all
avoid the mapped carrier cut.
-/
def BoundaryEdgeSetSharedEndpointMappedCutAvoidingReachable
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges))
    (e f : BoundaryEdgeSetEdgeVertex (G := G) edges) : Prop :=
  ∃ p : (BoundaryEdgeSetSharedEndpointGraph (G := G) edges).Walk e f,
    ∀ g : BoundaryEdgeSetEdgeVertex (G := G) edges,
      g ∈ p.support →
        g.1 ∉ cut.edgeCut.map
          (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet

/--
The named cut-avoiding shared-endpoint reachability target supplies a carrier
walk avoiding the carrier cut.
-/
theorem
    exists_boundaryEdgeSetInducedGraph_walk_avoids_cut_of_sharedEndpointGraph_cutAvoidingReachable
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    {e f : BoundaryEdgeSetEdgeVertex (G := G) edges}
    (hreachable :
      BoundaryEdgeSetSharedEndpointMappedCutAvoidingReachable
        (G := G) (edges := edges) cut e f)
    {u v : V} (hu : u ∈ (e.1 : Sym2 V)) (hv : v ∈ (f.1 : Sym2 V)) :
    ∃ q : (BoundaryEdgeSetInducedGraph (G := G) edges).Walk
      (boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
        (G := G) (edges := edges) e.2 hu)
      (boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
        (G := G) (edges := edges) f.2 hv),
        ∀ eH : (BoundaryEdgeSetInducedGraph (G := G) edges).edgeSet,
          eH ∈ cut.edgeCut →
            (eH : Sym2 (BoundaryEdgeSetEndpointVertex (G := G) edges)) ∉
              q.edges := by
  rcases hreachable with ⟨p, hAvoid⟩
  exact
    exists_boundaryEdgeSetInducedGraph_walk_avoids_cut_of_sharedEndpointGraph_walk
      (G := G) (edges := edges) p cut hAvoid hu hv

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
