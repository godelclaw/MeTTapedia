import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebBoundaryData

/-!
# Ordered annular boundary data across graph isomorphisms

An annular frontier datum consists not only of an underlying graph but also of
two ordered degree-one interfaces.  This file transports that complete datum
through a graph isomorphism and proves that graph-level well-formedness is
preserved.  It is carrier plumbing: it neither constructs an annular embedding
nor identifies the distinguished hole faces of a source opening.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularBoundaryIsoTransport

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData

variable {V W : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} {H : SimpleGraph W}
  [DecidableRel G.Adj] [DecidableRel H.Adj]

noncomputable section

/-- The equivalence of unordered vertex pairs induced by a graph isomorphism. -/
def sym2Equiv (iso : G ≃g H) : Sym2 V ≃ Sym2 W :=
  Equiv.ofBijective (Sym2.map iso) ⟨Sym2.map.injective iso.injective, by
    intro edge
    induction edge using Sym2.inductionOn with
    | _ left right => exact ⟨s(iso.symm left, iso.symm right), by simp⟩⟩

/-- The induced equivalence of graph edge subtypes. -/
def edgeEquiv (iso : G ≃g H) : G.edgeSet ≃ H.edgeSet :=
  (sym2Equiv iso).subtypeEquiv (fun edge => by
    induction edge using Sym2.inductionOn with
    | _ left right =>
      simpa [sym2Equiv] using ((iso.map_rel_iff).symm :
        G.Adj left right ↔ H.Adj (iso left) (iso right)))

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [DecidableRel G.Adj] [DecidableRel H.Adj] in
@[simp] theorem edgeEquiv_val (iso : G ≃g H) (edge : G.edgeSet) :
    (edgeEquiv iso edge).1 = Sym2.map iso edge.1 :=
  rfl

/-- Incident-edge membership is preserved by the induced edge equivalence. -/
theorem edgeEquiv_mem_incidentEdgeFinset_iff
    (iso : G ≃g H) (edge : G.edgeSet) (vertex : V) :
    edgeEquiv iso edge ∈ incidentEdgeFinset H (iso vertex) ↔
      edge ∈ incidentEdgeFinset G vertex := by
  rw [incidentEdgeFinset, incidentEdgeFinset]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right =>
    simp [edgeEquiv, sym2Equiv, Sym2.mem_iff]

/-- An isomorphism maps the complete incident-edge finite set at a vertex
onto the complete incident-edge finite set at its image. -/
theorem incidentEdgeFinset_map_edgeEquiv
    (iso : G ≃g H) (vertex : V) :
    (incidentEdgeFinset G vertex).map (edgeEquiv iso).toEmbedding =
      incidentEdgeFinset H (iso vertex) := by
  ext edge
  constructor
  · intro hmem
    rcases Finset.mem_map.mp hmem with ⟨source, hsource, hmap⟩
    subst edge
    exact (edgeEquiv_mem_incidentEdgeFinset_iff iso source vertex).mpr hsource
  · intro hmem
    let source := (edgeEquiv iso).symm edge
    have hsource : source ∈ incidentEdgeFinset G vertex :=
      (edgeEquiv_mem_incidentEdgeFinset_iff iso source vertex).mp (by
        simpa [source] using hmem)
    exact Finset.mem_map.mpr ⟨source, hsource, by simp [source]⟩

/-- In particular, all graph degrees expressed through `incidentEdgeFinset`
are invariant under a graph isomorphism. -/
theorem incidentEdgeFinset_card_iso (iso : G ≃g H) (vertex : V) :
    (incidentEdgeFinset H (iso vertex)).card =
      (incidentEdgeFinset G vertex).card := by
  rw [← incidentEdgeFinset_map_edgeEquiv iso vertex, Finset.card_map]

/-- Transport the two ordered boundary interfaces along a graph isomorphism. -/
def transport (iso : G ≃g H)
    {outerCount : Nat} (data : AnnularBoundaryData G outerCount) :
    AnnularBoundaryData H outerCount where
  innerStub := data.innerStub.trans iso.toEquiv.toEmbedding
  outerStub := data.outerStub.trans iso.toEquiv.toEmbedding
  innerBoundaryEdge := data.innerBoundaryEdge.trans (edgeEquiv iso).toEmbedding
  outerBoundaryEdge := data.outerBoundaryEdge.trans (edgeEquiv iso).toEmbedding

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [DecidableRel G.Adj] [DecidableRel H.Adj] in
@[simp] theorem transport_innerStub
    (iso : G ≃g H) {outerCount : Nat} (data : AnnularBoundaryData G outerCount)
    (inner : Fin 5) :
    (transport iso data).innerStub inner = iso (data.innerStub inner) :=
  rfl

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [DecidableRel G.Adj] [DecidableRel H.Adj] in
@[simp] theorem transport_outerStub
    (iso : G ≃g H) {outerCount : Nat} (data : AnnularBoundaryData G outerCount)
    (outer : Fin outerCount) :
    (transport iso data).outerStub outer = iso (data.outerStub outer) :=
  rfl

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [DecidableRel G.Adj] [DecidableRel H.Adj] in
@[simp] theorem transport_innerBoundaryEdge
    (iso : G ≃g H) {outerCount : Nat} (data : AnnularBoundaryData G outerCount)
    (inner : Fin 5) :
    (transport iso data).innerBoundaryEdge inner = edgeEquiv iso (data.innerBoundaryEdge inner) :=
  rfl

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [DecidableRel G.Adj] [DecidableRel H.Adj] in
@[simp] theorem transport_outerBoundaryEdge
    (iso : G ≃g H) {outerCount : Nat} (data : AnnularBoundaryData G outerCount)
    (outer : Fin outerCount) :
    (transport iso data).outerBoundaryEdge outer = edgeEquiv iso (data.outerBoundaryEdge outer) :=
  rfl

/-- Graph-level well-formedness of the two interfaces is invariant under
graph isomorphism.  Thus an opening comparison transports actual boundary
data, not only its vertex carrier. -/
theorem wellFormed_transport
    (iso : G ≃g H) {outerCount : Nat} (data : AnnularBoundaryData G outerCount)
    (hdata : data.WellFormed) :
    (transport iso data).WellFormed := by
  refine {
    inner_outer_stub_disjoint := ?_,
    inner_outer_edge_disjoint := ?_,
    innerBoundaryEdge_incident := ?_,
    outerBoundaryEdge_incident := ?_,
    inner_stub_degree_one := ?_,
    outer_stub_degree_one := ?_,
    cubic_elsewhere := ?_ }
  · intro inner outer heq
    apply hdata.inner_outer_stub_disjoint inner outer
    apply iso.injective
    simpa using heq
  · intro inner outer heq
    apply hdata.inner_outer_edge_disjoint inner outer
    apply (edgeEquiv iso).injective
    simpa using heq
  · intro inner
    rw [transport_innerBoundaryEdge, transport_innerStub]
    exact (edgeEquiv_mem_incidentEdgeFinset_iff iso _ _).mpr
      (hdata.innerBoundaryEdge_incident inner)
  · intro outer
    rw [transport_outerBoundaryEdge, transport_outerStub]
    exact (edgeEquiv_mem_incidentEdgeFinset_iff iso _ _).mpr
      (hdata.outerBoundaryEdge_incident outer)
  · intro inner
    rw [transport_innerStub, incidentEdgeFinset_card_iso iso]
    exact hdata.inner_stub_degree_one inner
  · intro outer
    rw [transport_outerStub, incidentEdgeFinset_card_iso iso]
    exact hdata.outer_stub_degree_one outer
  · intro vertex hinner houter
    have hsourceInner : ∀ inner, iso.symm vertex ≠ data.innerStub inner := by
      intro inner heq
      apply hinner inner
      simpa only [transport_innerStub, iso.apply_symm_apply] using congrArg iso heq
    have hsourceOuter : ∀ outer, iso.symm vertex ≠ data.outerStub outer := by
      intro outer heq
      apply houter outer
      simpa only [transport_outerStub, iso.apply_symm_apply] using congrArg iso heq
    calc
      (incidentEdgeFinset H vertex).card =
          (incidentEdgeFinset G (iso.symm vertex)).card := by
        simpa using incidentEdgeFinset_card_iso iso (iso.symm vertex)
      _ = 3 := hdata.cubic_elsewhere (iso.symm vertex) hsourceInner hsourceOuter

end

end GoertzelV24AnnularBoundaryIsoTransport

end Mettapedia.GraphTheory.FourColor
