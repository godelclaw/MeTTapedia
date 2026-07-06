import Mettapedia.GraphTheory.FourColor.PeeledCollarBoundaryCarrierEndpointRange
import Mettapedia.GraphTheory.FourColor.PeeledCollarCutLiftLocalConstancy

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/--
An ambient edge touches the outside of a finite vertex support when at least
one of its endpoints is not in that support.
-/
def EdgeTouchesOutsideVertexSupport (support : Finset V) (e : Sym2 V) : Prop :=
  ∃ v : V, v ∈ e ∧ v ∉ support

/--
An ambient walk is off-carrier when every traversed edge touches the outside
of the finite carrier support.
-/
def WalkUsesOnlyEdgesTouchingOutsideVertexSupport
    {G : SimpleGraph V} (support : Finset V) {u v : V}
    (p : G.Walk u v) : Prop :=
  ∀ e : Sym2 V, e ∈ p.edges → EdgeTouchesOutsideVertexSupport support e

/--
Off-carrier reachability between two ambient vertices.
-/
def OffCarrierReachable
    (G : SimpleGraph V) (support : Finset V) (u v : V) : Prop :=
  ∃ p : G.Walk u v, WalkUsesOnlyEdgesTouchingOutsideVertexSupport support p

namespace OffCarrierReachable

omit [DecidableEq V] in
/-- Reflexivity of off-carrier reachability. -/
theorem refl {G : SimpleGraph V} {support : Finset V} (u : V) :
    OffCarrierReachable G support u u := by
  refine ⟨SimpleGraph.Walk.nil, ?_⟩
  intro e he
  simp at he

omit [DecidableEq V] in
/-- Off-carrier walks compose. -/
theorem trans {G : SimpleGraph V} {support : Finset V} {u v w : V}
    (huv : OffCarrierReachable G support u v)
    (hvw : OffCarrierReachable G support v w) :
    OffCarrierReachable G support u w := by
  rcases huv with ⟨p, hp⟩
  rcases hvw with ⟨q, hq⟩
  refine ⟨p.append q, ?_⟩
  intro e he
  rw [SimpleGraph.Walk.edges_append] at he
  rcases List.mem_append.1 he with heP | heQ
  · exact hp e heP
  · exact hq e heQ

omit [DecidableEq V] in
/-- Off-carrier reachability is symmetric. -/
theorem symm {G : SimpleGraph V} {support : Finset V} {u v : V}
    (huv : OffCarrierReachable G support u v) :
    OffCarrierReachable G support v u := by
  rcases huv with ⟨p, hp⟩
  refine ⟨p.reverse, ?_⟩
  intro e he
  exact hp e (by simpa [SimpleGraph.Walk.edges_reverse] using he)

/--
One ambient edge whose endpoint leaves the support gives off-carrier
reachability between any two listed endpoints of that edge.
-/
theorem of_edge_endpoint_outside
    {G : SimpleGraph V} {support : Finset V} {e : G.edgeSet} {u v : V}
    (hu : u ∈ (e : Sym2 V)) (hv : v ∈ (e : Sym2 V))
    (hoff : EdgeTouchesOutsideVertexSupport support (e : Sym2 V)) :
    OffCarrierReachable G support u v := by
  by_cases huv : u = v
  · subst huv
    exact refl u
  · have heq : (e : Sym2 V) = s(u, v) :=
      sym2_eq_mk_of_mem_of_mem_of_ne hu hv huv
    have hadj : G.Adj u v :=
      (SimpleGraph.mem_edgeSet G).1 (by simpa [heq] using e.property)
    refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
    intro f hf
    have hf_eq : f = (e : Sym2 V) := by
      simpa [SimpleGraph.Walk.edges_cons, heq] using hf
    simpa [hf_eq] using hoff

end OffCarrierReachable

/-- Endpoint support is monotone in the selected finite edge set. -/
theorem boundaryEdgeSetEndpointSupport_mono
    {G : SimpleGraph V} {edges₁ edges₂ : Finset G.edgeSet}
    (hsubset : edges₁ ⊆ edges₂) :
    boundaryEdgeSetEndpointSupport edges₁ ⊆
      boundaryEdgeSetEndpointSupport edges₂ := by
  intro v hv
  rcases (mem_boundaryEdgeSetEndpointSupport_iff edges₁).1 hv with
    ⟨e, he, hve⟩
  exact (mem_boundaryEdgeSetEndpointSupport_iff edges₂).2
    ⟨e, hsubset he, hve⟩

omit [DecidableEq V] in
/--
Edge-local side constancy across every edge of an off-support walk makes the
side predicate constant between the walk endpoints.
-/
theorem EdgeSideLocallyConstantOffSupport.walk_side_iff
    {G : SimpleGraph V} {side : V → Prop} {support : Finset V}
    (hlocal : EdgeSideLocallyConstantOffSupport (G := G) side support)
    {u v : V} (p : G.Walk u v)
    (hp : WalkUsesOnlyEdgesTouchingOutsideVertexSupport support p) :
    side u ↔ side v := by
  constructor
  · intro hu
    by_contra hv
    rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides side p hu hv with
      ⟨e, he, hcross⟩
    exact
      (not_edgeCrossesVertexSide_of_edgeSideLocallyConstantOffSupport
        hlocal (hp e he)) hcross
  · intro hv
    by_contra hu
    rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides
        (fun x => ¬ side x) p hu (by simpa using hv) with
      ⟨e, he, hcross⟩
    have hcrossSide : EdgeCrossesVertexSide G side e :=
      (edgeCrossesVertexSide_compl G side e).1 hcross
    exact
      (not_edgeCrossesVertexSide_of_edgeSideLocallyConstantOffSupport
        hlocal (hp e he)) hcrossSide

/--
Ambient side obtained by filling a carrier cut through off-carrier
reachability from true-side carrier vertices.
-/
def boundaryEdgeSetInducedCutOffCarrierReachSide
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges))
    (v : V) : Prop :=
  ∃ w : BoundaryEdgeSetEndpointVertex (G := G) edges,
    cut.side w ∧
      OffCarrierReachable G (boundaryEdgeSetEndpointSupport edges) w v

/--
Off-carrier walk consistency for a cut of the canonical induced boundary
graph: off-carrier walks between carrier vertices preserve the carrier-side
predicate.
-/
def BoundaryEdgeSetInducedCutOffCarrierWalkConsistent
    {G : SimpleGraph V} (edges : Finset G.edgeSet)
    (cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)) :
    Prop :=
  ∀ a b : BoundaryEdgeSetEndpointVertex (G := G) edges,
    OffCarrierReachable G (boundaryEdgeSetEndpointSupport edges) a b →
      (cut.side a ↔ cut.side b)

/--
No off-carrier component joins opposite sides of a cut of the canonical
endpoint-support induced boundary graph.  This is the direct topological shape
expected from the annulus/Jordan layer.
-/
def BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnected
    {G : SimpleGraph V} (edges : Finset G.edgeSet)
    (cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)) :
    Prop :=
  ¬ ∃ a b : BoundaryEdgeSetEndpointVertex (G := G) edges,
    cut.side a ∧ ¬ cut.side b ∧
      OffCarrierReachable G (boundaryEdgeSetEndpointSupport edges) a b

/--
An ambient off-carrier component, represented by any ambient vertex `root`,
attaches to a carrier vertex when the root reaches that carrier vertex through
edges touching the outside of the carrier support.
-/
def BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
    {G : SimpleGraph V} (edges : Finset G.edgeSet) (root : V)
    (a : BoundaryEdgeSetEndpointVertex (G := G) edges) : Prop :=
  OffCarrierReachable G (boundaryEdgeSetEndpointSupport edges) root a

/--
Every off-carrier component has one-sided attachments to a given carrier cut:
no component representative reaches both a true-side and a false-side carrier
vertex.
-/
def BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachments
    {G : SimpleGraph V} (edges : Finset G.edgeSet)
    (cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)) :
    Prop :=
  ∀ root : V,
    ¬ ((∃ a : BoundaryEdgeSetEndpointVertex (G := G) edges,
          cut.side a ∧
            BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
              (G := G) edges root a) ∧
        (∃ b : BoundaryEdgeSetEndpointVertex (G := G) edges,
          ¬ cut.side b ∧
            BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
              (G := G) edges root b))

/--
Carrier-side connectivity target for an off-carrier component's attachments:
any two carrier vertices attached to the same off-carrier component can be
joined in the carrier by a walk avoiding the small cut edge support.

This is a sharper planar foundation target than the side statement itself.  A
future annulus/Jordan proof can discharge it by proving that an outside
component attaches along a single carrier interval after the cut edges are
deleted.
-/
def BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentsCarrierConnected
    {G : SimpleGraph V} (edges : Finset G.edgeSet)
    (cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)) :
    Prop :=
  ∀ root : V,
    ∀ a b : BoundaryEdgeSetEndpointVertex (G := G) edges,
      BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
        (G := G) edges root a →
      BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
        (G := G) edges root b →
        ∃ p : (BoundaryEdgeSetInducedGraph (G := G) edges).Walk a b,
          ∀ e : (BoundaryEdgeSetInducedGraph (G := G) edges).edgeSet,
            e ∈ cut.edgeCut → (e : Sym2 _) ∉ p.edges

/--
Planar-facing shared-endpoint boundary-route target for one off-carrier
component: any two carrier attachments of the same off-carrier component lie
on selected ambient boundary edges joined by a shared-endpoint boundary walk
whose visited selected edges avoid the mapped carrier cut.
-/
def BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachable
    {G : SimpleGraph V} (edges : Finset G.edgeSet)
    (cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)) :
    Prop :=
  ∀ root : V,
    ∀ a b : BoundaryEdgeSetEndpointVertex (G := G) edges,
      BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
        (G := G) edges root a →
      BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
        (G := G) edges root b →
        ∃ ea eb : BoundaryEdgeSetEdgeVertex (G := G) edges,
          (a : V) ∈ (ea.1 : Sym2 V) ∧
            (b : V) ∈ (eb.1 : Sym2 V) ∧
              BoundaryEdgeSetSharedEndpointMappedCutAvoidingReachable
                (G := G) (edges := edges) cut ea eb

/--
Selected boundary edges that survive deletion of the mapped carrier cut.
-/
abbrev BoundaryEdgeSetMappedCutAvoidingEdgeVertex
    {G : SimpleGraph V} (edges : Finset G.edgeSet)
    (cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)) :
    Type _ :=
  {e : BoundaryEdgeSetEdgeVertex (G := G) edges //
    e.1 ∉ cut.edgeCut.map
      (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet}

/--
The selected-boundary shared-endpoint graph after deleting selected edges that
are in the mapped carrier cut.
-/
def BoundaryEdgeSetMappedCutAvoidingSharedEndpointGraph
    {G : SimpleGraph V} (edges : Finset G.edgeSet)
    (cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)) :
    SimpleGraph
      (BoundaryEdgeSetMappedCutAvoidingEdgeVertex (G := G) edges cut) where
  Adj e f := (BoundaryEdgeSetSharedEndpointGraph (G := G) edges).Adj e.1 f.1
  symm := ⟨by
    intro e f h
    rcases h with ⟨hne, v, hvE, hvF⟩
    exact ⟨hne.symm, v, hvF, hvE⟩
  ⟩
  loopless := ⟨fun e h => h.1 rfl⟩

/--
Reachability in the selected-edge shared-endpoint graph after deleting the
mapped carrier cut supplies the existing cut-avoiding shared-endpoint
reachability predicate.
-/
theorem
    boundaryEdgeSetSharedEndpointMappedCutAvoidingReachable_of_mappedCutAvoidingSharedEndpointGraph_reachable
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    {e f : BoundaryEdgeSetMappedCutAvoidingEdgeVertex (G := G) edges cut}
    (hreachable :
      (BoundaryEdgeSetMappedCutAvoidingSharedEndpointGraph
        (G := G) edges cut).Reachable e f) :
    BoundaryEdgeSetSharedEndpointMappedCutAvoidingReachable
      (G := G) (edges := edges) cut e.1 f.1 := by
  rcases hreachable with ⟨p⟩
  induction p with
  | @nil g =>
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      intro x hx
      have hx_eq : x = g.1 := by
        simpa using hx
      simpa [hx_eq] using g.2
  | @cons e₀ e₁ e₂ hadj p ih =>
      rcases ih with ⟨tail, htail⟩
      have hfullAdj :
          (BoundaryEdgeSetSharedEndpointGraph (G := G) edges).Adj
            e₀.1 e₁.1 := by
        exact hadj
      refine ⟨SimpleGraph.Walk.cons hfullAdj tail, ?_⟩
      intro x hx
      rcases (by
          simpa [SimpleGraph.Walk.support_cons] using hx :
          x = e₀.1 ∨ x ∈ tail.support) with hxHead | hxTail
      · simpa [hxHead] using e₀.2
      · exact htail x hxTail

/--
An explicit shared-endpoint walk whose visited selected boundary edges avoid
the mapped carrier cut is equivalently a walk in the cut-deleted
shared-endpoint graph, up to the endpoint subtype witnesses.
-/
theorem
    exists_mappedCutAvoidingSharedEndpointGraph_reachable_of_sharedEndpointGraph_walk
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    {e f : BoundaryEdgeSetEdgeVertex (G := G) edges}
    (p : (BoundaryEdgeSetSharedEndpointGraph (G := G) edges).Walk e f)
    (hAvoid :
      ∀ g : BoundaryEdgeSetEdgeVertex (G := G) edges,
        g ∈ p.support →
          g.1 ∉ cut.edgeCut.map
            (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet) :
    ∃ ea eb : BoundaryEdgeSetMappedCutAvoidingEdgeVertex (G := G) edges cut,
      ea.1 = e ∧
        eb.1 = f ∧
          (BoundaryEdgeSetMappedCutAvoidingSharedEndpointGraph
            (G := G) edges cut).Reachable ea eb := by
  induction p with
  | @nil g =>
      let g' : BoundaryEdgeSetMappedCutAvoidingEdgeVertex (G := G) edges cut :=
        ⟨g, hAvoid g (by simp)⟩
      exact ⟨g', g', rfl, rfl, SimpleGraph.Reachable.refl g'⟩
  | @cons e₀ e₁ e₂ hadj p ih =>
      have he₀Avoid :
          e₀.1 ∉ cut.edgeCut.map
            (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet :=
        hAvoid e₀ (by simp [SimpleGraph.Walk.support_cons])
      have htailAvoid :
          ∀ g : BoundaryEdgeSetEdgeVertex (G := G) edges,
            g ∈ p.support →
              g.1 ∉ cut.edgeCut.map
                (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet := by
        intro g hg
        exact hAvoid g (by simp [SimpleGraph.Walk.support_cons, hg])
      rcases ih htailAvoid with ⟨e₁', e₂', he₁', he₂', htailReach⟩
      let e₀' : BoundaryEdgeSetMappedCutAvoidingEdgeVertex (G := G) edges cut :=
        ⟨e₀, he₀Avoid⟩
      have hAdj :
          (BoundaryEdgeSetMappedCutAvoidingSharedEndpointGraph
            (G := G) edges cut).Adj e₀' e₁' := by
        change (BoundaryEdgeSetSharedEndpointGraph (G := G) edges).Adj e₀ e₁'.1
        rw [he₁']
        exact hadj
      rcases htailReach with ⟨q⟩
      exact
        ⟨e₀', e₂', rfl, he₂',
          ⟨SimpleGraph.Walk.cons hAdj q⟩⟩

/--
The explicit cut-avoiding shared-endpoint reachability predicate supplies
reachability in the cut-deleted shared-endpoint graph.
-/
theorem
    exists_mappedCutAvoidingSharedEndpointGraph_reachable_of_sharedEndpointMappedCutAvoidingReachable
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    {e f : BoundaryEdgeSetEdgeVertex (G := G) edges}
    (hreachable :
      BoundaryEdgeSetSharedEndpointMappedCutAvoidingReachable
        (G := G) (edges := edges) cut e f) :
    ∃ ea eb : BoundaryEdgeSetMappedCutAvoidingEdgeVertex (G := G) edges cut,
      ea.1 = e ∧
        eb.1 = f ∧
          (BoundaryEdgeSetMappedCutAvoidingSharedEndpointGraph
            (G := G) edges cut).Reachable ea eb := by
  rcases hreachable with ⟨p, hAvoid⟩
  exact
    exists_mappedCutAvoidingSharedEndpointGraph_reachable_of_sharedEndpointGraph_walk
      (G := G) (edges := edges) (cut := cut) p hAvoid

/--
Planar-facing component target stated through the graph obtained by deleting
the mapped carrier cut from the selected-boundary shared-endpoint graph.
-/
def BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentMappedCutAvoidingSharedEndpointConnected
    {G : SimpleGraph V} (edges : Finset G.edgeSet)
    (cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)) :
    Prop :=
  ∀ root : V,
    ∀ a b : BoundaryEdgeSetEndpointVertex (G := G) edges,
      BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
        (G := G) edges root a →
      BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
        (G := G) edges root b →
        ∃ ea eb :
          BoundaryEdgeSetMappedCutAvoidingEdgeVertex (G := G) edges cut,
          (a : V) ∈ (ea.1.1 : Sym2 V) ∧
            (b : V) ∈ (eb.1.1 : Sym2 V) ∧
              (BoundaryEdgeSetMappedCutAvoidingSharedEndpointGraph
                (G := G) edges cut).Reachable ea eb

/--
The cut-deleted shared-endpoint component target supplies the existing
cut-avoiding shared-endpoint route target.
-/
theorem
    boundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachable_of_mappedCutAvoidingSharedEndpointConnected
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    (hconnected :
      BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentMappedCutAvoidingSharedEndpointConnected
        (G := G) edges cut) :
    BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachable
      (G := G) edges cut := by
  intro root a b hrootA hrootB
  rcases hconnected root a b hrootA hrootB with
    ⟨ea, eb, ha, hb, hreachable⟩
  exact
    ⟨ea.1, eb.1, ha, hb,
      boundaryEdgeSetSharedEndpointMappedCutAvoidingReachable_of_mappedCutAvoidingSharedEndpointGraph_reachable
        (G := G) (edges := edges) (cut := cut) hreachable⟩

/--
Cut-avoiding shared-endpoint routes for component attachments supply the
cut-deleted shared-endpoint connectivity form of the same target.
-/
theorem
    boundaryEdgeSetInducedCutOffCarrierComponentAttachmentMappedCutAvoidingSharedEndpointConnected_of_cutAvoidingSharedEndpointReachable
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    (hreachable :
      BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachable
        (G := G) edges cut) :
    BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentMappedCutAvoidingSharedEndpointConnected
      (G := G) edges cut := by
  intro root a b hrootA hrootB
  rcases hreachable root a b hrootA hrootB with
    ⟨ea, eb, ha, hb, hroute⟩
  rcases
    exists_mappedCutAvoidingSharedEndpointGraph_reachable_of_sharedEndpointMappedCutAvoidingReachable
      (G := G) (edges := edges) (cut := cut) hroute with
    ⟨ea', eb', hea', heb', hreach⟩
  refine ⟨ea', eb', ?_, ?_, hreach⟩
  · rw [hea']
    exact ha
  · rw [heb']
    exact hb

/--
The component attachment target is equivalently expressed by an explicit
cut-avoiding shared-endpoint walk or by reachability in the cut-deleted
shared-endpoint graph.
-/
theorem
    boundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachable_iff_mappedCutAvoidingSharedEndpointConnected
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)} :
    BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachable
        (G := G) edges cut ↔
      BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentMappedCutAvoidingSharedEndpointConnected
        (G := G) edges cut :=
  ⟨boundaryEdgeSetInducedCutOffCarrierComponentAttachmentMappedCutAvoidingSharedEndpointConnected_of_cutAvoidingSharedEndpointReachable,
    boundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachable_of_mappedCutAvoidingSharedEndpointConnected⟩

/--
Cut-avoiding shared-endpoint boundary routes for component attachments supply
the carrier-walk attachment-connectivity target.
-/
theorem
    boundaryEdgeSetInducedCutOffCarrierComponentAttachmentsCarrierConnected_of_cutAvoidingSharedEndpointReachable
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    (hreachable :
      BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachable
        (G := G) edges cut) :
    BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentsCarrierConnected
      (G := G) edges cut := by
  intro root a b hrootA hrootB
  rcases hreachable root a b hrootA hrootB with
    ⟨ea, eb, ha, hb, hroute⟩
  exact
    exists_boundaryEdgeSetInducedGraph_walk_avoids_cut_of_sharedEndpointGraph_cutAvoidingReachable
      (G := G) (edges := edges) hroute ha hb

namespace BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnected

/-- Off-carrier walk consistency rules out off-carrier reachability between
opposite carrier sides. -/
theorem of_walkConsistent
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    (hconsistent :
      BoundaryEdgeSetInducedCutOffCarrierWalkConsistent (G := G) edges cut) :
    BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnected
      (G := G) edges cut := by
  rintro ⟨a, b, ha, hb, hab⟩
  exact hb ((hconsistent a b hab).1 ha)

/-- If no off-carrier component joins opposite carrier sides, then off-carrier
walks preserve the carrier-side predicate. -/
theorem to_walkConsistent
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    (hdisconnected :
      BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnected
        (G := G) edges cut) :
    BoundaryEdgeSetInducedCutOffCarrierWalkConsistent (G := G) edges cut := by
  intro a b hab
  constructor
  · intro ha
    by_contra hb
    exact hdisconnected ⟨a, b, ha, hb, hab⟩
  · intro hb
    by_contra ha
    exact hdisconnected ⟨b, a, hb, ha, hab.symm⟩

end BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnected

namespace BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachments

/-- Carrier-side connectivity of a component's attachments implies the
one-sided attachment target, because a carrier walk avoiding the cut preserves
the bundled cut side. -/
theorem of_attachmentCarrierConnected
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    (hconnected :
      BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentsCarrierConnected
        (G := G) edges cut) :
    BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachments
      (G := G) edges cut := by
  intro root hboth
  rcases hboth with ⟨⟨a, ha, hrootA⟩, ⟨b, hb, hrootB⟩⟩
  rcases hconnected root a b hrootA hrootB with ⟨p, hp⟩
  exact hb ((cut.side_iff_of_forall_not_mem_edgeCut_of_walk p hp).1 ha)

/-- No opposite-side off-carrier connection implies the component-attachment
form: a single off-carrier component cannot attach to both cut sides. -/
theorem of_oppositeSideDisconnected
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    (hdisconnected :
      BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnected
        (G := G) edges cut) :
    BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachments
      (G := G) edges cut := by
  intro root hboth
  rcases hboth with ⟨⟨a, ha, hrootA⟩, ⟨b, hb, hrootB⟩⟩
  exact hdisconnected ⟨a, b, ha, hb, hrootA.symm.trans hrootB⟩

/-- The component-attachment form implies no opposite-side off-carrier
connection by taking one endpoint as the component representative. -/
theorem to_oppositeSideDisconnected
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    (honeSided :
      BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachments
        (G := G) edges cut) :
    BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnected
      (G := G) edges cut := by
  rintro ⟨a, b, ha, hb, hab⟩
  exact honeSided a
    ⟨⟨a, ha,
        OffCarrierReachable.refl (G := G)
          (support := boundaryEdgeSetEndpointSupport edges) a⟩,
      ⟨b, hb, hab⟩⟩

end BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachments

/-- For one carrier cut, no opposite-side off-carrier connection is equivalent
to the component-attachment form. -/
theorem
    boundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnected_iff_componentOneSidedAttachments
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)} :
    BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnected
        (G := G) edges cut ↔
      BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachments
        (G := G) edges cut :=
  ⟨BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachments.of_oppositeSideDisconnected,
    BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachments.to_oppositeSideDisconnected⟩

/-- For one carrier cut, off-carrier walk consistency is equivalent to saying
that off-carrier reachability never connects opposite carrier sides. -/
theorem
    boundaryEdgeSetInducedCutOffCarrierWalkConsistent_iff_oppositeSideDisconnected
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)} :
    BoundaryEdgeSetInducedCutOffCarrierWalkConsistent (G := G) edges cut ↔
      BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnected
        (G := G) edges cut :=
  ⟨BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnected.of_walkConsistent,
    BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnected.to_walkConsistent⟩

namespace BoundaryEdgeSetInducedCutOffCarrierWalkConsistent

/--
The reachability-filled side agrees with the original cut side on carrier
vertices when off-carrier walks preserve the carrier side.
-/
theorem offCarrierReachSide_comp_embedding
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    (hconsistent :
      BoundaryEdgeSetInducedCutOffCarrierWalkConsistent (G := G) edges cut)
    (w : BoundaryEdgeSetEndpointVertex (G := G) edges) :
    boundaryEdgeSetInducedCutOffCarrierReachSide (G := G) (edges := edges) cut
        (boundaryEdgeSetInducedGraphEmbedding (G := G) edges w) ↔
      cut.side w := by
  constructor
  · rintro ⟨a, ha, hreach⟩
    exact (hconsistent a w hreach).1 ha
  · intro hw
    exact ⟨w, hw, OffCarrierReachable.refl (G := G)
      (support := boundaryEdgeSetEndpointSupport edges) w⟩

/--
The reachability-filled side is locally constant across every edge touching
the outside of the carrier support.
-/
theorem offCarrierReachSide_locallyConstant
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)) :
    EdgeSideLocallyConstantOffSupport
      (G := G)
      (boundaryEdgeSetInducedCutOffCarrierReachSide (G := G) (edges := edges) cut)
      (boundaryEdgeSetEndpointSupport edges) := by
  intro e hoffSupport u v hu hv
  constructor
  · rintro ⟨a, ha, hau⟩
    exact
      ⟨a, ha,
        hau.trans
          (OffCarrierReachable.of_edge_endpoint_outside
            (G := G) (support := boundaryEdgeSetEndpointSupport edges)
            (e := e) hu hv hoffSupport)⟩
  · rintro ⟨a, ha, hav⟩
    exact
      ⟨a, ha,
        hav.trans
          (OffCarrierReachable.of_edge_endpoint_outside
            (G := G) (support := boundaryEdgeSetEndpointSupport edges)
            (e := e) hv hu hoffSupport)⟩

/--
Off-carrier walk consistency supplies carrier-endpoint support data for one
small cyclic cut of the canonical induced boundary graph.
-/
def toCarrierEndpointSupport
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    (hconsistent :
      BoundaryEdgeSetInducedCutOffCarrierWalkConsistent (G := G) edges cut) :
    BoundaryEdgeSetInducedCutAmbientSideEndpointSupport (G := G) edges cut where
  side := boundaryEdgeSetInducedCutOffCarrierReachSide (G := G) (edges := edges) cut
  side_comp_embedding := hconsistent.offCarrierReachSide_comp_embedding
  crossingEdge_endpointSupport := by
    intro e hcross v hv
    by_contra hvOutside
    have hnotCross :
        ¬ EdgeCrossesVertexSide G
          (boundaryEdgeSetInducedCutOffCarrierReachSide
            (G := G) (edges := edges) cut) e :=
      not_edgeCrossesVertexSide_of_edgeSideLocallyConstantOffSupport
        (offCarrierReachSide_locallyConstant (G := G) (edges := edges) cut)
        ⟨v, hv, hvOutside⟩
    exact hnotCross hcross

/--
For the canonical endpoint-support induced graph, mapped cut edges are still
selected carrier edges when the selected edge set is induced.
-/
theorem mappedCutEdgeSet_subset_carrierEdges_of_inducedSubgraph
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hInduced : BoundaryEdgeSetInducedSubgraph edges)
    (cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)) :
    cut.edgeCut.map
        (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet ⊆
      edges := by
  intro e he
  rcases Finset.mem_map.1 he with ⟨eH, _heH, heq⟩
  rw [← heq]
  exact boundaryEdgeSetInducedGraphEmbedding_mapEdgeSet_mem_of_inducedSubgraph
    (G := G) (edges := edges) hInduced eH

/--
Canonical local-constancy data imply off-carrier walk consistency.  The only
extra graph condition needed is that the finite carrier edge set is induced,
so the mapped support of a carrier cut is contained in the full carrier
support.
-/
theorem of_localConstancy
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    (hInduced : BoundaryEdgeSetInducedSubgraph edges)
    (localData :
      PeeledCollarCutAmbientSideLocalConstancy
        (boundaryEdgeSetInducedGraphEmbedding (G := G) edges) cut) :
    BoundaryEdgeSetInducedCutOffCarrierWalkConsistent (G := G) edges cut := by
  intro a b hab
  rcases hab with ⟨p, hp⟩
  have hcutSupport_subset :
      boundaryEdgeSetEndpointSupport
          (cut.edgeCut.map
            (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet) ⊆
        boundaryEdgeSetEndpointSupport edges :=
    boundaryEdgeSetEndpointSupport_mono
      (mappedCutEdgeSet_subset_carrierEdges_of_inducedSubgraph
        (G := G) (edges := edges) hInduced cut)
  have hpCut :
      WalkUsesOnlyEdgesTouchingOutsideVertexSupport
        (boundaryEdgeSetEndpointSupport
          (cut.edgeCut.map
            (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet))
        p := by
    intro e he
    rcases hp e he with ⟨v, hv, hvOutside⟩
    exact ⟨v, hv, fun hvCut => hvOutside (hcutSupport_subset hvCut)⟩
  have hside :
      localData.side
          (boundaryEdgeSetInducedGraphEmbedding (G := G) edges a) ↔
        localData.side
          (boundaryEdgeSetInducedGraphEmbedding (G := G) edges b) :=
    localData.offBoundaryEndpoint_side_iff.walk_side_iff p hpCut
  exact (localData.side_comp_embedding a).symm.trans
    (hside.trans (localData.side_comp_embedding b))

/--
A mapped cut edge of the endpoint-support induced carrier cannot touch the
outside of the full carrier endpoint support.
-/
theorem not_edgeTouchesOutsideVertexSupport_of_mem_boundaryEdgeSetInduced_mappedCut
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    {e : G.edgeSet}
    (he :
      e ∈ cut.edgeCut.map
        (boundaryEdgeSetInducedGraphEmbedding (G := G) edges).mapEdgeSet) :
    ¬ EdgeTouchesOutsideVertexSupport
      (boundaryEdgeSetEndpointSupport edges) (e : Sym2 V) := by
  intro htouch
  rcases htouch with ⟨v, hv, hvOutside⟩
  rcases Finset.mem_map.1 he with ⟨eH, _heH, heq⟩
  rw [← heq] at hv
  have hpreimage :
      ∃ w : BoundaryEdgeSetEndpointVertex (G := G) edges,
        w ∈ (eH : Sym2 (BoundaryEdgeSetEndpointVertex (G := G) edges)) ∧
          boundaryEdgeSetInducedGraphEmbedding (G := G) edges w = v := by
    simpa [SimpleGraph.Embedding.mapEdgeSet, SimpleGraph.Hom.mapEdgeSet,
      Sym2.mem_map] using hv
  rcases hpreimage with ⟨w, _hw, hw⟩
  exact hvOutside (by
    rw [← hw]
    exact boundaryEdgeSetEndpointVertex_mem w)

/--
No-avoiding-walk side separation implies off-carrier walk consistency for the
canonical endpoint-support carrier.  No inducedness hypothesis is needed:
off-carrier edges touch the outside of the full endpoint support, whereas
mapped carrier-cut edges have both endpoints inside that support.
-/
theorem of_ambientSideSeparation
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    (separation :
      PeeledCollarCutAmbientSideSeparation
        (boundaryEdgeSetInducedGraphEmbedding (G := G) edges) cut) :
    BoundaryEdgeSetInducedCutOffCarrierWalkConsistent (G := G) edges cut := by
  intro a b hab
  have hforward :
      ∀ x y : BoundaryEdgeSetEndpointVertex (G := G) edges,
        OffCarrierReachable G (boundaryEdgeSetEndpointSupport edges) x y →
          cut.side x → cut.side y := by
    intro x y hxy hx
    rcases hxy with ⟨p, hp⟩
    by_contra hy
    have hsx : separation.side (x : V) := by
      simpa [boundaryEdgeSetInducedGraphEmbedding] using
        (separation.side_comp_embedding x).2 hx
    have hsy : ¬ separation.side (y : V) := by
      intro hsideY
      exact hy ((separation.side_comp_embedding y).1 (by
        simpa [boundaryEdgeSetInducedGraphEmbedding] using hsideY))
    exact separation.noWalkAvoiding_mappedCut
      ⟨x, y, p, hsx, hsy, by
        intro e heCut heEdges
        exact
          not_edgeTouchesOutsideVertexSupport_of_mem_boundaryEdgeSetInduced_mappedCut
            (G := G) (edges := edges) (cut := cut) heCut
            (hp (e : Sym2 V) heEdges)⟩
  constructor
  · exact hforward a b hab
  · exact hforward b a hab.symm

end BoundaryEdgeSetInducedCutOffCarrierWalkConsistent

/--
Off-carrier walk consistency target for the canonical induced boundary graph.
This is the graph-theoretic shape expected from the annulus separation
theorem: outside-carrier regions cannot connect opposite sides of the carrier
cut.
-/
def BoundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient
    {G : SimpleGraph V} (edges : Finset G.edgeSet) : Prop :=
  ∀ cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges),
    BoundaryEdgeSetInducedCutOffCarrierWalkConsistent (G := G) edges cut

/--
No off-carrier component joins opposite sides for any small cyclic cut in the
canonical induced boundary graph.  This is the exact graph-facing target that a
planar annulus separation proof can discharge directly.
-/
def BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient
    {G : SimpleGraph V} (edges : Finset G.edgeSet) : Prop :=
  ∀ cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges),
    BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnected (G := G)
      edges cut

/--
For every small cyclic carrier cut, each off-carrier component has one-sided
attachments to that cut.  This is the component-facing planar target: the
remaining annulus/Jordan theorem should prove this by showing outside
components cannot meet both sides of a carrier separator.
-/
def BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachmentsToAmbient
    {G : SimpleGraph V} (edges : Finset G.edgeSet) : Prop :=
  ∀ cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges),
    BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachments
      (G := G) edges cut

/--
For every small cyclic carrier cut, each off-carrier component's attachments
are connected in the carrier after deleting the cut edge support.  This is the
carrier-walk foundation target that feeds the component-attachment target.
-/
def BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCarrierConnectivitiesToAmbient
    {G : SimpleGraph V} (edges : Finset G.edgeSet) : Prop :=
  ∀ cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges),
    BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentsCarrierConnected
      (G := G) edges cut

/--
For every small cyclic carrier cut, each off-carrier component's attachments
are connected by a cut-avoiding shared-endpoint boundary route.
-/
def BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachabilitiesToAmbient
    {G : SimpleGraph V} (edges : Finset G.edgeSet) : Prop :=
  ∀ cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges),
    BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachable
      (G := G) edges cut

/--
For every small cyclic carrier cut, attachments of each off-carrier component
are connected in the selected-boundary shared-endpoint graph after deleting
the mapped carrier cut.
-/
def BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentMappedCutAvoidingSharedEndpointConnectivitiesToAmbient
    {G : SimpleGraph V} (edges : Finset G.edgeSet) : Prop :=
  ∀ cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges),
    BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentMappedCutAvoidingSharedEndpointConnected
      (G := G) edges cut

/--
The cut-deleted shared-endpoint component target supplies cut-avoiding
shared-endpoint routes for every small cyclic carrier cut.
-/
theorem
    boundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachabilitiesToAmbient_of_mappedCutAvoidingSharedEndpointConnectivities
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hconnected :
      BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentMappedCutAvoidingSharedEndpointConnectivitiesToAmbient
        (G := G) edges) :
    BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachabilitiesToAmbient
      (G := G) edges := by
  intro cut
  exact
    boundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachable_of_mappedCutAvoidingSharedEndpointConnected
      (G := G) (edges := edges) (cut := cut) (hconnected cut)

/--
Cut-avoiding shared-endpoint routes for every small cyclic carrier cut supply
the cut-deleted shared-endpoint connectivity target for every such cut.
-/
theorem
    boundaryEdgeSetInducedCutOffCarrierComponentAttachmentMappedCutAvoidingSharedEndpointConnectivitiesToAmbient_of_cutAvoidingSharedEndpointReachabilities
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hreachable :
      BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachabilitiesToAmbient
        (G := G) edges) :
    BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentMappedCutAvoidingSharedEndpointConnectivitiesToAmbient
      (G := G) edges := by
  intro cut
  exact
    boundaryEdgeSetInducedCutOffCarrierComponentAttachmentMappedCutAvoidingSharedEndpointConnected_of_cutAvoidingSharedEndpointReachable
      (G := G) (edges := edges) (cut := cut) (hreachable cut)

/--
For all small cyclic carrier cuts, the explicit cut-avoiding route target and
the cut-deleted shared-endpoint connectivity target are equivalent.
-/
theorem
    boundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachabilitiesToAmbient_iff_mappedCutAvoidingSharedEndpointConnectivities
    {G : SimpleGraph V} {edges : Finset G.edgeSet} :
    BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachabilitiesToAmbient
        (G := G) edges ↔
      BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentMappedCutAvoidingSharedEndpointConnectivitiesToAmbient
        (G := G) edges :=
  ⟨boundaryEdgeSetInducedCutOffCarrierComponentAttachmentMappedCutAvoidingSharedEndpointConnectivitiesToAmbient_of_cutAvoidingSharedEndpointReachabilities,
    boundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachabilitiesToAmbient_of_mappedCutAvoidingSharedEndpointConnectivities⟩

/--
Cut-avoiding shared-endpoint boundary routes supply the carrier-connectivity
target for every small cyclic carrier cut.
-/
theorem
    boundaryEdgeSetInducedCutOffCarrierComponentAttachmentCarrierConnectivitiesToAmbient_of_cutAvoidingSharedEndpointReachabilities
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hreachable :
      BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachabilitiesToAmbient
        (G := G) edges) :
    BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCarrierConnectivitiesToAmbient
      (G := G) edges := by
  intro cut
  exact
    boundaryEdgeSetInducedCutOffCarrierComponentAttachmentsCarrierConnected_of_cutAvoidingSharedEndpointReachable
      (G := G) (edges := edges) (cut := cut) (hreachable cut)

/-- Off-carrier walk consistency implies the no-opposite-side off-carrier
component target. -/
theorem
    boundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient_of_offCarrierWalkConsistencies
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hconsistent :
      BoundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient
        (G := G) edges) :
    BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient
      (G := G) edges := by
  intro cut
  exact
    BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnected.of_walkConsistent
      (hconsistent cut)

/-- No-opposite-side off-carrier components imply off-carrier walk
consistency. -/
theorem
    boundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient_of_oppositeSideDisconnections
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hdisconnected :
      BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient
        (G := G) edges) :
    BoundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient
      (G := G) edges := by
  intro cut
  exact
    BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnected.to_walkConsistent
      (hdisconnected cut)

/-- No-opposite-side off-carrier components imply the one-sided attachment
target. -/
theorem
    boundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachmentsToAmbient_of_oppositeSideDisconnections
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hdisconnected :
      BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient
        (G := G) edges) :
    BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachmentsToAmbient
      (G := G) edges := by
  intro cut
  exact
    BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachments.of_oppositeSideDisconnected
      (hdisconnected cut)

/-- Carrier-side connectivity of component attachments implies one-sided
component attachments. -/
theorem
    boundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachmentsToAmbient_of_attachmentCarrierConnectivities
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hconnected :
      BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCarrierConnectivitiesToAmbient
        (G := G) edges) :
    BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachmentsToAmbient
      (G := G) edges := by
  intro cut
  exact
    BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachments.of_attachmentCarrierConnected
      (hconnected cut)

/-- Carrier-side connectivity of component attachments implies no
opposite-side off-carrier components. -/
theorem
    boundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient_of_attachmentCarrierConnectivities
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hconnected :
      BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCarrierConnectivitiesToAmbient
        (G := G) edges) :
    BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient
      (G := G) edges := by
  intro cut
  exact
    BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachments.to_oppositeSideDisconnected
      (BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachments.of_attachmentCarrierConnected
        (hconnected cut))

/-- Carrier-side connectivity of component attachments implies off-carrier
walk consistency. -/
theorem
    boundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient_of_attachmentCarrierConnectivities
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hconnected :
      BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCarrierConnectivitiesToAmbient
        (G := G) edges) :
    BoundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient
      (G := G) edges :=
  boundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient_of_oppositeSideDisconnections
    (boundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient_of_attachmentCarrierConnectivities
      hconnected)

/-- One-sided off-carrier component attachments imply no opposite-side
off-carrier components. -/
theorem
    boundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient_of_componentOneSidedAttachments
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (honeSided :
      BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachmentsToAmbient
        (G := G) edges) :
    BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient
      (G := G) edges := by
  intro cut
  exact
    BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachments.to_oppositeSideDisconnected
      (honeSided cut)

/-- The off-carrier target can equivalently be stated as side preservation
along off-carrier walks or as disconnection of opposite carrier sides. -/
theorem
    boundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient_iff_oppositeSideDisconnections
    {G : SimpleGraph V} {edges : Finset G.edgeSet} :
    BoundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient
        (G := G) edges ↔
      BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient
        (G := G) edges :=
  ⟨boundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient_of_offCarrierWalkConsistencies,
    boundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient_of_oppositeSideDisconnections⟩

/-- The off-carrier target can equivalently be stated as no opposite-side
off-carrier connection or as one-sided component attachments. -/
theorem
    boundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient_iff_componentOneSidedAttachments
    {G : SimpleGraph V} {edges : Finset G.edgeSet} :
    BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient
        (G := G) edges ↔
      BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachmentsToAmbient
        (G := G) edges :=
  ⟨boundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachmentsToAmbient_of_oppositeSideDisconnections,
    boundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient_of_componentOneSidedAttachments⟩

/-- Off-carrier walk consistency is equivalent to the component-attachment
form of the planar target. -/
theorem
    boundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient_iff_componentOneSidedAttachments
    {G : SimpleGraph V} {edges : Finset G.edgeSet} :
    BoundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient
        (G := G) edges ↔
      BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachmentsToAmbient
        (G := G) edges := by
  rw [boundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient_iff_oppositeSideDisconnections,
    boundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient_iff_componentOneSidedAttachments]

/--
Off-carrier walk consistency implies the carrier-endpoint support target for
the canonical induced boundary graph.
-/
theorem boundaryCarrierEndpointSupports_of_offCarrierWalkConsistencies
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hconsistent :
      BoundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient (G := G) edges) :
    BoundaryEdgeSetInducedCutAmbientSideEndpointSupportsToAmbient
      (G := G) edges := by
  intro cut
  exact ⟨(hconsistent cut).toCarrierEndpointSupport⟩

/--
Off-carrier walk consistency implies no-avoiding-walk side separations for the
canonical induced boundary graph.
-/
theorem peeledCollarCutAmbientSideSeparationsToAmbient_of_offCarrierWalkConsistencies
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hconsistent :
      BoundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient (G := G) edges) :
    PeeledCollarCutAmbientSideSeparationsToAmbient
      (boundaryEdgeSetInducedGraphEmbedding (G := G) edges) :=
  peeledCollarCutAmbientSideSeparationsToAmbient_of_boundaryCarrierEndpointSupports
    (boundaryCarrierEndpointSupports_of_offCarrierWalkConsistencies hconsistent)

/--
Canonical local-constancy data imply the off-carrier walk-consistency target
when the selected finite carrier edge set is induced.
-/
theorem boundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient_of_localConstancies
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hInduced : BoundaryEdgeSetInducedSubgraph edges)
    (hlocal :
      PeeledCollarCutAmbientSideLocalConstanciesToAmbient
        (boundaryEdgeSetInducedGraphEmbedding (G := G) edges)) :
    BoundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient
      (G := G) edges := by
  intro cut
  rcases hlocal cut with ⟨localData⟩
  exact BoundaryEdgeSetInducedCutOffCarrierWalkConsistent.of_localConstancy
    (G := G) (edges := edges) hInduced localData

/--
No-avoiding-walk side separation implies off-carrier walk consistency for the
canonical endpoint-support carrier.
-/
theorem boundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient_of_ambientSideSeparations
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hseparate :
      PeeledCollarCutAmbientSideSeparationsToAmbient
        (boundaryEdgeSetInducedGraphEmbedding (G := G) edges)) :
    BoundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient
      (G := G) edges := by
  intro cut
  rcases hseparate cut with ⟨separation⟩
  exact BoundaryEdgeSetInducedCutOffCarrierWalkConsistent.of_ambientSideSeparation
    (G := G) (edges := edges) separation

/--
Off-carrier walk consistency and no-avoiding-walk side separation are
equivalent foundation targets for the canonical endpoint-support carrier.
-/
theorem boundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient_iff_ambientSideSeparations
    {G : SimpleGraph V} {edges : Finset G.edgeSet} :
    BoundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient
        (G := G) edges ↔
      PeeledCollarCutAmbientSideSeparationsToAmbient
        (boundaryEdgeSetInducedGraphEmbedding (G := G) edges) :=
  ⟨peeledCollarCutAmbientSideSeparationsToAmbient_of_offCarrierWalkConsistencies,
    boundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient_of_ambientSideSeparations⟩

/--
Off-carrier walk consistency implies endpoint-range data for the canonical
induced boundary graph.
-/
theorem peeledCollarCutAmbientSideEndpointRangesToAmbient_of_offCarrierWalkConsistencies
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hconsistent :
      BoundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient (G := G) edges) :
    PeeledCollarCutAmbientSideEndpointRangesToAmbient
      (boundaryEdgeSetInducedGraphEmbedding (G := G) edges) :=
  peeledCollarCutAmbientSideEndpointRangesToAmbient_of_boundaryCarrierEndpointSupports
    (boundaryCarrierEndpointSupports_of_offCarrierWalkConsistencies hconsistent)

/--
Off-carrier walk consistency implies the graph-facing small-cut lift for the
canonical induced boundary graph.
-/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_offCarrierWalkConsistencies
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hconsistent :
      BoundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient (G := G) edges) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  peeledCollarSmallCyclicCutLiftsToAmbient_of_boundaryCarrierEndpointSupports
    (boundaryCarrierEndpointSupports_of_offCarrierWalkConsistencies hconsistent)

/--
Regime-facing inheritance theorem from off-carrier walk consistency for the
canonical induced boundary graph.
-/
theorem
    peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_offCarrierWalkConsistencies
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) edges)
        (BoundaryEdgeSetInducedGraph (G := G) edges))
    (hconsistent :
      BoundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient (G := G) edges) :
    CyclicallyFiveEdgeConnected (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_boundaryCarrierEndpointSupports
    regime
    (boundaryCarrierEndpointSupports_of_offCarrierWalkConsistencies hconsistent)

namespace PlanarBoundaryAnnulusBoundaryData

/--
A selected-boundary support walk whose visited edges avoid the mapped carrier
cut becomes reachability in the shared-endpoint graph after deleting that cut.
-/
theorem
    exists_mappedCutAvoidingSharedEndpointGraph_reachable_of_planarBoundarySupportEndpointAdjGraph_walk
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb)
    {cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)}
    {e f : PlanarBoundaryEdgeVertex emb}
    (p : (planarBoundarySupportEndpointAdjGraph emb).Walk e f)
    (hAvoid :
      ∀ g : PlanarBoundaryEdgeVertex emb,
        g ∈ p.support →
          (data.toBoundaryEdgeSetEdgeVertex g).1 ∉
            cut.edgeCut.map
              (boundaryEdgeSetInducedGraphEmbedding
                (G := G) data.ambientBoundaryEdgeSet).mapEdgeSet) :
    ∃ ea eb :
        BoundaryEdgeSetMappedCutAvoidingEdgeVertex
          (G := G) data.ambientBoundaryEdgeSet cut,
      ea.1 = data.toBoundaryEdgeSetEdgeVertex e ∧
        eb.1 = data.toBoundaryEdgeSetEdgeVertex f ∧
          (BoundaryEdgeSetMappedCutAvoidingSharedEndpointGraph
            (G := G) data.ambientBoundaryEdgeSet cut).Reachable ea eb := by
  induction p with
  | @nil g =>
      let g' :
          BoundaryEdgeSetMappedCutAvoidingEdgeVertex
            (G := G) data.ambientBoundaryEdgeSet cut :=
        ⟨data.toBoundaryEdgeSetEdgeVertex g, hAvoid g (by simp)⟩
      exact ⟨g', g', rfl, rfl, SimpleGraph.Reachable.refl g'⟩
  | @cons e₀ e₁ e₂ hadj p ih =>
      have he₀Avoid :
          (data.toBoundaryEdgeSetEdgeVertex e₀).1 ∉
            cut.edgeCut.map
              (boundaryEdgeSetInducedGraphEmbedding
                (G := G) data.ambientBoundaryEdgeSet).mapEdgeSet :=
        hAvoid e₀ (by simp [SimpleGraph.Walk.support_cons])
      have htailAvoid :
          ∀ g : PlanarBoundaryEdgeVertex emb,
            g ∈ p.support →
              (data.toBoundaryEdgeSetEdgeVertex g).1 ∉
                cut.edgeCut.map
                  (boundaryEdgeSetInducedGraphEmbedding
                    (G := G) data.ambientBoundaryEdgeSet).mapEdgeSet := by
        intro g hg
        exact hAvoid g (by simp [SimpleGraph.Walk.support_cons, hg])
      rcases ih htailAvoid with ⟨e₁', e₂', he₁', he₂', htailReach⟩
      let e₀' :
          BoundaryEdgeSetMappedCutAvoidingEdgeVertex
            (G := G) data.ambientBoundaryEdgeSet cut :=
        ⟨data.toBoundaryEdgeSetEdgeVertex e₀, he₀Avoid⟩
      have hAdj :
          (BoundaryEdgeSetMappedCutAvoidingSharedEndpointGraph
            (G := G) data.ambientBoundaryEdgeSet cut).Adj e₀' e₁' := by
        change
          (BoundaryEdgeSetSharedEndpointGraph
            (G := G) data.ambientBoundaryEdgeSet).Adj
            (data.toBoundaryEdgeSetEdgeVertex e₀) e₁'.1
        rw [he₁']
        exact
          data.boundaryEdgeSetSharedEndpointGraph_adj_of_planarBoundarySupportEndpointAdjGraph_adj
            hadj
      rcases htailReach with ⟨q⟩
      exact
        ⟨e₀', e₂', rfl, he₂',
          ⟨SimpleGraph.Walk.cons hAdj q⟩⟩

/--
Face-local selected-boundary walks give cut-deleted shared-endpoint
reachability when every selected boundary edge on that face avoids the mapped
carrier cut.
-/
theorem
    exists_mappedCutAvoidingSharedEndpointGraph_reachable_of_boundaryComponentWalkOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb)
    {cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)}
    {f : AmbientFace emb.faces}
    (hwalk : BoundaryComponentWalkOnFace (emb := emb) f)
    (hfaceAvoid :
      ∀ g : PlanarBoundaryEdgeVertex emb,
        g.1 ∈ emb.faceBoundary f.1 →
          (data.toBoundaryEdgeSetEdgeVertex g).1 ∉
            cut.edgeCut.map
              (boundaryEdgeSetInducedGraphEmbedding
                (G := G) data.ambientBoundaryEdgeSet).mapEdgeSet)
    {e₁ e₂ : G.edgeSet}
    (he₁Face : e₁ ∈ emb.faceBoundary f.1)
    (he₂Face : e₂ ∈ emb.faceBoundary f.1)
    (he₁ : e₁ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (he₂ : e₂ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    ∃ ea eb :
        BoundaryEdgeSetMappedCutAvoidingEdgeVertex
          (G := G) data.ambientBoundaryEdgeSet cut,
      ea.1 = data.toBoundaryEdgeSetEdgeVertex ⟨e₁, he₁⟩ ∧
        eb.1 = data.toBoundaryEdgeSetEdgeVertex ⟨e₂, he₂⟩ ∧
          (BoundaryEdgeSetMappedCutAvoidingSharedEndpointGraph
            (G := G) data.ambientBoundaryEdgeSet cut).Reachable ea eb := by
  rcases hwalk he₁Face he₂Face he₁ he₂ with ⟨p, hpFace⟩
  exact
    data.exists_mappedCutAvoidingSharedEndpointGraph_reachable_of_planarBoundarySupportEndpointAdjGraph_walk
      p
      (fun g hg => hfaceAvoid g (hpFace g hg))

/--
Annulus-boundary off-carrier walk consistency target for the canonical induced
boundary graph selected by the ambient annulus boundary split.
-/
def PeeledCollarOffCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) : Prop :=
  BoundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient
    (G := G) data.ambientBoundaryEdgeSet

/--
Annulus-boundary no-opposite-side off-carrier target for the canonical
induced boundary graph selected by the ambient annulus boundary split.
-/
def PeeledCollarOffCarrierOppositeSideDisconnectionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) : Prop :=
  BoundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient
    (G := G) data.ambientBoundaryEdgeSet

/--
Annulus-boundary component-attachment target: for every small cyclic cut in
the canonical induced boundary graph, each off-carrier component attaches only
to one cut side.
-/
def PeeledCollarOffCarrierComponentOneSidedAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) : Prop :=
  BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachmentsToAmbient
    (G := G) data.ambientBoundaryEdgeSet

/--
Annulus-boundary attachment-carrier-connectivity target: for every small
cyclic cut in the canonical induced boundary graph, attachments of one
off-carrier component are connected in the carrier after deleting the cut
edges.
-/
def PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) : Prop :=
  BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCarrierConnectivitiesToAmbient
    (G := G) data.ambientBoundaryEdgeSet

/--
Annulus-boundary cut-avoiding shared-endpoint reachability target: for every
small cyclic cut in the canonical induced boundary graph, attachments of one
off-carrier component can be joined through selected boundary edges avoiding
the mapped carrier cut.
-/
def PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) : Prop :=
  BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachabilitiesToAmbient
    (G := G) data.ambientBoundaryEdgeSet

/--
Annulus-boundary mapped-cut-deleted shared-endpoint connectivity target: for
every small cyclic cut, attachments of one off-carrier component are connected
in the selected-boundary shared-endpoint graph after deleting the mapped cut.
-/
def PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) : Prop :=
  BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentMappedCutAvoidingSharedEndpointConnectivitiesToAmbient
    (G := G) data.ambientBoundaryEdgeSet

/-- No-opposite-side off-carrier components supply annulus-boundary
off-carrier walk consistency. -/
theorem offCarrierWalkConsistencyTarget_of_oppositeSideDisconnectionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget :=
  boundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient_of_oppositeSideDisconnections
    (G := G) (edges := data.ambientBoundaryEdgeSet) h

/-- Annulus-boundary off-carrier walk consistency supplies the
no-opposite-side off-carrier component target. -/
theorem oppositeSideDisconnectionTarget_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget :=
  boundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient_of_offCarrierWalkConsistencies
    (G := G) (edges := data.ambientBoundaryEdgeSet) h

/-- No-opposite-side off-carrier components supply the one-sided attachment
target. -/
theorem componentOneSidedAttachmentTarget_of_oppositeSideDisconnectionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget) :
    data.PeeledCollarOffCarrierComponentOneSidedAttachmentTarget :=
  boundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachmentsToAmbient_of_oppositeSideDisconnections
    (G := G) (edges := data.ambientBoundaryEdgeSet) h

/-- One-sided off-carrier component attachments supply the no-opposite-side
off-carrier target. -/
theorem oppositeSideDisconnectionTarget_of_componentOneSidedAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarOffCarrierComponentOneSidedAttachmentTarget) :
    data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget :=
  boundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient_of_componentOneSidedAttachments
    (G := G) (edges := data.ambientBoundaryEdgeSet) h

/-- Attachment-carrier connectivity supplies the one-sided attachment target. -/
theorem componentOneSidedAttachmentTarget_of_attachmentCarrierConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget) :
    data.PeeledCollarOffCarrierComponentOneSidedAttachmentTarget :=
  boundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachmentsToAmbient_of_attachmentCarrierConnectivities
    (G := G) (edges := data.ambientBoundaryEdgeSet) h

/-- Attachment-carrier connectivity supplies annulus-boundary off-carrier walk
consistency. -/
theorem offCarrierWalkConsistencyTarget_of_attachmentCarrierConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget :=
  boundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient_of_attachmentCarrierConnectivities
    (G := G) (edges := data.ambientBoundaryEdgeSet) h

/--
Cut-avoiding shared-endpoint reachability supplies annulus-boundary
attachment-carrier connectivity.
-/
theorem attachmentCarrierConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget) :
    data.PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget :=
  boundaryEdgeSetInducedCutOffCarrierComponentAttachmentCarrierConnectivitiesToAmbient_of_cutAvoidingSharedEndpointReachabilities
    (G := G) (edges := data.ambientBoundaryEdgeSet) h

/--
Mapped-cut-deleted shared-endpoint connectivity supplies annulus-boundary
cut-avoiding shared-endpoint reachability.
-/
theorem cutAvoidingSharedEndpointReachabilityTarget_of_mappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h :
      data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget) :
    data.PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget :=
  boundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachabilitiesToAmbient_of_mappedCutAvoidingSharedEndpointConnectivities
    (G := G) (edges := data.ambientBoundaryEdgeSet) h

/--
Cut-avoiding shared-endpoint reachability supplies annulus-boundary
mapped-cut-deleted shared-endpoint connectivity.
-/
theorem mappedCutAvoidingSharedEndpointConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget) :
    data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget :=
  boundaryEdgeSetInducedCutOffCarrierComponentAttachmentMappedCutAvoidingSharedEndpointConnectivitiesToAmbient_of_cutAvoidingSharedEndpointReachabilities
    (G := G) (edges := data.ambientBoundaryEdgeSet) h

/--
The annulus-boundary cut-avoiding shared-endpoint target is equivalent to the
cut-deleted shared-endpoint connectivity target.
-/
theorem cutAvoidingSharedEndpointReachabilityTarget_iff_mappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb} :
    data.PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget ↔
      data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget :=
  boundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachabilitiesToAmbient_iff_mappedCutAvoidingSharedEndpointConnectivities
    (G := G) (edges := data.ambientBoundaryEdgeSet)

/-- The annulus-boundary off-carrier target can be stated either as walk
consistency or as no opposite-side off-carrier component. -/
theorem offCarrierWalkConsistencyTarget_iff_oppositeSideDisconnectionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb} :
    data.PeeledCollarOffCarrierWalkConsistencyTarget ↔
      data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget :=
  boundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient_iff_oppositeSideDisconnections
    (G := G) (edges := data.ambientBoundaryEdgeSet)

/-- The annulus-boundary off-carrier target can be stated either as
no-opposite-side components or as one-sided component attachments. -/
theorem oppositeSideDisconnectionTarget_iff_componentOneSidedAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb} :
    data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget ↔
      data.PeeledCollarOffCarrierComponentOneSidedAttachmentTarget :=
  boundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient_iff_componentOneSidedAttachments
    (G := G) (edges := data.ambientBoundaryEdgeSet)

/-- The annulus-boundary off-carrier target can be stated either as walk
consistency or as one-sided component attachments. -/
theorem offCarrierWalkConsistencyTarget_iff_componentOneSidedAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb} :
    data.PeeledCollarOffCarrierWalkConsistencyTarget ↔
      data.PeeledCollarOffCarrierComponentOneSidedAttachmentTarget :=
  boundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient_iff_componentOneSidedAttachments
    (G := G) (edges := data.ambientBoundaryEdgeSet)

/--
Canonical annulus-boundary local constancy implies off-carrier walk
consistency when the selected annulus boundary edge set is induced.
-/
theorem offCarrierWalkConsistencyTarget_of_localConstancies
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (hInduced : BoundaryEdgeSetInducedSubgraph data.ambientBoundaryEdgeSet)
    (hlocal :
      PeeledCollarCutAmbientSideLocalConstanciesToAmbient
        data.inducedBoundaryEmbedding) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget :=
  boundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient_of_localConstancies
    (G := G) (edges := data.ambientBoundaryEdgeSet) hInduced hlocal

/--
Canonical annulus-boundary side separation implies off-carrier walk
consistency.
-/
theorem offCarrierWalkConsistencyTarget_of_ambientSideSeparations
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (hseparate :
      PeeledCollarCutAmbientSideSeparationsToAmbient
        data.inducedBoundaryEmbedding) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget :=
  boundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient_of_ambientSideSeparations
    (G := G) (edges := data.ambientBoundaryEdgeSet) hseparate

/--
Annulus-boundary off-carrier walk consistency and no-avoiding-walk side
separation are equivalent.
-/
theorem offCarrierWalkConsistencyTarget_iff_ambientSideSeparations
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb} :
    data.PeeledCollarOffCarrierWalkConsistencyTarget ↔
      PeeledCollarCutAmbientSideSeparationsToAmbient
        data.inducedBoundaryEmbedding :=
  boundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient_iff_ambientSideSeparations
    (G := G) (edges := data.ambientBoundaryEdgeSet)

/--
Selected-boundary inducedness plus canonical annulus-boundary local constancy
implies off-carrier walk consistency.
-/
theorem offCarrierWalkConsistencyTarget_of_selectedBoundaryInducedSubgraph_of_localConstancies
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (hSelected : SelectedBoundaryInducedSubgraph emb)
    (hlocal :
      PeeledCollarCutAmbientSideLocalConstanciesToAmbient
        data.inducedBoundaryEmbedding) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget :=
  data.offCarrierWalkConsistencyTarget_of_localConstancies
    (by
      simpa [SelectedBoundaryInducedSubgraph,
        PlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet,
        data.ambientBoundary_eq] using hSelected)
    hlocal

/--
The annulus-boundary off-carrier walk consistency target gives the
carrier-endpoint target for the canonical induced annulus boundary graph.
-/
theorem carrierEndpointSupportTarget_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    data.PeeledCollarCarrierEndpointSupportTarget :=
  boundaryCarrierEndpointSupports_of_offCarrierWalkConsistencies
    (G := G) (edges := data.ambientBoundaryEdgeSet) h

/--
The annulus-boundary off-carrier walk consistency target gives no-avoiding-walk
side separation for the canonical induced annulus boundary graph.
-/
theorem peeledCollarCutAmbientSideSeparationsToAmbient_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    PeeledCollarCutAmbientSideSeparationsToAmbient data.inducedBoundaryEmbedding :=
  peeledCollarCutAmbientSideSeparationsToAmbient_of_offCarrierWalkConsistencies
    (G := G) (edges := data.ambientBoundaryEdgeSet) h

/--
The annulus-boundary off-carrier walk consistency target gives the small-cut
lift for the canonical induced annulus boundary graph.
-/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph :=
  data.peeledCollarSmallCyclicCutLiftsToAmbient_of_carrierEndpointSupportTarget
    (data.carrierEndpointSupportTarget_of_offCarrierWalkConsistencyTarget h)

/--
The ambient minimal-counterexample regime plus annulus-boundary off-carrier
walk consistency supplies cyclic five-edge-connectivity for the canonical
induced annulus boundary graph.
-/
theorem
    cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  data.cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_carrierEndpointSupportTarget
    regime
    (data.carrierEndpointSupportTarget_of_offCarrierWalkConsistencyTarget h)

end PlanarBoundaryAnnulusBoundaryData

namespace PlanarBoundaryAnnulusCollarGeometry

/--
Annulus-geometry off-carrier walk consistency target for the canonical induced
boundary graph selected by the geometry's ambient annulus boundary split.
-/
def PeeledCollarOffCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  data.boundaryData.PeeledCollarOffCarrierWalkConsistencyTarget

/--
Annulus-geometry no-opposite-side off-carrier target for the canonical induced
boundary graph selected by the geometry's ambient annulus boundary split.
-/
def PeeledCollarOffCarrierOppositeSideDisconnectionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  data.boundaryData.PeeledCollarOffCarrierOppositeSideDisconnectionTarget

/--
Annulus-geometry component-attachment target for the canonical induced
boundary graph selected by the geometry's ambient annulus boundary split.
-/
def PeeledCollarOffCarrierComponentOneSidedAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  data.boundaryData.PeeledCollarOffCarrierComponentOneSidedAttachmentTarget

/--
Annulus-geometry attachment-carrier-connectivity target for the canonical
induced boundary graph selected by the geometry's ambient annulus boundary
split.
-/
def PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  data.boundaryData.PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget

/--
Annulus-geometry cut-avoiding shared-endpoint reachability target for the
canonical induced boundary graph selected by the geometry's ambient annulus
boundary split.
-/
def PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  data.boundaryData.PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget

/--
Annulus-geometry mapped-cut-deleted shared-endpoint connectivity target.
-/
def PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  data.boundaryData
    |>.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget

/-- No-opposite-side off-carrier components supply annulus-geometry
off-carrier walk consistency. -/
theorem offCarrierWalkConsistencyTarget_of_oppositeSideDisconnectionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h : data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget :=
  data.boundaryData
    |>.offCarrierWalkConsistencyTarget_of_oppositeSideDisconnectionTarget h

/-- Annulus-geometry off-carrier walk consistency supplies the
no-opposite-side off-carrier component target. -/
theorem oppositeSideDisconnectionTarget_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget :=
  data.boundaryData
    |>.oppositeSideDisconnectionTarget_of_offCarrierWalkConsistencyTarget h

/-- No-opposite-side off-carrier components supply the annulus-geometry
one-sided attachment target. -/
theorem componentOneSidedAttachmentTarget_of_oppositeSideDisconnectionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h : data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget) :
    data.PeeledCollarOffCarrierComponentOneSidedAttachmentTarget :=
  data.boundaryData
    |>.componentOneSidedAttachmentTarget_of_oppositeSideDisconnectionTarget h

/-- One-sided off-carrier component attachments supply the annulus-geometry
no-opposite-side target. -/
theorem oppositeSideDisconnectionTarget_of_componentOneSidedAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h : data.PeeledCollarOffCarrierComponentOneSidedAttachmentTarget) :
    data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget :=
  data.boundaryData
    |>.oppositeSideDisconnectionTarget_of_componentOneSidedAttachmentTarget h

/-- Attachment-carrier connectivity supplies the annulus-geometry one-sided
attachment target. -/
theorem componentOneSidedAttachmentTarget_of_attachmentCarrierConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h : data.PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget) :
    data.PeeledCollarOffCarrierComponentOneSidedAttachmentTarget :=
  data.boundaryData
    |>.componentOneSidedAttachmentTarget_of_attachmentCarrierConnectivityTarget h

/-- Attachment-carrier connectivity supplies annulus-geometry off-carrier walk
consistency. -/
theorem offCarrierWalkConsistencyTarget_of_attachmentCarrierConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h : data.PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget :=
  data.boundaryData
    |>.offCarrierWalkConsistencyTarget_of_attachmentCarrierConnectivityTarget h

/--
Cut-avoiding shared-endpoint reachability supplies annulus-geometry
attachment-carrier connectivity.
-/
theorem attachmentCarrierConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h : data.PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget) :
    data.PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget :=
  data.boundaryData
    |>.attachmentCarrierConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget h

/--
Mapped-cut-deleted shared-endpoint connectivity supplies annulus-geometry
cut-avoiding shared-endpoint reachability.
-/
theorem cutAvoidingSharedEndpointReachabilityTarget_of_mappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget) :
    data.PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget :=
  data.boundaryData
    |>.cutAvoidingSharedEndpointReachabilityTarget_of_mappedCutAvoidingSharedEndpointConnectivityTarget
      h

/--
Cut-avoiding shared-endpoint reachability supplies annulus-geometry
mapped-cut-deleted shared-endpoint connectivity.
-/
theorem mappedCutAvoidingSharedEndpointConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h : data.PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget) :
    data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget :=
  data.boundaryData
    |>.mappedCutAvoidingSharedEndpointConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
      h

/--
The annulus-geometry cut-avoiding shared-endpoint target is equivalent to the
cut-deleted shared-endpoint connectivity target.
-/
theorem cutAvoidingSharedEndpointReachabilityTarget_iff_mappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb} :
    data.PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget ↔
      data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget :=
  data.boundaryData
    |>.cutAvoidingSharedEndpointReachabilityTarget_iff_mappedCutAvoidingSharedEndpointConnectivityTarget

/-- The annulus-geometry off-carrier target can be stated either as walk
consistency or as no opposite-side off-carrier component. -/
theorem offCarrierWalkConsistencyTarget_iff_oppositeSideDisconnectionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb} :
    data.PeeledCollarOffCarrierWalkConsistencyTarget ↔
      data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget :=
  data.boundaryData.offCarrierWalkConsistencyTarget_iff_oppositeSideDisconnectionTarget

/-- The annulus-geometry off-carrier target can be stated either as
no-opposite-side components or as one-sided component attachments. -/
theorem oppositeSideDisconnectionTarget_iff_componentOneSidedAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb} :
    data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget ↔
      data.PeeledCollarOffCarrierComponentOneSidedAttachmentTarget :=
  data.boundaryData.oppositeSideDisconnectionTarget_iff_componentOneSidedAttachmentTarget

/-- The annulus-geometry off-carrier target can be stated either as walk
consistency or as one-sided component attachments. -/
theorem offCarrierWalkConsistencyTarget_iff_componentOneSidedAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb} :
    data.PeeledCollarOffCarrierWalkConsistencyTarget ↔
      data.PeeledCollarOffCarrierComponentOneSidedAttachmentTarget :=
  data.boundaryData.offCarrierWalkConsistencyTarget_iff_componentOneSidedAttachmentTarget

/--
Canonical annulus-geometry local constancy implies off-carrier walk
consistency when the selected annulus boundary edge set is induced.
-/
theorem offCarrierWalkConsistencyTarget_of_localConstancies
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (hInduced : BoundaryEdgeSetInducedSubgraph data.ambientBoundaryEdgeSet)
    (hlocal :
      PeeledCollarCutAmbientSideLocalConstanciesToAmbient
        data.inducedBoundaryEmbedding) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget :=
  data.boundaryData.offCarrierWalkConsistencyTarget_of_localConstancies
    hInduced hlocal

/--
Canonical annulus-geometry side separation implies off-carrier walk
consistency.
-/
theorem offCarrierWalkConsistencyTarget_of_ambientSideSeparations
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (hseparate :
      PeeledCollarCutAmbientSideSeparationsToAmbient
        data.inducedBoundaryEmbedding) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget :=
  data.boundaryData.offCarrierWalkConsistencyTarget_of_ambientSideSeparations
    hseparate

/--
Canonical annulus-geometry off-carrier walk consistency and no-avoiding-walk
side separation are equivalent.
-/
theorem offCarrierWalkConsistencyTarget_iff_ambientSideSeparations
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb} :
    data.PeeledCollarOffCarrierWalkConsistencyTarget ↔
      PeeledCollarCutAmbientSideSeparationsToAmbient
        data.inducedBoundaryEmbedding :=
  data.boundaryData.offCarrierWalkConsistencyTarget_iff_ambientSideSeparations

/--
The annulus-geometry off-carrier walk consistency target gives
no-avoiding-walk side separation for the canonical induced annulus boundary
graph.
-/
theorem peeledCollarCutAmbientSideSeparationsToAmbient_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    PeeledCollarCutAmbientSideSeparationsToAmbient data.inducedBoundaryEmbedding :=
  data.boundaryData
    |>.peeledCollarCutAmbientSideSeparationsToAmbient_of_offCarrierWalkConsistencyTarget
      h

/--
The annulus-geometry off-carrier walk consistency target gives the small-cut
lift for the canonical induced annulus boundary graph.
-/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph :=
  data.boundaryData.peeledCollarSmallCyclicCutLiftsToAmbient_of_offCarrierWalkConsistencyTarget
    h

/--
The ambient minimal-counterexample regime plus annulus-geometry off-carrier
walk consistency supplies cyclic five-edge-connectivity for the canonical
induced annulus boundary graph.
-/
theorem
    cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  data.boundaryData
    |>.cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_offCarrierWalkConsistencyTarget
      regime h

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Repaired annulus-geometry off-carrier walk consistency target for the
canonical induced boundary graph selected by the geometry's ambient annulus
boundary split.
-/
def PeeledCollarOffCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) : Prop :=
  data.toPlanarBoundaryAnnulusCollarGeometry.PeeledCollarOffCarrierWalkConsistencyTarget

/--
Repaired annulus-geometry no-opposite-side off-carrier target for the
canonical induced boundary graph selected by the geometry's ambient annulus
boundary split.
-/
def PeeledCollarOffCarrierOppositeSideDisconnectionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) : Prop :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.PeeledCollarOffCarrierOppositeSideDisconnectionTarget

/--
Repaired annulus-geometry component-attachment target for the canonical
induced boundary graph selected by the geometry's ambient annulus boundary
split.
-/
def PeeledCollarOffCarrierComponentOneSidedAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) : Prop :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.PeeledCollarOffCarrierComponentOneSidedAttachmentTarget

/--
Repaired annulus-geometry attachment-carrier-connectivity target for the
canonical induced boundary graph selected by the geometry's ambient annulus
boundary split.
-/
def PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) : Prop :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget

/--
Repaired annulus-geometry cut-avoiding shared-endpoint reachability target for
the canonical induced boundary graph selected by the geometry's ambient
annulus boundary split.
-/
def PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) : Prop :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget

/--
Repaired annulus-geometry mapped-cut-deleted shared-endpoint connectivity
target.
-/
def PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) : Prop :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget

/-- No-opposite-side off-carrier components supply repaired annulus-geometry
off-carrier walk consistency. -/
theorem offCarrierWalkConsistencyTarget_of_oppositeSideDisconnectionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h : data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.offCarrierWalkConsistencyTarget_of_oppositeSideDisconnectionTarget h

/-- Repaired annulus-geometry off-carrier walk consistency supplies the
no-opposite-side off-carrier component target. -/
theorem oppositeSideDisconnectionTarget_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.oppositeSideDisconnectionTarget_of_offCarrierWalkConsistencyTarget h

/-- No-opposite-side off-carrier components supply the repaired annulus
one-sided attachment target. -/
theorem componentOneSidedAttachmentTarget_of_oppositeSideDisconnectionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h : data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget) :
    data.PeeledCollarOffCarrierComponentOneSidedAttachmentTarget :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.componentOneSidedAttachmentTarget_of_oppositeSideDisconnectionTarget h

/-- One-sided off-carrier component attachments supply the repaired annulus
no-opposite-side target. -/
theorem oppositeSideDisconnectionTarget_of_componentOneSidedAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h : data.PeeledCollarOffCarrierComponentOneSidedAttachmentTarget) :
    data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.oppositeSideDisconnectionTarget_of_componentOneSidedAttachmentTarget h

/-- Attachment-carrier connectivity supplies the repaired-annulus one-sided
attachment target. -/
theorem componentOneSidedAttachmentTarget_of_attachmentCarrierConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h : data.PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget) :
    data.PeeledCollarOffCarrierComponentOneSidedAttachmentTarget :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.componentOneSidedAttachmentTarget_of_attachmentCarrierConnectivityTarget h

/-- Attachment-carrier connectivity supplies repaired-annulus off-carrier walk
consistency. -/
theorem offCarrierWalkConsistencyTarget_of_attachmentCarrierConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h : data.PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.offCarrierWalkConsistencyTarget_of_attachmentCarrierConnectivityTarget h

/--
Cut-avoiding shared-endpoint reachability supplies repaired-annulus
attachment-carrier connectivity.
-/
theorem attachmentCarrierConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h : data.PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget) :
    data.PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.attachmentCarrierConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget h

/--
Mapped-cut-deleted shared-endpoint connectivity supplies repaired-annulus
cut-avoiding shared-endpoint reachability.
-/
theorem cutAvoidingSharedEndpointReachabilityTarget_of_mappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget) :
    data.PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.cutAvoidingSharedEndpointReachabilityTarget_of_mappedCutAvoidingSharedEndpointConnectivityTarget
      h

/--
Cut-avoiding shared-endpoint reachability supplies repaired-annulus
mapped-cut-deleted shared-endpoint connectivity.
-/
theorem mappedCutAvoidingSharedEndpointConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h : data.PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget) :
    data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.mappedCutAvoidingSharedEndpointConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
      h

/--
The repaired-annulus cut-avoiding shared-endpoint target is equivalent to the
cut-deleted shared-endpoint connectivity target.
-/
theorem cutAvoidingSharedEndpointReachabilityTarget_iff_mappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb} :
    data.PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget ↔
      data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.cutAvoidingSharedEndpointReachabilityTarget_iff_mappedCutAvoidingSharedEndpointConnectivityTarget

/-- The repaired annulus-geometry off-carrier target can be stated either as
walk consistency or as no opposite-side off-carrier component. -/
theorem offCarrierWalkConsistencyTarget_iff_oppositeSideDisconnectionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb} :
    data.PeeledCollarOffCarrierWalkConsistencyTarget ↔
      data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.offCarrierWalkConsistencyTarget_iff_oppositeSideDisconnectionTarget

/-- The repaired annulus-geometry off-carrier target can be stated either as
no-opposite-side components or as one-sided component attachments. -/
theorem oppositeSideDisconnectionTarget_iff_componentOneSidedAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb} :
    data.PeeledCollarOffCarrierOppositeSideDisconnectionTarget ↔
      data.PeeledCollarOffCarrierComponentOneSidedAttachmentTarget :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.oppositeSideDisconnectionTarget_iff_componentOneSidedAttachmentTarget

/-- The repaired annulus-geometry off-carrier target can be stated either as
walk consistency or as one-sided component attachments. -/
theorem offCarrierWalkConsistencyTarget_iff_componentOneSidedAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb} :
    data.PeeledCollarOffCarrierWalkConsistencyTarget ↔
      data.PeeledCollarOffCarrierComponentOneSidedAttachmentTarget :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.offCarrierWalkConsistencyTarget_iff_componentOneSidedAttachmentTarget

/--
Canonical repaired-annulus local constancy implies off-carrier walk
consistency when the selected annulus boundary edge set is induced.
-/
theorem offCarrierWalkConsistencyTarget_of_localConstancies
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (hInduced : BoundaryEdgeSetInducedSubgraph data.ambientBoundaryEdgeSet)
    (hlocal :
      PeeledCollarCutAmbientSideLocalConstanciesToAmbient
        data.inducedBoundaryEmbedding) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.offCarrierWalkConsistencyTarget_of_localConstancies hInduced hlocal

/--
Repaired annulus-geometry side separation implies off-carrier walk consistency.
-/
theorem offCarrierWalkConsistencyTarget_of_ambientSideSeparations
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (hseparate :
      PeeledCollarCutAmbientSideSeparationsToAmbient
        data.inducedBoundaryEmbedding) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.offCarrierWalkConsistencyTarget_of_ambientSideSeparations
      hseparate

/--
Repaired annulus-geometry off-carrier walk consistency and no-avoiding-walk
side separation are equivalent.
-/
theorem offCarrierWalkConsistencyTarget_iff_ambientSideSeparations
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb} :
    data.PeeledCollarOffCarrierWalkConsistencyTarget ↔
      PeeledCollarCutAmbientSideSeparationsToAmbient
        data.inducedBoundaryEmbedding :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.offCarrierWalkConsistencyTarget_iff_ambientSideSeparations

/--
The repaired annulus-geometry off-carrier walk consistency target gives
no-avoiding-walk side separation for the canonical induced annulus boundary
graph.
-/
theorem peeledCollarCutAmbientSideSeparationsToAmbient_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    PeeledCollarCutAmbientSideSeparationsToAmbient data.inducedBoundaryEmbedding :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.peeledCollarCutAmbientSideSeparationsToAmbient_of_offCarrierWalkConsistencyTarget
      h

/--
The repaired annulus-geometry off-carrier walk consistency target gives the
small-cut lift for the canonical induced annulus boundary graph.
-/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.peeledCollarSmallCyclicCutLiftsToAmbient_of_offCarrierWalkConsistencyTarget h

/--
The ambient minimal-counterexample regime plus repaired annulus-geometry
off-carrier walk consistency supplies cyclic five-edge-connectivity for the
canonical induced annulus boundary graph.
-/
theorem
    cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_offCarrierWalkConsistencyTarget
      regime h

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

end Mettapedia.GraphTheory.FourColor
