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
