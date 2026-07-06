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
