import Mettapedia.GraphTheory.FourColor.PeeledCollarAnnulusBoundarySupportExtraction

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/--
For the canonical endpoint-support induced graph, an ambient vertex is in the
embedding range exactly when it lies in the finite edge set's endpoint support.
-/
theorem boundaryEdgeSetInducedGraphEmbedding_range_iff_endpointSupport
    {G : SimpleGraph V} {edges : Finset G.edgeSet} {v : V} :
    (∃ w : BoundaryEdgeSetEndpointVertex (G := G) edges,
      boundaryEdgeSetInducedGraphEmbedding (G := G) edges w = v) ↔
      v ∈ boundaryEdgeSetEndpointSupport edges := by
  constructor
  · rintro ⟨w, hw⟩
    rw [← hw]
    exact boundaryEdgeSetEndpointVertex_mem w
  · exact exists_preimage_boundaryEdgeSetInducedGraphEmbedding_of_mem_endpointSupport

/--
Endpoint-range over the canonical induced graph is the same as endpoint
membership in the finite edge set's endpoint support.
-/
theorem boundaryEdgeSetInducedGraphEmbedding_endpointRange_iff_endpointSupport
    {G : SimpleGraph V} {edges : Finset G.edgeSet} {e : G.edgeSet} :
    (∀ v : V, v ∈ (e : Sym2 V) →
      ∃ w : BoundaryEdgeSetEndpointVertex (G := G) edges,
        boundaryEdgeSetInducedGraphEmbedding (G := G) edges w = v) ↔
      ∀ v : V, v ∈ (e : Sym2 V) →
        v ∈ boundaryEdgeSetEndpointSupport edges := by
  constructor
  · intro hrange v hv
    exact (boundaryEdgeSetInducedGraphEmbedding_range_iff_endpointSupport
      (G := G) (edges := edges) (v := v)).1 (hrange v hv)
  · intro hsupport v hv
    exact (boundaryEdgeSetInducedGraphEmbedding_range_iff_endpointSupport
      (G := G) (edges := edges) (v := v)).2 (hsupport v hv)

/--
Carrier-endpoint-support datum for one cut of the canonical induced boundary
graph.  The ambient side agrees with the collar cut side on boundary-carrier
vertices, and every ambient side-crossing edge has all endpoints in the
carrier endpoint support.

This is weaker than demanding endpoints in the mapped cut support: the generic
embedding reflection layer then proves that any carrier-supported crossing
edge is already a mapped collar-cut edge.
-/
structure BoundaryEdgeSetInducedCutAmbientSideEndpointSupport
    {G : SimpleGraph V} (edges : Finset G.edgeSet)
    (cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)) where
  side : V → Prop
  side_comp_embedding :
    ∀ w, side (boundaryEdgeSetInducedGraphEmbedding (G := G) edges w) ↔ cut.side w
  crossingEdge_endpointSupport :
    ∀ e : G.edgeSet,
      EdgeCrossesVertexSide G side e →
        ∀ v : V, v ∈ (e : Sym2 V) →
          v ∈ boundaryEdgeSetEndpointSupport edges

namespace BoundaryEdgeSetInducedCutAmbientSideEndpointSupport

/--
Carrier endpoint-support data give the existing endpoint-range datum for the
canonical induced boundary graph.
-/
def toAmbientSideEndpointRange
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    (support :
      BoundaryEdgeSetInducedCutAmbientSideEndpointSupport (G := G) edges cut) :
    PeeledCollarCutAmbientSideEndpointRange
      (boundaryEdgeSetInducedGraphEmbedding (G := G) edges) cut where
  side := support.side
  side_comp_embedding := support.side_comp_embedding
  crossingEdge_endpointRange := by
    intro e hcross
    exact
      (boundaryEdgeSetInducedGraphEmbedding_endpointRange_iff_endpointSupport
        (G := G) (edges := edges) (e := e)).2
        (support.crossingEdge_endpointSupport e hcross)

/--
Carrier endpoint-support data give the existing preimage datum for the
canonical induced boundary graph.
-/
def toAmbientSidePreimage
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    (support :
      BoundaryEdgeSetInducedCutAmbientSideEndpointSupport (G := G) edges cut) :
    PeeledCollarCutAmbientSidePreimage
      (boundaryEdgeSetInducedGraphEmbedding (G := G) edges) cut :=
  support.toAmbientSideEndpointRange.toAmbientSidePreimage

/--
Carrier endpoint-support data give the edge-barrier datum for the canonical
induced boundary graph.
-/
def toAmbientSideBarrier
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    (support :
      BoundaryEdgeSetInducedCutAmbientSideEndpointSupport (G := G) edges cut) :
    PeeledCollarCutAmbientSideBarrier
      (boundaryEdgeSetInducedGraphEmbedding (G := G) edges) cut :=
  support.toAmbientSideEndpointRange.toAmbientSideBarrier

/--
Carrier endpoint-support data give the no-avoiding-walk separation datum for
the canonical induced boundary graph.
-/
def toAmbientSideSeparation
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    (support :
      BoundaryEdgeSetInducedCutAmbientSideEndpointSupport (G := G) edges cut) :
    PeeledCollarCutAmbientSideSeparation
      (boundaryEdgeSetInducedGraphEmbedding (G := G) edges) cut :=
  support.toAmbientSideEndpointRange.toAmbientSideSeparation

/--
Carrier endpoint-support data give the concrete side-extension datum for the
canonical induced boundary graph.
-/
def toCutSideExtension
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    {cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges)}
    (support :
      BoundaryEdgeSetInducedCutAmbientSideEndpointSupport (G := G) edges cut) :
    PeeledCollarCutSideExtension
      (boundaryEdgeSetInducedGraphEmbedding (G := G) edges) cut :=
  support.toAmbientSideEndpointRange.toCutSideExtension

end BoundaryEdgeSetInducedCutAmbientSideEndpointSupport

/--
Carrier-endpoint foundation target for the canonical induced boundary graph:
every small cyclic cut has an ambient side whose side-crossing ambient edges
have endpoints in the finite carrier endpoint support.
-/
def BoundaryEdgeSetInducedCutAmbientSideEndpointSupportsToAmbient
    {G : SimpleGraph V} (edges : Finset G.edgeSet) : Prop :=
  ∀ cut : SmallCyclicEdgeCut (BoundaryEdgeSetInducedGraph (G := G) edges),
    Nonempty (BoundaryEdgeSetInducedCutAmbientSideEndpointSupport (G := G) edges cut)

/--
Carrier endpoint-support data imply the existing endpoint-range target for the
canonical induced boundary graph.
-/
theorem peeledCollarCutAmbientSideEndpointRangesToAmbient_of_boundaryCarrierEndpointSupports
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hsupport :
      BoundaryEdgeSetInducedCutAmbientSideEndpointSupportsToAmbient (G := G) edges) :
    PeeledCollarCutAmbientSideEndpointRangesToAmbient
      (boundaryEdgeSetInducedGraphEmbedding (G := G) edges) := by
  intro cut
  rcases hsupport cut with ⟨support⟩
  exact ⟨support.toAmbientSideEndpointRange⟩

/--
Carrier endpoint-support data imply the existing preimage target for the
canonical induced boundary graph.
-/
theorem peeledCollarCutAmbientSidePreimagesToAmbient_of_boundaryCarrierEndpointSupports
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hsupport :
      BoundaryEdgeSetInducedCutAmbientSideEndpointSupportsToAmbient (G := G) edges) :
    PeeledCollarCutAmbientSidePreimagesToAmbient
      (boundaryEdgeSetInducedGraphEmbedding (G := G) edges) :=
  peeledCollarCutAmbientSidePreimagesToAmbient_of_ambientSideEndpointRanges
    (peeledCollarCutAmbientSideEndpointRangesToAmbient_of_boundaryCarrierEndpointSupports
      hsupport)

/--
Carrier endpoint-support data imply edge barriers for the canonical induced
boundary graph.
-/
theorem peeledCollarCutAmbientSideBarriersToAmbient_of_boundaryCarrierEndpointSupports
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hsupport :
      BoundaryEdgeSetInducedCutAmbientSideEndpointSupportsToAmbient (G := G) edges) :
    PeeledCollarCutAmbientSideBarriersToAmbient
      (boundaryEdgeSetInducedGraphEmbedding (G := G) edges) :=
  peeledCollarCutAmbientSideBarriersToAmbient_of_ambientSideEndpointRanges
    (peeledCollarCutAmbientSideEndpointRangesToAmbient_of_boundaryCarrierEndpointSupports
      hsupport)

/--
Carrier endpoint-support data imply no-avoiding-walk side separations for the
canonical induced boundary graph.
-/
theorem
    peeledCollarCutAmbientSideSeparationsToAmbient_of_boundaryCarrierEndpointSupports
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hsupport :
      BoundaryEdgeSetInducedCutAmbientSideEndpointSupportsToAmbient (G := G) edges) :
    PeeledCollarCutAmbientSideSeparationsToAmbient
      (boundaryEdgeSetInducedGraphEmbedding (G := G) edges) :=
  peeledCollarCutAmbientSideSeparationsToAmbient_of_ambientSideEndpointRanges
    (peeledCollarCutAmbientSideEndpointRangesToAmbient_of_boundaryCarrierEndpointSupports
      hsupport)

/--
Carrier endpoint-support data imply concrete side extensions for the canonical
induced boundary graph.
-/
theorem peeledCollarCutSideExtensionsToAmbient_of_boundaryCarrierEndpointSupports
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hsupport :
      BoundaryEdgeSetInducedCutAmbientSideEndpointSupportsToAmbient (G := G) edges) :
    PeeledCollarCutSideExtensionsToAmbient
      (boundaryEdgeSetInducedGraphEmbedding (G := G) edges) :=
  peeledCollarCutSideExtensionsToAmbient_of_ambientSideEndpointRanges
    (peeledCollarCutAmbientSideEndpointRangesToAmbient_of_boundaryCarrierEndpointSupports
      hsupport)

/--
Carrier endpoint-support data imply the graph-facing small-cut lift for the
canonical induced boundary graph.
-/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_boundaryCarrierEndpointSupports
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (hsupport :
      BoundaryEdgeSetInducedCutAmbientSideEndpointSupportsToAmbient (G := G) edges) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideEndpointRanges
    (peeledCollarCutAmbientSideEndpointRangesToAmbient_of_boundaryCarrierEndpointSupports
      hsupport)

/--
Regime-facing inheritance theorem from carrier endpoint-support data for the
canonical induced boundary graph.
-/
theorem
    peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_boundaryCarrierEndpointSupports
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) edges)
        (BoundaryEdgeSetInducedGraph (G := G) edges))
    (hsupport :
      BoundaryEdgeSetInducedCutAmbientSideEndpointSupportsToAmbient (G := G) edges) :
    CyclicallyFiveEdgeConnected (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_ambientSideEndpointRanges
    regime
    (peeledCollarCutAmbientSideEndpointRangesToAmbient_of_boundaryCarrierEndpointSupports
      hsupport)

namespace PlanarBoundaryAnnulusBoundaryData

/--
Annulus-boundary carrier-endpoint target for the canonical induced boundary
graph selected by the ambient annulus boundary split.
-/
def PeeledCollarCarrierEndpointSupportTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) : Prop :=
  BoundaryEdgeSetInducedCutAmbientSideEndpointSupportsToAmbient
    (G := G) data.ambientBoundaryEdgeSet

/--
The annulus-boundary carrier-endpoint target gives endpoint-range data for the
canonical induced annulus boundary graph.
-/
theorem peeledCollarCutAmbientSideEndpointRangesToAmbient_of_carrierEndpointSupportTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarCarrierEndpointSupportTarget) :
    PeeledCollarCutAmbientSideEndpointRangesToAmbient data.inducedBoundaryEmbedding :=
  peeledCollarCutAmbientSideEndpointRangesToAmbient_of_boundaryCarrierEndpointSupports
    (G := G) (edges := data.ambientBoundaryEdgeSet) h

/--
The annulus-boundary carrier-endpoint target gives the small-cut lift for the
canonical induced annulus boundary graph.
-/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_carrierEndpointSupportTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarCarrierEndpointSupportTarget) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph :=
  peeledCollarSmallCyclicCutLiftsToAmbient_of_boundaryCarrierEndpointSupports
    (G := G) (edges := data.ambientBoundaryEdgeSet) h

/--
The ambient minimal-counterexample regime plus the annulus-boundary
carrier-endpoint target supplies cyclic five-edge-connectivity for the
canonical induced annulus boundary graph.
-/
theorem
    cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_carrierEndpointSupportTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h : data.PeeledCollarCarrierEndpointSupportTarget) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_boundaryCarrierEndpointSupports
    regime h

end PlanarBoundaryAnnulusBoundaryData

namespace PlanarBoundaryAnnulusCollarGeometry

/--
Annulus-geometry carrier-endpoint target for the canonical induced boundary
graph selected by the geometry's ambient annulus boundary split.
-/
def PeeledCollarCarrierEndpointSupportTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  data.boundaryData.PeeledCollarCarrierEndpointSupportTarget

/--
The annulus-geometry carrier-endpoint target gives the small-cut lift for the
canonical induced annulus boundary graph.
-/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_carrierEndpointSupportTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h : data.PeeledCollarCarrierEndpointSupportTarget) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph :=
  data.boundaryData.peeledCollarSmallCyclicCutLiftsToAmbient_of_carrierEndpointSupportTarget
    h

/--
The ambient minimal-counterexample regime plus the annulus-geometry
carrier-endpoint target supplies cyclic five-edge-connectivity for the
canonical induced annulus boundary graph.
-/
theorem
    cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_carrierEndpointSupportTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h : data.PeeledCollarCarrierEndpointSupportTarget) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  data.boundaryData
    |>.cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_carrierEndpointSupportTarget
      regime h

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Repaired annulus-geometry carrier-endpoint target for the canonical induced
boundary graph selected by the geometry's ambient annulus boundary split.
-/
def PeeledCollarCarrierEndpointSupportTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) : Prop :=
  data.toPlanarBoundaryAnnulusCollarGeometry.PeeledCollarCarrierEndpointSupportTarget

/--
The repaired annulus-geometry carrier-endpoint target gives the small-cut lift
for the canonical induced annulus boundary graph.
-/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_carrierEndpointSupportTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h : data.PeeledCollarCarrierEndpointSupportTarget) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.peeledCollarSmallCyclicCutLiftsToAmbient_of_carrierEndpointSupportTarget h

/--
The ambient minimal-counterexample regime plus the repaired annulus-geometry
carrier-endpoint target supplies cyclic five-edge-connectivity for the
canonical induced annulus boundary graph.
-/
theorem
    cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_carrierEndpointSupportTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h : data.PeeledCollarCarrierEndpointSupportTarget) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_carrierEndpointSupportTarget
      regime h

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

end Mettapedia.GraphTheory.FourColor
