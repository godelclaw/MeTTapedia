import Mettapedia.GraphTheory.FourColor.PeeledCollarRegimeFacePlacementFoundationIndex
import Mettapedia.GraphTheory.FourColor.PeeledCollarClosedWalkFacePlacementOffBoundaryRoute

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Regime face-placement bridge into the off-boundary interface.

The named regime face-placement foundation target is the source-level
interface a planar-normal-form proof is expected to supply.  This module
exposes the off-boundary, local-constancy, and separation consequences of
that named target, before packaging the small-cut lift and S4 route.
-/

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
The named regime face-placement target supplies off-boundary no-crossing for
the source's selected induced boundary embedding.
-/
theorem offBoundaryNoCrossingsToAmbient_of_regimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeFacePlacementFoundationTarget) :
    PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
  source.offBoundaryNoCrossingsToAmbient_of_facePlacementNoncrossingTarget
    ((source.regimeFacePlacementFoundationTarget_iff_facePlacementNoncrossingTarget).1
      h)

/--
The named regime face-placement target supplies local side constancy for the
source's selected induced boundary embedding.
-/
theorem localConstanciesToAmbient_of_regimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeFacePlacementFoundationTarget) :
    PeeledCollarCutAmbientSideLocalConstanciesToAmbient
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
  source.localConstanciesToAmbient_of_facePlacementNoncrossingTarget
    ((source.regimeFacePlacementFoundationTarget_iff_facePlacementNoncrossingTarget).1
      h)

/--
The named regime face-placement target supplies no-avoiding-walk side
separations for the source's selected induced boundary embedding.
-/
theorem separationsToAmbient_of_regimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeFacePlacementFoundationTarget) :
    PeeledCollarCutAmbientSideSeparationsToAmbient
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
  source.separationsToAmbient_of_facePlacementNoncrossingTarget
    ((source.regimeFacePlacementFoundationTarget_iff_facePlacementNoncrossingTarget).1
      h)

/--
The named regime face-placement target supplies the full off-boundary route
consequences for the source's selected induced boundary graph.
-/
theorem offBoundaryRouteConsequences_of_regimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h : source.RegimeFacePlacementFoundationTarget) :
    PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
      PeeledCollarCutAmbientSideLocalConstanciesToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
      PeeledCollarCutAmbientSideSeparationsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
      PeeledCollarSmallCyclicCutLiftsToAmbient G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      CyclicallyFiveEdgeConnected
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
  source.offBoundaryRouteConsequences_of_minimalCounterexampleRegime_of_facePlacementNoncrossingTarget
    regime
    ((source.regimeFacePlacementFoundationTarget_iff_facePlacementNoncrossingTarget).1
      h)

end PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Closed-walk source route target: the named regime face-placement foundation
supplies off-boundary no-crossing, local constancy, separation, the small-cut
lift, cyclic five-edge-connectivity, no cyclic two-cut, and S4 no-escape.
-/
def Section92Step4ClosedWalkRegimeFacePlacementOffBoundaryRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph),
      source.RegimeFacePlacementFoundationTarget →
        PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
            source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
          PeeledCollarCutAmbientSideLocalConstanciesToAmbient
            source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
          PeeledCollarCutAmbientSideSeparationsToAmbient
            source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
          PeeledCollarSmallCyclicCutLiftsToAmbient G
            source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
          CyclicallyFiveEdgeConnected
            source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
          ClosedCollarForbidsCyclicTwoCut
            source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
          ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
            source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/--
Route-index theorem for the named regime face-placement off-boundary bridge.
-/
theorem section92Step4ClosedWalkRegimeFacePlacementOffBoundaryRouteIndexTarget :
    Section92Step4ClosedWalkRegimeFacePlacementOffBoundaryRouteIndexTarget := by
  intro V _ G emb source regime h
  exact
    source.offBoundaryRouteConsequences_of_regimeFacePlacementFoundationTarget
      regime h

end Mettapedia.GraphTheory.FourColor
