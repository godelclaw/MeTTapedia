import Mettapedia.GraphTheory.FourColor.PeeledCollarClosedWalkFacePlacementConnectivity
import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeOffBoundaryFaceSource

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Closed-walk face-placement bridge into the off-boundary interface.

The face-placement target is the source-level planar-normal-form obligation
for a closed-walk boundary source.  This module exposes the stronger
off-boundary, local-constancy, and separation consequences before packaging
the graph-facing small-cut lift and the downstream closed-collar S4 salvage.
-/

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Closed-walk face-placement data supplies off-boundary no-crossing for the
source's selected induced boundary embedding.
-/
theorem offBoundaryNoCrossingsToAmbient_of_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
    PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
  source.toPlanarBoundaryAnnulusBoundaryData
    |>.peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_offCarrierWalkConsistencyTarget
      (source.offCarrierWalkConsistencyTarget_of_facePlacementNoncrossingTarget h)

/--
Closed-walk face-placement data supplies local side constancy for the source's
selected induced boundary embedding.
-/
theorem localConstanciesToAmbient_of_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
    PeeledCollarCutAmbientSideLocalConstanciesToAmbient
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
  peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_ambientSideOffBoundaryNoCrossings
    (source.offBoundaryNoCrossingsToAmbient_of_facePlacementNoncrossingTarget h)

/--
Closed-walk face-placement data supplies no-avoiding-walk side separations for
the source's selected induced boundary embedding.
-/
theorem separationsToAmbient_of_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
    PeeledCollarCutAmbientSideSeparationsToAmbient
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
  peeledCollarCutAmbientSideSeparationsToAmbient_of_localConstancies
    (source.localConstanciesToAmbient_of_facePlacementNoncrossingTarget h)

/--
Closed-walk face-placement data, together with the minimal-counterexample
regime, supplies the full off-boundary route consequences for the selected
induced boundary graph.
-/
theorem offBoundaryRouteConsequences_of_minimalCounterexampleRegime_of_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
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
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph := by
  have hoffBoundary :
      PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
    source.offBoundaryNoCrossingsToAmbient_of_facePlacementNoncrossingTarget h
  have hlocal :
      PeeledCollarCutAmbientSideLocalConstanciesToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
    peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_ambientSideOffBoundaryNoCrossings
      hoffBoundary
  have hseparate :
      PeeledCollarCutAmbientSideSeparationsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
    peeledCollarCutAmbientSideSeparationsToAmbient_of_localConstancies
      hlocal
  have hlift :
      PeeledCollarSmallCyclicCutLiftsToAmbient G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
    peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideOffBoundaryNoCrossings
      hoffBoundary
  let inputs :
      MinimalCounterexamplePeeledCollarRouteInputs G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph := {
    regime := regime
    smallCutLift := hlift
  }
  exact
    ⟨hoffBoundary,
      hlocal,
      hseparate,
      hlift,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

end PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Closed-walk source route target: face-placement data supplies off-boundary
no-crossing, local constancy, separation, the small-cut lift, cyclic
five-edge-connectivity, no cyclic two-cut, and S4 no-escape.
-/
def Section92Step4ClosedWalkFacePlacementOffBoundaryRouteIndexTarget :
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
      source.OffCarrierAttachmentFacePlacementNoncrossingTarget →
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

/-- Route-index theorem for the closed-walk face-placement off-boundary bridge. -/
theorem section92Step4ClosedWalkFacePlacementOffBoundaryRouteIndexTarget :
    Section92Step4ClosedWalkFacePlacementOffBoundaryRouteIndexTarget := by
  intro V _ G emb source regime h
  exact
    source.offBoundaryRouteConsequences_of_minimalCounterexampleRegime_of_facePlacementNoncrossingTarget
      regime h

end Mettapedia.GraphTheory.FourColor
