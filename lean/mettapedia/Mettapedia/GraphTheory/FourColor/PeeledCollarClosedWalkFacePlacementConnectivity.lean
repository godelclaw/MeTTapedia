import Mettapedia.GraphTheory.FourColor.PeeledCollarClosedWalkFacePlacementEquiv

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
The closed-walk face-placement target, together with the selected-boundary
arc geometry already carried by the closed-walk source, supplies the
selected-boundary-arc source target on the extracted annulus boundary split.
-/
theorem noncrossingSelectedBoundaryArcSourceTarget_of_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.PeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget :=
  source.toPlanarBoundaryAnnulusBoundaryData
    |>.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceDataTarget
      source.toPlanarBoundarySelectedBoundaryArcGeometry.boundarySelectedBoundaryArcOnFace
      (source.attachmentFaceSourceDataTarget_of_facePlacementNoncrossingTarget h)

/--
The closed-walk face-placement target supplies mapped-cut-deleted
shared-endpoint connectivity for off-carrier attachment pairs.
-/
theorem mappedCutAvoidingSharedEndpointConnectivityTarget_of_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget :=
  source.toPlanarBoundaryAnnulusBoundaryData
    |>.mappedCutAvoidingSharedEndpointConnectivityTarget_of_noncrossingSelectedBoundaryArcSourceTarget
      (source.noncrossingSelectedBoundaryArcSourceTarget_of_facePlacementNoncrossingTarget h)

/--
The closed-walk face-placement target supplies off-carrier walk consistency
for the extracted annulus boundary split.
-/
theorem offCarrierWalkConsistencyTarget_of_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.PeeledCollarOffCarrierWalkConsistencyTarget := by
  let data := source.toPlanarBoundaryAnnulusBoundaryData
  have hmapped :
      data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget :=
    source.mappedCutAvoidingSharedEndpointConnectivityTarget_of_facePlacementNoncrossingTarget
      h
  have hreachable :
      data.PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget :=
    data.cutAvoidingSharedEndpointReachabilityTarget_of_mappedCutAvoidingSharedEndpointConnectivityTarget
      hmapped
  have hcarrier :
      data.PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget :=
    data.attachmentCarrierConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
      hreachable
  exact data.offCarrierWalkConsistencyTarget_of_attachmentCarrierConnectivityTarget hcarrier

/--
The closed-walk face-placement target supplies the graph-facing small-cut lift
for the induced annulus boundary graph.
-/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
  source.toPlanarBoundaryAnnulusBoundaryData
    |>.peeledCollarSmallCyclicCutLiftsToAmbient_of_offCarrierWalkConsistencyTarget
      (source.offCarrierWalkConsistencyTarget_of_facePlacementNoncrossingTarget h)

/--
The ambient minimal-counterexample regime plus closed-walk face-placement
noncrossing data supplies cyclic five-edge-connectivity for the source's
induced annulus boundary graph.
-/
theorem cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
    CyclicallyFiveEdgeConnected
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
  source.toPlanarBoundaryAnnulusBoundaryData
    |>.cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_offCarrierWalkConsistencyTarget
      regime
      (source.offCarrierWalkConsistencyTarget_of_facePlacementNoncrossingTarget h)

/--
Regime-discharged S4 salvage on the source's induced annulus boundary graph,
with cyclic five-edge-connectivity supplied by the closed-walk face-placement
target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_minimalCounterexampleRegime_of_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
    ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
  closedCollarWindingFreedomSeparatorEquippedEscape_not_realizable_of_cyclicallyFiveEdgeConnected
    (source.cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_facePlacementNoncrossingTarget
      regime h)

end PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Closed-walk source target: face-placement noncrossing data supplies the
graph-facing small-cut lift for the source's induced annulus boundary graph.
-/
def Section92Step4ClosedWalkFacePlacementSmallCutLiftTarget : Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      source.OffCarrierAttachmentFacePlacementNoncrossingTarget →
        PeeledCollarSmallCyclicCutLiftsToAmbient G
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/-- Verbatim closed-walk face-placement small-cut-lift statement. -/
theorem section92Step4ClosedWalkFacePlacementSmallCutLiftTarget :
    Section92Step4ClosedWalkFacePlacementSmallCutLiftTarget := by
  intro V _ G emb source h
  exact source.peeledCollarSmallCyclicCutLiftsToAmbient_of_facePlacementNoncrossingTarget h

/--
Closed-walk source target: the minimal-counterexample regime plus
face-placement noncrossing data supplies cyclic five-edge-connectivity for the
source's induced annulus boundary graph.
-/
def Section92Step4ClosedWalkFacePlacementCyclicallyFiveEdgeConnectedTarget :
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
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/-- Verbatim closed-walk face-placement cyclic-connectivity statement. -/
theorem section92Step4ClosedWalkFacePlacementCyclicallyFiveEdgeConnectedTarget :
    Section92Step4ClosedWalkFacePlacementCyclicallyFiveEdgeConnectedTarget := by
  intro V _ G emb source regime h
  exact
    source.cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_facePlacementNoncrossingTarget
      regime h

/--
Closed-walk source target: regime-discharged S4 salvage with cyclic
five-edge-connectivity supplied by face-placement noncrossing data.
-/
def Section92Step4ClosedWalkFacePlacementRegimeDischargedS4SalvageTarget :
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
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/-- Verbatim closed-walk face-placement S4 statement through cyclic connectivity. -/
theorem section92Step4ClosedWalkFacePlacementRegimeDischargedS4SalvageTarget :
    Section92Step4ClosedWalkFacePlacementRegimeDischargedS4SalvageTarget := by
  intro V _ G emb source regime h
  exact
    source.closedCollarWindingFreedomEscape_not_simplyRealizable_of_minimalCounterexampleRegime_of_facePlacementNoncrossingTarget
      regime h

end Mettapedia.GraphTheory.FourColor
