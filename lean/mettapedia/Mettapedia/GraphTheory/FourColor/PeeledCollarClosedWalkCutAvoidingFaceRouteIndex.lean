import Mettapedia.GraphTheory.FourColor.PeeledCollarClosedWalkCutAvoidingFaceRouteCompatibility

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

variable {V : Type} [DecidableEq V]

/--
Reusable index for the closed-walk cut-avoiding face-route regime path.  The
remaining planar-normal-form obligation is exactly the mapped-cut-avoiding
face-route source target; cyclic five-edge-connectivity is derived, not
assumed.
-/
structure ClosedWalkMappedCutAvoidingFaceRouteInputs
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) where
  regime :
    MinimalCounterexamplePeeledCollarRegime G
      (BoundaryEdgeSetEndpointVertex
        (G := G)
        source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph
  mappedCutAvoidingFaceRoute :
    source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget

namespace ClosedWalkMappedCutAvoidingFaceRouteInputs

/-- The closed-walk route index supplies mapped-cut-deleted shared-endpoint connectivity. -/
theorem mappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb}
    (inputs : ClosedWalkMappedCutAvoidingFaceRouteInputs source) :
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget :=
  source.mappedCutAvoidingSharedEndpointConnectivityTarget_of_mappedCutAvoidingFaceRouteTarget
    inputs.mappedCutAvoidingFaceRoute

/-- The closed-walk route index supplies the graph-facing small-cut lift. -/
theorem peeledCollarSmallCyclicCutLiftsToAmbient
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb}
    (inputs : ClosedWalkMappedCutAvoidingFaceRouteInputs source) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
  source.peeledCollarSmallCyclicCutLiftsToAmbient_of_mappedCutAvoidingFaceRouteTarget
    inputs.mappedCutAvoidingFaceRoute

/-- The closed-walk route index supplies cyclic five-edge-connectivity. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb}
    (inputs : ClosedWalkMappedCutAvoidingFaceRouteInputs source) :
    CyclicallyFiveEdgeConnected
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
  source.cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_mappedCutAvoidingFaceRouteTarget
    inputs.regime inputs.mappedCutAvoidingFaceRoute

/-- The closed-walk route index supplies the no-cyclic-two-cut consequence. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb}
    (inputs : ClosedWalkMappedCutAvoidingFaceRouteInputs source) :
    ClosedCollarForbidsCyclicTwoCut
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
  closedCollarForbidsCyclicTwoCut_of_cyclicallyFiveEdgeConnected
    inputs.cyclicallyFiveEdgeConnected

/-- The closed-walk route index supplies the S4 winding salvage. -/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb}
    (inputs : ClosedWalkMappedCutAvoidingFaceRouteInputs source) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
  source.closedCollarWindingFreedomEscape_not_simplyRealizable_of_minimalCounterexampleRegime_of_mappedCutAvoidingFaceRouteTarget
    inputs.regime inputs.mappedCutAvoidingFaceRoute

/-- Build the route index from the older face-placement noncrossing target. -/
def of_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
    ClosedWalkMappedCutAvoidingFaceRouteInputs source where
  regime := regime
  mappedCutAvoidingFaceRoute :=
    source.mappedCutAvoidingFaceRouteTarget_of_facePlacementNoncrossingTarget h

/--
Build the route index from chosen source-side attachment-face data.  This is
the source-data form most directly exposed by the planar normal-form route.
-/
def of_attachmentFaceSourceDataTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h :
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
        source.toPlanarBoundaryAnnulusBoundaryData) :
    ClosedWalkMappedCutAvoidingFaceRouteInputs source where
  regime := regime
  mappedCutAvoidingFaceRoute :=
    source.mappedCutAvoidingFaceRouteTarget_of_attachmentFaceSourceDataTarget h

/-- Build the route index from the noncrossing face-source target. -/
def of_noncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h :
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        source.toPlanarBoundaryAnnulusBoundaryData) :
    ClosedWalkMappedCutAvoidingFaceRouteInputs source where
  regime := regime
  mappedCutAvoidingFaceRoute :=
    source.mappedCutAvoidingFaceRouteTarget_of_noncrossingFaceSourceTarget h

/--
Build the route index from the selected-boundary-arc source target after
forgetting the explicit selected-arc witness.
-/
def of_noncrossingSelectedBoundaryArcSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h :
      source.toPlanarBoundaryAnnulusBoundaryData
        |>.PeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget) :
    ClosedWalkMappedCutAvoidingFaceRouteInputs source where
  regime := regime
  mappedCutAvoidingFaceRoute :=
    source.mappedCutAvoidingFaceRouteTarget_of_noncrossingSelectedBoundaryArcSourceTarget h

end ClosedWalkMappedCutAvoidingFaceRouteInputs

/--
Canonical annulus index for the closed-walk cut-avoiding face-route path,
aligned with the canonical annulus boundary data.
-/
structure CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) where
  regime :
    MinimalCounterexamplePeeledCollarRegime G
      (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
      data.inducedBoundaryGraph
  source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb
  boundaryData_eq_source :
    data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData
  mappedCutAvoidingFaceRoute :
    source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget

namespace CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs

/-- Canonical route inputs supply mapped-cut-deleted shared-endpoint connectivity. -/
theorem mappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs :
      CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget := by
  have hmappedSource :
      inputs.source.toPlanarBoundaryAnnulusBoundaryData
        |>.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget :=
    inputs.source
      |>.mappedCutAvoidingSharedEndpointConnectivityTarget_of_mappedCutAvoidingFaceRouteTarget
        inputs.mappedCutAvoidingFaceRoute
  change data.boundaryData
    |>.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget
  rw [inputs.boundaryData_eq_source]
  exact hmappedSource

/-- Canonical route inputs supply the older mapped-connectivity route index. -/
def toMappedCutAvoidingSharedEndpointConnectedRouteInputs
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs :
      CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    MinimalCounterexampleOffCarrierMappedCutAvoidingSharedEndpointConnectedPeeledCollarRouteInputs
      G data.ambientBoundaryEdgeSet where
  regime := inputs.regime
  offCarrierMappedCutAvoidingSharedEndpointConnectivities :=
    inputs.mappedCutAvoidingSharedEndpointConnectivityTarget

/-- Canonical route inputs supply cyclic five-edge-connectivity. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs :
      CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  inputs.toMappedCutAvoidingSharedEndpointConnectedRouteInputs
    |>.cyclicallyFiveEdgeConnected

/-- Canonical route inputs supply the no-cyclic-two-cut consequence. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs :
      CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph :=
  inputs.toMappedCutAvoidingSharedEndpointConnectedRouteInputs
    |>.closedCollarForbidsCyclicTwoCut

/-- Canonical route inputs supply the S4 winding salvage. -/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs :
      CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  inputs.toMappedCutAvoidingSharedEndpointConnectedRouteInputs
    |>.closedCollarWindingFreedomEscape_not_simplyRealizable

/-- Build canonical route inputs from the older face-placement noncrossing target. -/
def of_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
    CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data where
  regime := regime
  source := source
  boundaryData_eq_source := hboundary
  mappedCutAvoidingFaceRoute :=
    source.mappedCutAvoidingFaceRouteTarget_of_facePlacementNoncrossingTarget h

/-- Build canonical route inputs from chosen source-side attachment-face data. -/
def of_attachmentFaceSourceDataTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h :
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
        source.toPlanarBoundaryAnnulusBoundaryData) :
    CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data where
  regime := regime
  source := source
  boundaryData_eq_source := hboundary
  mappedCutAvoidingFaceRoute :=
    source.mappedCutAvoidingFaceRouteTarget_of_attachmentFaceSourceDataTarget h

/-- Build canonical route inputs from the noncrossing face-source target. -/
def of_noncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h :
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        source.toPlanarBoundaryAnnulusBoundaryData) :
    CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data where
  regime := regime
  source := source
  boundaryData_eq_source := hboundary
  mappedCutAvoidingFaceRoute :=
    source.mappedCutAvoidingFaceRouteTarget_of_noncrossingFaceSourceTarget h

/-- Build canonical route inputs from the selected-boundary-arc source target. -/
def of_noncrossingSelectedBoundaryArcSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h :
      source.toPlanarBoundaryAnnulusBoundaryData
        |>.PeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget) :
    CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data where
  regime := regime
  source := source
  boundaryData_eq_source := hboundary
  mappedCutAvoidingFaceRoute :=
    source.mappedCutAvoidingFaceRouteTarget_of_noncrossingSelectedBoundaryArcSourceTarget h

end CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs

/--
Repaired annulus index for the closed-walk cut-avoiding face-route path,
aligned with the repaired previous-boundary annulus data.
-/
structure RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) where
  regime :
    MinimalCounterexamplePeeledCollarRegime G
      (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
      data.inducedBoundaryGraph
  source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb
  boundaryData_eq_source :
    data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
      source.toPlanarBoundaryAnnulusBoundaryData
  mappedCutAvoidingFaceRoute :
    source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget

namespace RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs

/-- Repaired route inputs supply mapped-cut-deleted shared-endpoint connectivity. -/
theorem mappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs :
      RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget := by
  have hmappedSource :
      inputs.source.toPlanarBoundaryAnnulusBoundaryData
        |>.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget :=
    inputs.source
      |>.mappedCutAvoidingSharedEndpointConnectivityTarget_of_mappedCutAvoidingFaceRouteTarget
        inputs.mappedCutAvoidingFaceRoute
  change data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData
    |>.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget
  rw [inputs.boundaryData_eq_source]
  exact hmappedSource

/-- Repaired route inputs supply the older mapped-connectivity route index. -/
def toMappedCutAvoidingSharedEndpointConnectedRouteInputs
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs :
      RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    MinimalCounterexampleOffCarrierMappedCutAvoidingSharedEndpointConnectedPeeledCollarRouteInputs
      G data.ambientBoundaryEdgeSet where
  regime := inputs.regime
  offCarrierMappedCutAvoidingSharedEndpointConnectivities :=
    inputs.mappedCutAvoidingSharedEndpointConnectivityTarget

/-- Repaired route inputs supply cyclic five-edge-connectivity. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs :
      RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  inputs.toMappedCutAvoidingSharedEndpointConnectedRouteInputs
    |>.cyclicallyFiveEdgeConnected

/-- Repaired route inputs supply the no-cyclic-two-cut consequence. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs :
      RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph :=
  inputs.toMappedCutAvoidingSharedEndpointConnectedRouteInputs
    |>.closedCollarForbidsCyclicTwoCut

/-- Repaired route inputs supply the S4 winding salvage. -/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs :
      RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  inputs.toMappedCutAvoidingSharedEndpointConnectedRouteInputs
    |>.closedCollarWindingFreedomEscape_not_simplyRealizable

/-- Build repaired route inputs from the older face-placement noncrossing target. -/
def of_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
    RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data where
  regime := regime
  source := source
  boundaryData_eq_source := hboundary
  mappedCutAvoidingFaceRoute :=
    source.mappedCutAvoidingFaceRouteTarget_of_facePlacementNoncrossingTarget h

/-- Build repaired route inputs from chosen source-side attachment-face data. -/
def of_attachmentFaceSourceDataTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (h :
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
        source.toPlanarBoundaryAnnulusBoundaryData) :
    RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data where
  regime := regime
  source := source
  boundaryData_eq_source := hboundary
  mappedCutAvoidingFaceRoute :=
    source.mappedCutAvoidingFaceRouteTarget_of_attachmentFaceSourceDataTarget h

/-- Build repaired route inputs from the noncrossing face-source target. -/
def of_noncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (h :
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        source.toPlanarBoundaryAnnulusBoundaryData) :
    RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data where
  regime := regime
  source := source
  boundaryData_eq_source := hboundary
  mappedCutAvoidingFaceRoute :=
    source.mappedCutAvoidingFaceRouteTarget_of_noncrossingFaceSourceTarget h

/-- Build repaired route inputs from the selected-boundary-arc source target. -/
def of_noncrossingSelectedBoundaryArcSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (h :
      source.toPlanarBoundaryAnnulusBoundaryData
        |>.PeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget) :
    RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data where
  regime := regime
  source := source
  boundaryData_eq_source := hboundary
  mappedCutAvoidingFaceRoute :=
    source.mappedCutAvoidingFaceRouteTarget_of_noncrossingSelectedBoundaryArcSourceTarget h

end RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs

end Mettapedia.GraphTheory.FourColor
