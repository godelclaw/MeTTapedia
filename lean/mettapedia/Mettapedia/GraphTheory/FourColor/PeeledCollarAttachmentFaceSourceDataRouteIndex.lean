import Mettapedia.GraphTheory.FourColor.PeeledCollarAttachmentFaceSourceData

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

variable {V : Type} [DecidableEq V]

/--
Reusable index for the canonical annulus route when selected-boundary arc
geometry is supplied directly and the remaining planar-normal-form obligation
is chosen source-side attachment-face data.
-/
structure CanonicalAnnulusAttachmentFaceSourceDataRouteInputs
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) where
  regime :
    MinimalCounterexamplePeeledCollarRegime G
      (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
      data.inducedBoundaryGraph
  selectedBoundaryArcOnFace :
    ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f
  attachmentFaceSourceData :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
      data

namespace CanonicalAnnulusAttachmentFaceSourceDataRouteInputs

/-- The canonical selected-arc route index supplies cyclic five-edge-connectivity. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs : CanonicalAnnulusAttachmentFaceSourceDataRouteInputs data) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs.cyclicallyFiveEdgeConnected_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceDataTarget
    inputs.regime inputs.selectedBoundaryArcOnFace
    inputs.attachmentFaceSourceData

/-- The canonical selected-arc route index supplies the S4 winding salvage. -/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs : CanonicalAnnulusAttachmentFaceSourceDataRouteInputs data) :
    ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
      data.inducedBoundaryGraph :=
  MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceDataTarget
    inputs.regime inputs.selectedBoundaryArcOnFace
    inputs.attachmentFaceSourceData

end CanonicalAnnulusAttachmentFaceSourceDataRouteInputs

/--
Reusable index for the repaired annulus route when selected-boundary arc
geometry is supplied directly and the remaining planar-normal-form obligation
is chosen source-side attachment-face data.
-/
structure RepairedAnnulusAttachmentFaceSourceDataRouteInputs
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) where
  regime :
    MinimalCounterexamplePeeledCollarRegime G
      (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
      data.inducedBoundaryGraph
  selectedBoundaryArcOnFace :
    ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f
  attachmentFaceSourceData :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
      data

namespace RepairedAnnulusAttachmentFaceSourceDataRouteInputs

/-- The repaired selected-arc route index supplies cyclic five-edge-connectivity. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs : RepairedAnnulusAttachmentFaceSourceDataRouteInputs data) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs.cyclicallyFiveEdgeConnected_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceDataTarget
    inputs.regime inputs.selectedBoundaryArcOnFace
    inputs.attachmentFaceSourceData

/-- The repaired selected-arc route index supplies the S4 winding salvage. -/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs : RepairedAnnulusAttachmentFaceSourceDataRouteInputs data) :
    ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
      data.inducedBoundaryGraph :=
  MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceDataTarget
    inputs.regime inputs.selectedBoundaryArcOnFace
    inputs.attachmentFaceSourceData

end RepairedAnnulusAttachmentFaceSourceDataRouteInputs

/--
Reusable index for the canonical closed-walk route.  The closed-walk source
supplies selected-boundary arc geometry; the listed remaining obligation is
chosen source-side attachment-face data on the extracted boundary data.
-/
structure CanonicalAnnulusClosedWalkAttachmentFaceSourceDataRouteInputs
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) where
  regime :
    MinimalCounterexamplePeeledCollarRegime G
      (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
      data.inducedBoundaryGraph
  source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb
  boundaryData_eq_source :
    data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData
  attachmentFaceSourceData :
    PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
      source.toPlanarBoundaryAnnulusBoundaryData

namespace CanonicalAnnulusClosedWalkAttachmentFaceSourceDataRouteInputs

/-- The canonical closed-walk route index supplies cyclic five-edge-connectivity. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs :
      CanonicalAnnulusClosedWalkAttachmentFaceSourceDataRouteInputs data) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  data.cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceDataTarget
    inputs.regime inputs.source inputs.boundaryData_eq_source
    inputs.attachmentFaceSourceData

/-- The canonical closed-walk route index supplies the S4 winding salvage. -/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs :
      CanonicalAnnulusClosedWalkAttachmentFaceSourceDataRouteInputs data) :
    ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
      data.inducedBoundaryGraph :=
  data.closedCollarWindingFreedomEscape_not_simplyRealizable_throughConnectivity_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceDataTarget
    inputs.regime inputs.source inputs.boundaryData_eq_source
    inputs.attachmentFaceSourceData

end CanonicalAnnulusClosedWalkAttachmentFaceSourceDataRouteInputs

/--
Reusable index for the repaired closed-walk route.  The closed-walk source
supplies selected-boundary arc geometry; the listed remaining obligation is
chosen source-side attachment-face data on the extracted boundary data.
-/
structure RepairedAnnulusClosedWalkAttachmentFaceSourceDataRouteInputs
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
  attachmentFaceSourceData :
    PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
      source.toPlanarBoundaryAnnulusBoundaryData

namespace RepairedAnnulusClosedWalkAttachmentFaceSourceDataRouteInputs

/-- The repaired closed-walk route index supplies cyclic five-edge-connectivity. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs :
      RepairedAnnulusClosedWalkAttachmentFaceSourceDataRouteInputs data) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  data.cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceDataTarget
    inputs.regime inputs.source inputs.boundaryData_eq_source
    inputs.attachmentFaceSourceData

/-- The repaired closed-walk route index supplies the S4 winding salvage. -/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs :
      RepairedAnnulusClosedWalkAttachmentFaceSourceDataRouteInputs data) :
    ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
      data.inducedBoundaryGraph :=
  data.closedCollarWindingFreedomEscape_not_simplyRealizable_throughConnectivity_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceDataTarget
    inputs.regime inputs.source inputs.boundaryData_eq_source
    inputs.attachmentFaceSourceData

end RepairedAnnulusClosedWalkAttachmentFaceSourceDataRouteInputs

end Mettapedia.GraphTheory.FourColor
