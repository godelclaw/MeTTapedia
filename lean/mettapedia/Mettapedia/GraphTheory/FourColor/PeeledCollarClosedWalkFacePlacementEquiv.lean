import Mettapedia.GraphTheory.FourColor.PeeledCollarClosedWalkFacePlacementTarget

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
The closed-walk face-placement target is equivalent to the existing
noncrossing face-source target on the same extracted annulus boundary split.
-/
theorem facePlacementNoncrossingTarget_iff_noncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    source.OffCarrierAttachmentFacePlacementNoncrossingTarget ↔
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        source.toPlanarBoundaryAnnulusBoundaryData :=
  source.facePlacementNoncrossingTarget_iff_attachmentFaceSourceDataTarget.trans
    (PlanarBoundaryAnnulusBoundaryData.attachmentFaceSourceDataTarget_iff_noncrossingFaceSourceTarget
      (data := source.toPlanarBoundaryAnnulusBoundaryData))

/-- The existing noncrossing face-source target supplies the closed-walk face-placement target. -/
theorem facePlacementNoncrossingTarget_of_noncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h :
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        source.toPlanarBoundaryAnnulusBoundaryData) :
    source.OffCarrierAttachmentFacePlacementNoncrossingTarget :=
  (source.facePlacementNoncrossingTarget_iff_noncrossingFaceSourceTarget).2 h

/-- The closed-walk face-placement target supplies the existing noncrossing face-source target. -/
theorem noncrossingFaceSourceTarget_of_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
    PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
      source.toPlanarBoundaryAnnulusBoundaryData :=
  (source.facePlacementNoncrossingTarget_iff_noncrossingFaceSourceTarget).1 h

/--
Selected-boundary-arc source data are stronger than the closed-walk
face-placement target; the selected arc proof is forgotten here.
-/
theorem facePlacementNoncrossingTarget_of_noncrossingSelectedBoundaryArcSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h :
      source.toPlanarBoundaryAnnulusBoundaryData
        |>.PeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget) :
    source.OffCarrierAttachmentFacePlacementNoncrossingTarget :=
  (source.facePlacementNoncrossingTarget_iff_attachmentFaceSourceDataTarget).2
    (source.toPlanarBoundaryAnnulusBoundaryData
      |>.attachmentFaceSourceDataTarget_of_noncrossingSelectedBoundaryArcSourceTarget h)

end PlanarBoundaryClosedWalkAnnulusBoundarySource

namespace PlanarBoundaryAnnulusCollarGeometry

/--
Canonical closed-walk-source cyclic five-edge-connectivity from the existing
noncrossing face-source target, routed through the named face-placement
target.
-/
theorem cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_noncrossingFaceSourceTarget
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
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  data.cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_facePlacementNoncrossingTarget
    regime source hboundary
    (source.facePlacementNoncrossingTarget_of_noncrossingFaceSourceTarget h)

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Repaired closed-walk-source cyclic five-edge-connectivity from the existing
noncrossing face-source target, routed through the named face-placement
target.
-/
theorem cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_noncrossingFaceSourceTarget
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
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  data.cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_facePlacementNoncrossingTarget
    regime source hboundary
    (source.facePlacementNoncrossingTarget_of_noncrossingFaceSourceTarget h)

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

end Mettapedia.GraphTheory.FourColor
