import Mettapedia.GraphTheory.FourColor.PeeledCollarAttachmentNoncrossingFaceSource

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryAnnulusCollarGeometry

/--
Transport a closed-walk annulus source face-source target across a matching
annulus boundary split, then insert the source's selected-boundary arc
geometry to obtain the canonical selected-boundary-arc source target.
-/
theorem
    attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_closedWalkAnnulusBoundarySource_faceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h :
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        source.toPlanarBoundaryAnnulusBoundaryData) :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
      data := by
  have hFace :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        data := by
    simpa [PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget,
      hboundary] using h
  exact
    planarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget_of_selectedBoundaryArcGeometry_of_faceSourceTarget
      source.toPlanarBoundarySelectedBoundaryArcGeometry hFace

/--
Canonical annulus S4 salvage from an aligned closed-walk source face-source
target.
-/
theorem
    closedCollarWindingFreedomEscape_not_simplyRealizable_of_closedWalkAnnulusBoundarySource_faceSourceTarget
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
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_noncrossingSelectedBoundaryArcSourceTarget
    regime
    (data.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_closedWalkAnnulusBoundarySource_faceSourceTarget
      source hboundary h)

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Transport a closed-walk annulus source face-source target across a matching
annulus boundary split, then insert the source's selected-boundary arc
geometry to obtain the repaired selected-boundary-arc source target.
-/
theorem
    attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_closedWalkAnnulusBoundarySource_faceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (h :
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        source.toPlanarBoundaryAnnulusBoundaryData) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
      data := by
  have hFace :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        data := by
    simpa [
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget,
      PlanarBoundaryAnnulusCollarGeometry.boundaryData, hboundary] using h
  exact
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget_of_selectedBoundaryArcGeometry_of_faceSourceTarget
      source.toPlanarBoundarySelectedBoundaryArcGeometry hFace

/--
Repaired annulus S4 salvage from an aligned closed-walk source face-source
target.
-/
theorem
    closedCollarWindingFreedomEscape_not_simplyRealizable_of_closedWalkAnnulusBoundarySource_faceSourceTarget
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
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_noncrossingSelectedBoundaryArcSourceTarget
    regime
    (data.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_closedWalkAnnulusBoundarySource_faceSourceTarget
      source hboundary h)

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
End-to-end S4 salvage target using canonical annulus geometry aligned with a
closed-walk annulus source.  The selected-boundary arc geometry is supplied by
the source; the remaining source obligation is the face-source target on the
same boundary split.
-/
def
    Section92Step4CanonicalAnnulusClosedWalkFaceSourceRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData →
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        source.toPlanarBoundaryAnnulusBoundaryData →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim canonical-annulus closed-walk-source face-source S4 salvage statement. -/
theorem
    section92Step4CanonicalAnnulusClosedWalkFaceSourceRegimeDischargedS4SalvageTarget :
    Section92Step4CanonicalAnnulusClosedWalkFaceSourceRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime source hboundary h
  exact
    data.closedCollarWindingFreedomEscape_not_simplyRealizable_of_closedWalkAnnulusBoundarySource_faceSourceTarget
      regime source hboundary h

/--
End-to-end S4 salvage target using repaired annulus geometry aligned with a
closed-walk annulus source.  The selected-boundary arc geometry is supplied by
the source; the remaining source obligation is the face-source target on the
same boundary split.
-/
def
    Section92Step4RepairedAnnulusClosedWalkFaceSourceRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData →
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        source.toPlanarBoundaryAnnulusBoundaryData →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim repaired-annulus closed-walk-source face-source S4 salvage statement. -/
theorem
    section92Step4RepairedAnnulusClosedWalkFaceSourceRegimeDischargedS4SalvageTarget :
    Section92Step4RepairedAnnulusClosedWalkFaceSourceRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime source hboundary h
  exact
    data.closedCollarWindingFreedomEscape_not_simplyRealizable_of_closedWalkAnnulusBoundarySource_faceSourceTarget
      regime source hboundary h

end Mettapedia.GraphTheory.FourColor
