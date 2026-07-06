import Mettapedia.GraphTheory.FourColor.PeeledCollarClosedWalkCutAvoidingFaceRoute

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
The closed-walk face-placement noncrossing target is stronger than the
cut-avoiding face-route target.  The chosen noncrossing face gives mapped-cut
avoidance, while the closed-walk source's selected-boundary arc geometry gives
the face-local boundary walk.
-/
theorem mappedCutAvoidingFaceRouteTarget_of_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
    source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget := by
  intro cut root a b hrootA hrootB
  rcases h cut with ⟨side, hside, hroute⟩
  rcases hroute root a b hrootA hrootB with
    ⟨f, hplacement, hnoncross⟩
  rcases hplacement with
    ⟨e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb⟩
  refine
    ⟨f, e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb, ?_, ?_⟩
  · exact source.toPlanarBoundarySelectedBoundaryArcGeometry.boundaryComponentWalkOnFace f
  · exact
      source.toPlanarBoundaryAnnulusBoundaryData
        |>.mappedCutAvoidanceOnFace_of_faceSelectedBoundaryEdgesDoNotCrossSide
          hside hnoncross

/--
Chosen source-side attachment-face data are stronger than the cut-avoiding
face-route target.
-/
theorem mappedCutAvoidingFaceRouteTarget_of_attachmentFaceSourceDataTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h :
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
        source.toPlanarBoundaryAnnulusBoundaryData) :
    source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget :=
  source.mappedCutAvoidingFaceRouteTarget_of_facePlacementNoncrossingTarget
    ((source.facePlacementNoncrossingTarget_iff_attachmentFaceSourceDataTarget).2 h)

/--
The existing noncrossing face-source target supplies the cut-avoiding
face-route target.
-/
theorem mappedCutAvoidingFaceRouteTarget_of_noncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h :
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        source.toPlanarBoundaryAnnulusBoundaryData) :
    source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget :=
  source.mappedCutAvoidingFaceRouteTarget_of_facePlacementNoncrossingTarget
    (source.facePlacementNoncrossingTarget_of_noncrossingFaceSourceTarget h)

/--
The selected-boundary-arc source target supplies the cut-avoiding face-route
target after forgetting the explicit selected-arc witness.
-/
theorem mappedCutAvoidingFaceRouteTarget_of_noncrossingSelectedBoundaryArcSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h :
      source.toPlanarBoundaryAnnulusBoundaryData
        |>.PeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget) :
    source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget :=
  source.mappedCutAvoidingFaceRouteTarget_of_facePlacementNoncrossingTarget
    (source.facePlacementNoncrossingTarget_of_noncrossingSelectedBoundaryArcSourceTarget h)

end PlanarBoundaryClosedWalkAnnulusBoundarySource

end Mettapedia.GraphTheory.FourColor
