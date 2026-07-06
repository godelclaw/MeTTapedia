import Mettapedia.GraphTheory.FourColor.PeeledCollarAttachmentFaceSourceDataRouteIndex

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryAnnulusBoundaryData

/--
The older per-cut attachment-face noncrossing route target is stronger than
chosen source-side attachment-face data: the route target also carries a
face-walk witness, which the source-data interface does not need.
-/
theorem cutAttachmentFaceSourceDataTarget_of_attachmentFaceNoncrossingRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    {cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)}
    (h : data.CutOffCarrierAttachmentFaceNoncrossingRouteTarget cut) :
    ∃ source : data.CutOffCarrierAttachmentFaceSourceData cut,
      source.Noncrossing := by
  rcases h with ⟨side, hside, hroute⟩
  refine
    ⟨{ side := side
       side_comp_cut := hside
       placement := ?_ }, ?_⟩
  · intro root a b hrootA hrootB
    rcases hroute root a b hrootA hrootB with
      ⟨f, e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb, _, _⟩
    exact ⟨f, e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb⟩
  · intro root a b hrootA hrootB
    rcases hroute root a b hrootA hrootB with
      ⟨f, e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb, _, hnoncross⟩
    exact
      ⟨f, ⟨e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb⟩,
        hnoncross⟩

/--
The selected-boundary arc source target is also stronger than chosen
source-side attachment-face data: the source-data interface keeps the side,
face placement, and noncrossing fact, while forgetting the selected arc proof.
-/
theorem cutAttachmentFaceSourceDataTarget_of_noncrossingSelectedBoundaryArcSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    {cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)}
    (h :
      data.CutOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
        cut) :
    ∃ source : data.CutOffCarrierAttachmentFaceSourceData cut,
      source.Noncrossing :=
  data.cutAttachmentFaceSourceDataTarget_of_attachmentFaceNoncrossingRouteTarget
    (data.cutAttachmentFaceNoncrossingRouteTarget_of_noncrossingSelectedBoundaryArcSourceTarget
      h)

/-- All-cuts compatibility from the older noncrossing route target. -/
theorem attachmentFaceSourceDataTarget_of_attachmentFaceNoncrossingRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarOffCarrierAttachmentFaceNoncrossingRouteTarget) :
    data.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget := by
  intro cut
  exact
    data.cutAttachmentFaceSourceDataTarget_of_attachmentFaceNoncrossingRouteTarget
      (h cut)

/-- All-cuts compatibility from the selected-boundary arc source target. -/
theorem attachmentFaceSourceDataTarget_of_noncrossingSelectedBoundaryArcSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h :
      data.PeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget) :
    data.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget := by
  intro cut
  exact
    data.cutAttachmentFaceSourceDataTarget_of_noncrossingSelectedBoundaryArcSourceTarget
      (h cut)

end PlanarBoundaryAnnulusBoundaryData

/-- Canonical annulus compatibility from the older noncrossing route target. -/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceDataTarget_of_attachmentFaceNoncrossingRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceNoncrossingRouteTarget
        data) :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
      data :=
  data.attachmentFaceSourceDataTarget_of_attachmentFaceNoncrossingRouteTarget h

/-- Canonical annulus compatibility from the selected-boundary arc source target. -/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceDataTarget_of_noncrossingSelectedBoundaryArcSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
        data) :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
      data :=
  data.attachmentFaceSourceDataTarget_of_noncrossingSelectedBoundaryArcSourceTarget h

/-- Repaired annulus compatibility from the older noncrossing route target. -/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceDataTarget_of_attachmentFaceNoncrossingRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceNoncrossingRouteTarget
        data) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
      data :=
  data.attachmentFaceSourceDataTarget_of_attachmentFaceNoncrossingRouteTarget h

/-- Repaired annulus compatibility from the selected-boundary arc source target. -/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceDataTarget_of_noncrossingSelectedBoundaryArcSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
        data) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
      data :=
  data.attachmentFaceSourceDataTarget_of_noncrossingSelectedBoundaryArcSourceTarget h

end Mettapedia.GraphTheory.FourColor
