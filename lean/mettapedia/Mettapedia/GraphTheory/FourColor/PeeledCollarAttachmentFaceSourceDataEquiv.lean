import Mettapedia.GraphTheory.FourColor.PeeledCollarAttachmentFaceSourceDataCompatibility

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryAnnulusBoundaryData

/--
The older per-cut noncrossing face-source target and the chosen source-side
data target are equivalent.  The chosen data form only separates the placement
family from the noncrossing proof for the same recorded side.
-/
theorem cutAttachmentFaceSourceDataTarget_iff_noncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    {cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)} :
    (∃ source : data.CutOffCarrierAttachmentFaceSourceData cut,
      source.Noncrossing) ↔
      data.CutOffCarrierAttachmentNoncrossingFaceSourceTarget cut := by
  constructor
  · rintro ⟨source, hnoncross⟩
    exact source.toCutOffCarrierAttachmentNoncrossingFaceSourceTarget hnoncross
  · intro h
    rcases h with ⟨side, hside, hroute⟩
    refine
      ⟨{ side := side
         side_comp_cut := hside
         placement := ?_ }, ?_⟩
    · intro root a b hrootA hrootB
      rcases hroute root a b hrootA hrootB with
        ⟨f, e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb, _⟩
      exact ⟨f, e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb⟩
    · intro root a b hrootA hrootB
      rcases hroute root a b hrootA hrootB with
        ⟨f, e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb, hnoncross⟩
      exact
        ⟨f, ⟨e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb⟩,
          hnoncross⟩

/--
All-cuts equivalence between the older noncrossing face-source target and the
chosen source-side data target.
-/
theorem attachmentFaceSourceDataTarget_iff_noncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb} :
    data.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget ↔
      data.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget := by
  constructor
  · exact data.attachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceDataTarget
  · intro h cut
    exact
      (data.cutAttachmentFaceSourceDataTarget_iff_noncrossingFaceSourceTarget).2
        (h cut)

/-- The older all-cuts noncrossing face-source target supplies chosen source-side data. -/
theorem attachmentFaceSourceDataTarget_of_noncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget) :
    data.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget :=
  (data.attachmentFaceSourceDataTarget_iff_noncrossingFaceSourceTarget).2 h

end PlanarBoundaryAnnulusBoundaryData

/-- Canonical annulus equivalence with the older noncrossing face-source target. -/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceDataTarget_iff_noncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb} :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
        data ↔
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        data :=
  data.attachmentFaceSourceDataTarget_iff_noncrossingFaceSourceTarget

/-- Canonical annulus conversion from the older noncrossing face-source target. -/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceDataTarget_of_noncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        data) :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
      data :=
  data.attachmentFaceSourceDataTarget_of_noncrossingFaceSourceTarget h

/-- Repaired annulus equivalence with the older noncrossing face-source target. -/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceDataTarget_iff_noncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb} :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
        data ↔
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        data :=
  data.attachmentFaceSourceDataTarget_iff_noncrossingFaceSourceTarget

/-- Repaired annulus conversion from the older noncrossing face-source target. -/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceDataTarget_of_noncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        data) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
      data :=
  data.attachmentFaceSourceDataTarget_of_noncrossingFaceSourceTarget h

end Mettapedia.GraphTheory.FourColor
