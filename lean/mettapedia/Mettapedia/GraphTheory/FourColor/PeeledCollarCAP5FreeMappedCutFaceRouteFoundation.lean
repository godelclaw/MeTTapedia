import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeAttachmentFaceSplitSourceIndex

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Mapped-cut face-route foundation index for the CAP5-free peeled-collar route.

The face-source formulation and the attachment-face split-source formulation
are equivalent for selected boundary edges: noncrossing depends only on the
side values at selected-boundary endpoints, and any two sides compatible with
the same carrier cut agree on those endpoints.
-/

/--
Side-crossing of one edge is invariant under pointwise agreement of the two
side predicates on that edge's endpoints.
-/
theorem edgeCrossesVertexSide_congr_on_edge
    {V : Type} {G : SimpleGraph V}
    {side₁ side₂ : V → Prop} {e : G.edgeSet}
    (hside : ∀ v : V, v ∈ (e : Sym2 V) → (side₁ v ↔ side₂ v)) :
    EdgeCrossesVertexSide G side₁ e ↔
      EdgeCrossesVertexSide G side₂ e := by
  constructor
  · rintro ⟨u, v, hu, hv, hsu, hsv⟩
    exact
      ⟨u, v, hu, hv, (hside u hu).1 hsu,
        fun hsv₂ => hsv ((hside v hv).2 hsv₂)⟩
  · rintro ⟨u, v, hu, hv, hsu, hsv⟩
    exact
      ⟨u, v, hu, hv, (hside u hu).2 hsu,
        fun hsv₁ => hsv ((hside v hv).1 hsv₁)⟩

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryAnnulusBoundaryData

/--
Face-local noncrossing transfers between any two ambient sides compatible
with the same carrier cut, since selected boundary edges have endpoints in
the induced boundary carrier.
-/
theorem faceSelectedBoundaryEdgesDoNotCrossSide_of_compatible_cut_side
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb)
    {cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)}
    {side₁ side₂ : V → Prop}
    (hside₁ :
      ∀ w : BoundaryEdgeSetEndpointVertex
          (G := G) data.ambientBoundaryEdgeSet,
        side₁ (data.inducedBoundaryEmbedding w) ↔ cut.side w)
    (hside₂ :
      ∀ w : BoundaryEdgeSetEndpointVertex
          (G := G) data.ambientBoundaryEdgeSet,
        side₂ (data.inducedBoundaryEmbedding w) ↔ cut.side w)
    {f : AmbientFace emb.faces}
    (hnoncross : data.FaceSelectedBoundaryEdgesDoNotCrossSide side₁ f) :
    data.FaceSelectedBoundaryEdgesDoNotCrossSide side₂ f := by
  intro g hg hcross₂
  have hgBoundary : g.1 ∈ data.ambientBoundaryEdgeSet := by
    rw [data.ambientBoundaryEdgeSet_eq_selectedBoundarySupport]
    exact g.2
  have hagree :
      ∀ v : V, v ∈ (g.1 : Sym2 V) → (side₁ v ↔ side₂ v) := by
    intro v hv
    let w : BoundaryEdgeSetEndpointVertex
        (G := G) data.ambientBoundaryEdgeSet :=
      boundaryEdgeSetEndpointVertexOfMemEdgeEndpoint
        (G := G) (edges := data.ambientBoundaryEdgeSet) hgBoundary hv
    have h₁ : side₁ v ↔ cut.side w := by
      simpa [w] using hside₁ w
    have h₂ : side₂ v ↔ cut.side w := by
      simpa [w] using hside₂ w
    exact h₁.trans h₂.symm
  exact hnoncross g hg
    ((edgeCrossesVertexSide_congr_on_edge
      (G := G) (side₁ := side₁) (side₂ := side₂)
      (e := g.1) hagree).2 hcross₂)

/--
Per-cut face-source data forgets to the attachment-face placement target.
-/
theorem cutOffCarrierAttachmentFaceSourceTarget_of_noncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    {cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)}
    (h : data.CutOffCarrierAttachmentNoncrossingFaceSourceTarget cut) :
    data.CutOffCarrierAttachmentFaceSourceTarget cut := by
  rcases h with ⟨side, hside, hroute⟩
  refine ⟨side, hside, ?_⟩
  intro root a b hrootA hrootB
  rcases hroute root a b hrootA hrootB with
    ⟨f, e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb, _⟩
  exact ⟨f, e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb⟩

/--
Per-cut face-source data supplies the universal noncrossing-upgrade target.
-/
theorem cutOffCarrierAttachmentFaceNoncrossingUpgradeTarget_of_noncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    {cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)}
    (h : data.CutOffCarrierAttachmentNoncrossingFaceSourceTarget cut) :
    data.CutOffCarrierAttachmentFaceNoncrossingUpgradeTarget cut := by
  rcases h with ⟨sourceSide, hsourceSide, hroute⟩
  intro side hside _hplacements root a b hrootA hrootB
  rcases hroute root a b hrootA hrootB with
    ⟨f, e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb, hnoncross⟩
  exact
    ⟨f, ⟨e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb⟩,
      data.faceSelectedBoundaryEdgesDoNotCrossSide_of_compatible_cut_side
        hsourceSide hside hnoncross⟩

/--
All-cuts face-source data forgets to the attachment-face placement target.
-/
theorem attachmentFaceSourceTarget_of_noncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget) :
    data.PeeledCollarOffCarrierAttachmentFaceSourceTarget := by
  intro cut
  exact data.cutOffCarrierAttachmentFaceSourceTarget_of_noncrossingFaceSourceTarget
    (h cut)

/--
All-cuts face-source data supplies the universal noncrossing-upgrade target.
-/
theorem attachmentFaceNoncrossingUpgradeTarget_of_noncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget) :
    data.PeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget := by
  intro cut
  exact
    data.cutOffCarrierAttachmentFaceNoncrossingUpgradeTarget_of_noncrossingFaceSourceTarget
      (h cut)

/--
The split attachment-face source target is equivalent to the face-source
target.
-/
theorem attachmentFaceSplitSourceTarget_iff_noncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) :
    (data.PeeledCollarOffCarrierAttachmentFaceSourceTarget ∧
        data.PeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget) ↔
      data.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget := by
  constructor
  · intro h
    exact
      data.attachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
        h.1 h.2
  · intro h
    exact
      ⟨data.attachmentFaceSourceTarget_of_noncrossingFaceSourceTarget h,
        data.attachmentFaceNoncrossingUpgradeTarget_of_noncrossingFaceSourceTarget h⟩

end PlanarBoundaryAnnulusBoundaryData

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
The noncrossing face-source foundation target supplies the attachment-face
split-source foundation target.
-/
theorem regimeAttachmentFaceSplitSourceFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeNoncrossingFaceSourceFoundationTarget) :
    source.RegimeAttachmentFaceSplitSourceFoundationTarget :=
  (source.toPlanarBoundaryAnnulusBoundaryData
    |>.attachmentFaceSplitSourceTarget_iff_noncrossingFaceSourceTarget).2 h

/--
The split-source target and the noncrossing face-source target are equivalent
for closed-walk annulus boundary sources.
-/
theorem regimeAttachmentFaceSplitSourceFoundationTarget_iff_regimeNoncrossingFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    source.RegimeAttachmentFaceSplitSourceFoundationTarget ↔
      source.RegimeNoncrossingFaceSourceFoundationTarget :=
  ⟨source.regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSplitSourceFoundationTarget,
    source.regimeAttachmentFaceSplitSourceFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget⟩

end PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Closed-walk CAP5-free mapped-cut face-route foundation target.  This is the
face-local formulation of the remaining planar-normal-form obligation.
-/
def CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget

/--
The face-source foundation target supplies the mapped-cut face-route target.
-/
theorem cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_faceSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.mappedCutAvoidingFaceRouteTarget_of_regimeNoncrossingFaceSourceFoundationTarget
      (hfoundation source regime)

/--
The mapped-cut face-route foundation target supplies the face-source target.
-/
theorem cap5FreeClosedWalkFaceSourceFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.regimeNoncrossingFaceSourceFoundationTarget_of_mappedCutAvoidingFaceRouteTarget
      (hfoundation source regime)

/--
The mapped-cut face-route target and the face-source target are equivalent at
the CAP5-free closed-walk foundation level.
-/
theorem
    cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_iff_faceSourceFoundationTarget :
    CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget ↔
      CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget :=
  ⟨cap5FreeClosedWalkFaceSourceFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget,
    cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_faceSourceFoundationTarget⟩

/--
The face-source foundation target supplies the attachment-face split-source
target.
-/
theorem cap5FreeClosedWalkAttachmentFaceSplitSourceFoundationTarget_of_faceSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.regimeAttachmentFaceSplitSourceFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
      (hfoundation source regime)

/--
The attachment-face split-source target and the face-source target are
equivalent at the CAP5-free closed-walk foundation level.
-/
theorem
    cap5FreeClosedWalkAttachmentFaceSplitSourceFoundationTarget_iff_faceSourceFoundationTarget :
    CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget ↔
      CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget :=
  ⟨cap5FreeClosedWalkFaceSourceFoundationTarget_of_attachmentFaceSplitSourceFoundationTarget,
    cap5FreeClosedWalkAttachmentFaceSplitSourceFoundationTarget_of_faceSourceFoundationTarget⟩

/--
The mapped-cut face-route foundation target supplies the attachment-face
split-source target.
-/
theorem
    cap5FreeClosedWalkAttachmentFaceSplitSourceFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget :=
  cap5FreeClosedWalkAttachmentFaceSplitSourceFoundationTarget_of_faceSourceFoundationTarget
    (cap5FreeClosedWalkFaceSourceFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
      hfoundation)

/--
The mapped-cut face-route target, face-source target, and attachment-face
split-source target expose the same closed-walk CAP5-free foundation
obligation.
-/
theorem
    cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_iff_attachmentFaceSplitSourceFoundationTarget :
    CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget ↔
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget :=
  ⟨cap5FreeClosedWalkAttachmentFaceSplitSourceFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget,
    fun h =>
      cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_faceSourceFoundationTarget
        (cap5FreeClosedWalkFaceSourceFoundationTarget_of_attachmentFaceSplitSourceFoundationTarget
          h)⟩

end Mettapedia.GraphTheory.FourColor
