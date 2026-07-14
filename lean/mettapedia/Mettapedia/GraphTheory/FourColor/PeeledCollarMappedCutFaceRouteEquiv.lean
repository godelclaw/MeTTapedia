import Mettapedia.GraphTheory.FourColor.PeeledCollarRegimeFacePlacementFoundationSourceData

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryAnnulusBoundaryData

/--
Canonical ambient extension of a cut side on the induced annulus-boundary
carrier: an ambient vertex is on the side exactly when it is the image of a
carrier vertex on that side.
-/
def embeddedCutSide
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb)
    (cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet))
    (v : V) : Prop :=
  ∃ w : BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet,
    data.inducedBoundaryEmbedding w = v ∧ cut.side w

/-- The canonical embedded side agrees with the carrier cut side. -/
theorem embeddedCutSide_comp_inducedBoundaryEmbedding
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb)
    (cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet))
    (w : BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet) :
    data.embeddedCutSide cut (data.inducedBoundaryEmbedding w) ↔
      cut.side w := by
  constructor
  · rintro ⟨u, hu, hside⟩
    have huw : u = w := data.inducedBoundaryEmbedding.injective hu
    simpa [huw] using hside
  · intro hside
    exact ⟨w, rfl, hside⟩

/--
For selected annulus-boundary edges on a face, mapped-cut avoidance implies
face-local noncrossing for any ambient side compatible with the carrier cut.
-/
theorem faceSelectedBoundaryEdgesDoNotCrossSide_of_mappedCutAvoidanceOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb)
    {cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)}
    {side : V → Prop}
    (hside :
      ∀ w : BoundaryEdgeSetEndpointVertex
          (G := G) data.ambientBoundaryEdgeSet,
        side (data.inducedBoundaryEmbedding w) ↔ cut.side w)
    {f : AmbientFace emb.faces}
    (hAvoid :
      ∀ g : PlanarBoundaryEdgeVertex emb,
        g.1 ∈ emb.faceBoundary f.1 →
          (data.toBoundaryEdgeSetEdgeVertex g).1 ∉
            cut.edgeCut.map
              (boundaryEdgeSetInducedGraphEmbedding
                (G := G) data.ambientBoundaryEdgeSet).mapEdgeSet) :
    data.FaceSelectedBoundaryEdgesDoNotCrossSide side f := by
  intro g hg hcross
  have hgCarrier : g.1 ∈ data.ambientBoundaryEdgeSet := by
    rw [data.ambientBoundaryEdgeSet_eq_selectedBoundarySupport]
    exact g.2
  rcases
      exists_edge_preimage_boundaryEdgeSetInducedGraphEmbedding_of_mem_edges
        (G := G) (edges := data.ambientBoundaryEdgeSet) (e := g.1)
        hgCarrier with
    ⟨eH, hmap⟩
  have hcrossMapped :
      EdgeCrossesVertexSide G side
        ((boundaryEdgeSetInducedGraphEmbedding
          (G := G) data.ambientBoundaryEdgeSet).mapEdgeSet eH) := by
    simpa [hmap] using hcross
  have hcrossCarrier :
      EdgeCrossesVertexSide
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)
        cut.side eH :=
    EdgeCrossesVertexSide.comap_embedding
      (boundaryEdgeSetInducedGraphEmbedding
        (G := G) data.ambientBoundaryEdgeSet)
      hside hcrossMapped
  have hmem :
      (data.toBoundaryEdgeSetEdgeVertex g).1 ∈
        cut.edgeCut.map
          (boundaryEdgeSetInducedGraphEmbedding
            (G := G) data.ambientBoundaryEdgeSet).mapEdgeSet := by
    change g.1 ∈
      cut.edgeCut.map
        (boundaryEdgeSetInducedGraphEmbedding
          (G := G) data.ambientBoundaryEdgeSet).mapEdgeSet
    exact Finset.mem_map.2
      ⟨eH, (cut.hcut_eq eH).2 hcrossCarrier, hmap⟩
  exact hAvoid g hg hmem

/--
Face-local noncrossing is equivalent to mapped-cut avoidance for selected
annulus-boundary edges on a face.
-/
theorem faceSelectedBoundaryEdgesDoNotCrossSide_iff_mappedCutAvoidanceOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb)
    {cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)}
    {side : V → Prop}
    (hside :
      ∀ w : BoundaryEdgeSetEndpointVertex
          (G := G) data.ambientBoundaryEdgeSet,
        side (data.inducedBoundaryEmbedding w) ↔ cut.side w)
    {f : AmbientFace emb.faces} :
    data.FaceSelectedBoundaryEdgesDoNotCrossSide side f ↔
      ∀ g : PlanarBoundaryEdgeVertex emb,
        g.1 ∈ emb.faceBoundary f.1 →
          (data.toBoundaryEdgeSetEdgeVertex g).1 ∉
            cut.edgeCut.map
              (boundaryEdgeSetInducedGraphEmbedding
                (G := G) data.ambientBoundaryEdgeSet).mapEdgeSet :=
  ⟨data.mappedCutAvoidanceOnFace_of_faceSelectedBoundaryEdgesDoNotCrossSide
      hside,
    data.faceSelectedBoundaryEdgesDoNotCrossSide_of_mappedCutAvoidanceOnFace
      hside⟩

end PlanarBoundaryAnnulusBoundaryData

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
For one carrier cut, cut-avoiding face-route data supplies the closed-walk
face-placement noncrossing target by using the canonical embedded side.
-/
theorem cutFacePlacementNoncrossingTarget_of_mappedCutAvoidingFaceRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    {cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)}
    (h :
      source.CutOffCarrierAttachmentMappedCutAvoidingFaceRouteTarget cut) :
    source.CutOffCarrierAttachmentFacePlacementNoncrossingTarget cut := by
  let data := source.toPlanarBoundaryAnnulusBoundaryData
  refine
    ⟨data.embeddedCutSide cut,
      data.embeddedCutSide_comp_inducedBoundaryEmbedding cut, ?_⟩
  intro root a b hrootA hrootB
  rcases h root a b hrootA hrootB with
    ⟨f, e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb, _hwalk,
      hfaceAvoid⟩
  exact
    ⟨f, ⟨e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb⟩,
      data.faceSelectedBoundaryEdgesDoNotCrossSide_of_mappedCutAvoidanceOnFace
        (data.embeddedCutSide_comp_inducedBoundaryEmbedding cut)
        hfaceAvoid⟩

/--
Cut-avoiding face-route data supplies the closed-walk face-placement
noncrossing target for all small cyclic carrier cuts.
-/
theorem facePlacementNoncrossingTarget_of_mappedCutAvoidingFaceRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget) :
    source.OffCarrierAttachmentFacePlacementNoncrossingTarget := by
  intro cut
  exact source.cutFacePlacementNoncrossingTarget_of_mappedCutAvoidingFaceRouteTarget
    (h cut)

/--
The closed-walk cut-avoiding face-route target and the face-placement
noncrossing target are equivalent.
-/
theorem mappedCutAvoidingFaceRouteTarget_iff_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget ↔
      source.OffCarrierAttachmentFacePlacementNoncrossingTarget :=
  ⟨source.facePlacementNoncrossingTarget_of_mappedCutAvoidingFaceRouteTarget,
    source.mappedCutAvoidingFaceRouteTarget_of_facePlacementNoncrossingTarget⟩

/--
The named regime face-placement foundation target is equivalent to the
closed-walk cut-avoiding face-route target.
-/
theorem regimeFacePlacementFoundationTarget_iff_mappedCutAvoidingFaceRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    source.RegimeFacePlacementFoundationTarget ↔
      source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget :=
  (source.regimeFacePlacementFoundationTarget_iff_facePlacementNoncrossingTarget).trans
    source.mappedCutAvoidingFaceRouteTarget_iff_facePlacementNoncrossingTarget.symm

/--
The named source-data foundation target is equivalent to the closed-walk
cut-avoiding face-route target.
-/
theorem
    regimeAttachmentFaceSourceDataFoundationTarget_iff_mappedCutAvoidingFaceRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    source.RegimeAttachmentFaceSourceDataFoundationTarget ↔
      source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget :=
  (source.regimeFacePlacementFoundationTarget_iff_regimeAttachmentFaceSourceDataFoundationTarget).symm.trans
    source.regimeFacePlacementFoundationTarget_iff_mappedCutAvoidingFaceRouteTarget

/-- Cut-avoiding face routes supply the named source-data foundation target. -/
theorem regimeAttachmentFaceSourceDataFoundationTarget_of_mappedCutAvoidingFaceRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget) :
    source.RegimeAttachmentFaceSourceDataFoundationTarget :=
  (source.regimeAttachmentFaceSourceDataFoundationTarget_iff_mappedCutAvoidingFaceRouteTarget).2
    h

/--
Cut-avoiding face routes supply the named source-data foundation target and
all downstream source consequences.
-/
theorem routeIndexConsequences_of_mappedCutAvoidingFaceRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h : source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget) :
    source.RegimeAttachmentFaceSourceDataFoundationTarget ∧
      PeeledCollarSmallCyclicCutLiftsToAmbient G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      CyclicallyFiveEdgeConnected
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph := by
  have hsource :
      source.RegimeAttachmentFaceSourceDataFoundationTarget :=
    source.regimeAttachmentFaceSourceDataFoundationTarget_of_mappedCutAvoidingFaceRouteTarget
      h
  have hconsequences :=
    source.routeIndexConsequences_of_regimeAttachmentFaceSourceDataFoundationTarget
      regime hsource
  exact
    ⟨hsource, hconsequences.1, hconsequences.2.1,
      hconsequences.2.2.1, hconsequences.2.2.2⟩

end PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Source-level route index: the cut-avoiding face-route target is an equivalent
form of the source-data foundation target and supplies the downstream source
consequences.
-/
def Section92Step4ClosedWalkMappedCutFaceRouteEquivFoundationRouteIndexTarget :
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
      source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget →
        source.RegimeAttachmentFaceSourceDataFoundationTarget ∧
        source.RegimeFacePlacementFoundationTarget ∧
        PeeledCollarSmallCyclicCutLiftsToAmbient G
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/-- Verbatim source-level route index for the mapped-cut face-route equivalence. -/
theorem section92Step4ClosedWalkMappedCutFaceRouteEquivFoundationRouteIndexTarget :
    Section92Step4ClosedWalkMappedCutFaceRouteEquivFoundationRouteIndexTarget := by
  intro V _ G emb source regime h
  have hsource :
      source.RegimeAttachmentFaceSourceDataFoundationTarget :=
    source.regimeAttachmentFaceSourceDataFoundationTarget_of_mappedCutAvoidingFaceRouteTarget
      h
  have hfoundation :
      source.RegimeFacePlacementFoundationTarget :=
    source.facePlacementNoncrossingTarget_of_mappedCutAvoidingFaceRouteTarget
      h
  have hconsequences :=
    source.routeIndexConsequences_of_mappedCutAvoidingFaceRouteTarget
      regime h
  exact
    ⟨hsource, hfoundation, hconsequences.2.1,
      hconsequences.2.2.1, hconsequences.2.2.2.1,
      hconsequences.2.2.2.2⟩

end Mettapedia.GraphTheory.FourColor
