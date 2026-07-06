import Mettapedia.GraphTheory.FourColor.PeeledCollarRegimeS4

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryAnnulusBoundaryData

/--
Face-source version of the attachment noncrossing target.  It asks the
planar foundation layer to place any two off-carrier attachments on selected
boundary edges of one noncrossing face, while leaving the already available
selected-boundary-arc geometry to be supplied separately.
-/
def CutOffCarrierAttachmentNoncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb)
    (cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)) :
    Prop :=
  ∃ side : V → Prop,
    (∀ w : BoundaryEdgeSetEndpointVertex
        (G := G) data.ambientBoundaryEdgeSet,
      side (data.inducedBoundaryEmbedding w) ↔ cut.side w) ∧
      ∀ root : V,
        ∀ a b : BoundaryEdgeSetEndpointVertex
            (G := G) data.ambientBoundaryEdgeSet,
          BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
            (G := G) data.ambientBoundaryEdgeSet root a →
          BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
            (G := G) data.ambientBoundaryEdgeSet root b →
            ∃ f : AmbientFace emb.faces,
            ∃ e₁ e₂ : G.edgeSet,
            ∃ _ : e₁ ∈ emb.faceBoundary f.1,
            ∃ _ : e₂ ∈ emb.faceBoundary f.1,
            ∃ _ : e₁ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
            ∃ _ : e₂ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
              (a : V) ∈ (e₁ : Sym2 V) ∧
                (b : V) ∈ (e₂ : Sym2 V) ∧
                  data.FaceSelectedBoundaryEdgesDoNotCrossSide side f

/--
Per-cut face-source witnesses plus global selected-boundary arc geometry
supply the selected-boundary-arc source target consumed by the downstream
collar route.
-/
theorem cutOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_faceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    {cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)}
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (h :
      data.CutOffCarrierAttachmentNoncrossingFaceSourceTarget cut) :
    data.CutOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
      cut := by
  rcases h with ⟨side, hside, hroute⟩
  refine ⟨side, hside, ?_⟩
  intro root a b hrootA hrootB
  rcases hroute root a b hrootA hrootB with
    ⟨f, e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb, hnoncross⟩
  exact
    ⟨f, e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb, harc f,
      hnoncross⟩

/--
Bundled selected-boundary arc geometry supplies the arc half of the per-cut
face-source bridge.
-/
theorem cutOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget_of_selectedBoundaryArcGeometry_of_faceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    {cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)}
    (geom : PlanarBoundarySelectedBoundaryArcGeometry emb)
    (h :
      data.CutOffCarrierAttachmentNoncrossingFaceSourceTarget cut) :
    data.CutOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
      cut :=
  cutOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_faceSourceTarget
    geom.boundarySelectedBoundaryArcOnFace h

/--
Annulus-boundary all-cuts face-source target.  This is the remaining
planar-normal-form obligation before the selected-boundary arc geometry is
inserted.
-/
def PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) : Prop :=
  ∀ cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet),
    data.CutOffCarrierAttachmentNoncrossingFaceSourceTarget cut

/--
All-cuts face-source witnesses plus global selected-boundary arc geometry
supply the all-cuts selected-boundary-arc source target.
-/
theorem attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_faceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (h :
      data.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget) :
    data.PeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget := by
  intro cut
  exact
    data.cutOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_faceSourceTarget
      harc (h cut)

/--
Bundled selected-boundary arc geometry supplies the arc half of the all-cuts
face-source bridge.
-/
theorem attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_selectedBoundaryArcGeometry_of_faceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (geom : PlanarBoundarySelectedBoundaryArcGeometry emb)
    (h :
      data.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget) :
    data.PeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget :=
  attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_faceSourceTarget
    geom.boundarySelectedBoundaryArcOnFace h

end PlanarBoundaryAnnulusBoundaryData

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
The closed-walk annulus source supplies the selected-boundary arc geometry
needed to upgrade a per-cut face-source witness on its extracted boundary
split.
-/
theorem cutOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget_of_faceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    {cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph
          (G := G) source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)}
    (h :
      source.toPlanarBoundaryAnnulusBoundaryData
        |>.CutOffCarrierAttachmentNoncrossingFaceSourceTarget cut) :
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.CutOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
        cut :=
  source.toPlanarBoundaryAnnulusBoundaryData
    |>.cutOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget_of_selectedBoundaryArcGeometry_of_faceSourceTarget
      source.toPlanarBoundarySelectedBoundaryArcGeometry h

/--
The closed-walk annulus source supplies the selected-boundary arc geometry
needed to upgrade all face-source witnesses on its extracted boundary split.
-/
theorem attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_faceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h :
      source.toPlanarBoundaryAnnulusBoundaryData
        |>.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget) :
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.PeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget :=
  source.toPlanarBoundaryAnnulusBoundaryData
    |>.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_selectedBoundaryArcGeometry_of_faceSourceTarget
      source.toPlanarBoundarySelectedBoundaryArcGeometry h

end PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Canonical annulus face-source target.  This is the normal-form obligation
after the closed-walk/selected-arc layer has been separated out.
-/
def PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  data.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget

/--
Repaired previous-boundary annulus variant of the face-source target.
-/
def PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    Prop :=
  data.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget

/--
Canonical annulus face-source witnesses plus selected-boundary arc geometry
supply the selected-boundary-arc source target.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_faceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        data) :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
      data :=
  data.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_faceSourceTarget
    harc h

/--
Canonical annulus face-source witnesses plus bundled selected-boundary arc
geometry supply the selected-boundary-arc source target.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget_of_selectedBoundaryArcGeometry_of_faceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (geom : PlanarBoundarySelectedBoundaryArcGeometry emb)
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        data) :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
      data :=
  data.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_selectedBoundaryArcGeometry_of_faceSourceTarget
    geom h

/--
Repaired annulus face-source witnesses plus selected-boundary arc geometry
supply the selected-boundary-arc source target.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_faceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        data) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
      data :=
  data.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_faceSourceTarget
    harc h

/--
Repaired annulus face-source witnesses plus bundled selected-boundary arc
geometry supply the selected-boundary-arc source target.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget_of_selectedBoundaryArcGeometry_of_faceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (geom : PlanarBoundarySelectedBoundaryArcGeometry emb)
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        data) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
      data :=
  data.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_selectedBoundaryArcGeometry_of_faceSourceTarget
    geom h

namespace MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs

/--
Canonical-annulus S4 winding salvage from face-source witnesses once the
selected-boundary arc geometry is supplied by the planar boundary source.
-/
theorem
    closedCollarWindingFreedomEscape_not_simplyRealizable_of_boundarySelectedBoundaryArcOnFace_of_faceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        data) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomEscape_not_simplyRealizable_of_noncrossingSelectedBoundaryArcSourceTarget
    regime
    (planarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_faceSourceTarget
      harc h)

/--
Canonical-annulus S4 winding salvage from face-source witnesses and bundled
selected-boundary arc geometry.
-/
theorem
    closedCollarWindingFreedomEscape_not_simplyRealizable_of_selectedBoundaryArcGeometry_of_faceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (geom : PlanarBoundarySelectedBoundaryArcGeometry emb)
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        data) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomEscape_not_simplyRealizable_of_boundarySelectedBoundaryArcOnFace_of_faceSourceTarget
    regime geom.boundarySelectedBoundaryArcOnFace h

end MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs

namespace MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs

/--
Repaired-annulus S4 winding salvage from face-source witnesses once the
selected-boundary arc geometry is supplied by the planar boundary source.
-/
theorem
    closedCollarWindingFreedomEscape_not_simplyRealizable_of_boundarySelectedBoundaryArcOnFace_of_faceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        data) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomEscape_not_simplyRealizable_of_noncrossingSelectedBoundaryArcSourceTarget
    regime
    (planarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_faceSourceTarget
      harc h)

/--
Repaired-annulus S4 winding salvage from face-source witnesses and bundled
selected-boundary arc geometry.
-/
theorem
    closedCollarWindingFreedomEscape_not_simplyRealizable_of_selectedBoundaryArcGeometry_of_faceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (geom : PlanarBoundarySelectedBoundaryArcGeometry emb)
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        data) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomEscape_not_simplyRealizable_of_boundarySelectedBoundaryArcOnFace_of_faceSourceTarget
    regime geom.boundarySelectedBoundaryArcOnFace h

end MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs

/--
End-to-end S4 salvage target using the canonical annulus route with the
annulus obligation stated as face-source noncrossing data and the selected
boundary arc geometry supplied separately.
-/
def
    Section92Step4CanonicalAnnulusOffCarrierAttachmentNoncrossingFaceSourceRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      (∀ f : AmbientFace emb.faces,
        BoundarySelectedBoundaryArcOnFace (emb := emb) f) →
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        data →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim end-to-end canonical-annulus face-source S4 salvage statement. -/
theorem
    section92Step4CanonicalAnnulusOffCarrierAttachmentNoncrossingFaceSourceRegimeDischargedS4SalvageTarget :
    Section92Step4CanonicalAnnulusOffCarrierAttachmentNoncrossingFaceSourceRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime harc h
  exact
    MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_boundarySelectedBoundaryArcOnFace_of_faceSourceTarget
      regime harc h

/--
End-to-end S4 salvage target using the repaired annulus route with the
annulus obligation stated as face-source noncrossing data and the selected
boundary arc geometry supplied separately.
-/
def
    Section92Step4RepairedAnnulusOffCarrierAttachmentNoncrossingFaceSourceRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      (∀ f : AmbientFace emb.faces,
        BoundarySelectedBoundaryArcOnFace (emb := emb) f) →
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
        data →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim end-to-end repaired-annulus face-source S4 salvage statement. -/
theorem
    section92Step4RepairedAnnulusOffCarrierAttachmentNoncrossingFaceSourceRegimeDischargedS4SalvageTarget :
    Section92Step4RepairedAnnulusOffCarrierAttachmentNoncrossingFaceSourceRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime harc h
  exact
    MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_boundarySelectedBoundaryArcOnFace_of_faceSourceTarget
      regime harc h

end Mettapedia.GraphTheory.FourColor
