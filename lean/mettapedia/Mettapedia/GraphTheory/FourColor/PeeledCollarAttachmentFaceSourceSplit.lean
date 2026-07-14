import Mettapedia.GraphTheory.FourColor.PeeledCollarClosedWalkFaceSourceBridge

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryAnnulusBoundaryData

/--
Face witness for a pair of off-carrier attachments: the two attachment
vertices lie on selected boundary edges of the same ambient face.
-/
def OffCarrierAttachmentFacePlacementOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb)
    (_root : V)
    (a b : BoundaryEdgeSetEndpointVertex
        (G := G) data.ambientBoundaryEdgeSet)
    (f : AmbientFace emb.faces) : Prop :=
  ∃ e₁ e₂ : G.edgeSet,
  ∃ _ : e₁ ∈ emb.faceBoundary f.1,
  ∃ _ : e₂ ∈ emb.faceBoundary f.1,
  ∃ _ : e₁ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
  ∃ _ : e₂ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
    (a : V) ∈ (e₁ : Sym2 V) ∧
      (b : V) ∈ (e₂ : Sym2 V)

/--
Attachment-face placement target for one carrier cut.  It only asks the
planar normal form to place two off-carrier attachments on selected boundary
edges of one ambient face, with a side compatible with the carrier cut.

The separate noncrossing-upgrade target below supplies a noncrossing chosen
face for the same attachment pair.
-/
def CutOffCarrierAttachmentFaceSourceTarget
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
              data.OffCarrierAttachmentFacePlacementOn root a b f

/--
Noncrossing upgrade target for one carrier cut.  Given a compatible ambient
side and attachment-face placements, the planar foundation layer can choose
for each attachment pair a placement face whose selected boundary edges do
not cross that side.
-/
def CutOffCarrierAttachmentFaceNoncrossingUpgradeTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb)
    (cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)) :
    Prop :=
  ∀ side : V → Prop,
    (∀ w : BoundaryEdgeSetEndpointVertex
        (G := G) data.ambientBoundaryEdgeSet,
      side (data.inducedBoundaryEmbedding w) ↔ cut.side w) →
      (∀ root : V,
        ∀ a b : BoundaryEdgeSetEndpointVertex
            (G := G) data.ambientBoundaryEdgeSet,
          BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
            (G := G) data.ambientBoundaryEdgeSet root a →
          BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
            (G := G) data.ambientBoundaryEdgeSet root b →
            ∃ f : AmbientFace emb.faces,
              data.OffCarrierAttachmentFacePlacementOn root a b f) →
        ∀ root : V,
          ∀ a b : BoundaryEdgeSetEndpointVertex
              (G := G) data.ambientBoundaryEdgeSet,
            BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
              (G := G) data.ambientBoundaryEdgeSet root a →
            BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
              (G := G) data.ambientBoundaryEdgeSet root b →
              ∃ f : AmbientFace emb.faces,
                data.OffCarrierAttachmentFacePlacementOn root a b f ∧
                  data.FaceSelectedBoundaryEdgesDoNotCrossSide side f

/--
Attachment-face placement plus the noncrossing upgrade supply the face-source
target consumed by the selected-boundary-arc bridge.
-/
theorem cutOffCarrierAttachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    {cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)}
    (hface : data.CutOffCarrierAttachmentFaceSourceTarget cut)
    (hnoncross :
      data.CutOffCarrierAttachmentFaceNoncrossingUpgradeTarget cut) :
    data.CutOffCarrierAttachmentNoncrossingFaceSourceTarget cut := by
  rcases hface with ⟨side, hside, hroute⟩
  refine ⟨side, hside, ?_⟩
  intro root a b hrootA hrootB
  rcases hnoncross side hside hroute root a b hrootA hrootB with
    ⟨f, hplacement, hfaceNoncross⟩
  rcases hplacement with
    ⟨e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb⟩
  exact
    ⟨f, e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb,
      hfaceNoncross⟩

/--
All-cuts attachment-face placement target.
-/
def PeeledCollarOffCarrierAttachmentFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) : Prop :=
  ∀ cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet),
    data.CutOffCarrierAttachmentFaceSourceTarget cut

/--
All-cuts noncrossing-upgrade target.
-/
def PeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) : Prop :=
  ∀ cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet),
    data.CutOffCarrierAttachmentFaceNoncrossingUpgradeTarget cut

/--
All-cuts attachment-face placement plus all-cuts noncrossing upgrade supply
the all-cuts face-source target.
-/
theorem attachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (hface : data.PeeledCollarOffCarrierAttachmentFaceSourceTarget)
    (hnoncross :
      data.PeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget) :
    data.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget := by
  intro cut
  exact
    data.cutOffCarrierAttachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      (hface cut) (hnoncross cut)

end PlanarBoundaryAnnulusBoundaryData

/--
Canonical annulus attachment-face placement target.
-/
def PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  data.PeeledCollarOffCarrierAttachmentFaceSourceTarget

/--
Canonical annulus noncrossing-upgrade target.
-/
def PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  data.PeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget

/--
Repaired annulus attachment-face placement target.
-/
def PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    Prop :=
  data.PeeledCollarOffCarrierAttachmentFaceSourceTarget

/--
Repaired annulus noncrossing-upgrade target.
-/
def PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    Prop :=
  data.PeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget

/--
Canonical annulus composition from attachment-face placement and noncrossing
upgrade to the face-source target.
-/
theorem
    planarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (hface :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceTarget
        data)
    (hnoncross :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
        data) :
    PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
      data :=
  data.attachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
    hface hnoncross

/--
Repaired annulus composition from attachment-face placement and noncrossing
upgrade to the face-source target.
-/
theorem
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (hface :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceTarget
        data)
    (hnoncross :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
        data) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
      data :=
  data.attachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
    hface hnoncross

namespace PlanarBoundaryAnnulusCollarGeometry

/--
Canonical annulus S4 salvage from an aligned closed-walk source whose
face-source target has been split into attachment-face placement and
noncrossing upgrade.
-/
theorem
    closedCollarWindingFreedomEscape_not_simplyRealizable_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (hface :
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceTarget
        source.toPlanarBoundaryAnnulusBoundaryData)
    (hnoncross :
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
        source.toPlanarBoundaryAnnulusBoundaryData) :
    ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
      data.inducedBoundaryGraph :=
  data.closedCollarWindingFreedomEscape_not_simplyRealizable_of_closedWalkAnnulusBoundarySource_faceSourceTarget
    regime source hboundary
    (source.toPlanarBoundaryAnnulusBoundaryData
      |>.attachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
        hface hnoncross)

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Repaired annulus S4 salvage from an aligned closed-walk source whose
face-source target has been split into attachment-face placement and
noncrossing upgrade.
-/
theorem
    closedCollarWindingFreedomEscape_not_simplyRealizable_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
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
    (hface :
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceTarget
        source.toPlanarBoundaryAnnulusBoundaryData)
    (hnoncross :
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
        source.toPlanarBoundaryAnnulusBoundaryData) :
    ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
      data.inducedBoundaryGraph :=
  data.closedCollarWindingFreedomEscape_not_simplyRealizable_of_closedWalkAnnulusBoundarySource_faceSourceTarget
    regime source hboundary
    (source.toPlanarBoundaryAnnulusBoundaryData
      |>.attachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
        hface hnoncross)

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
End-to-end canonical annulus S4 target with the closed-walk source obligation
split into attachment-face placement and noncrossing upgrade.
-/
def
    Section92Step4CanonicalAnnulusClosedWalkAttachmentFaceAndNoncrossingUpgradeRegimeDischargedS4SalvageTarget :
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
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceTarget
        source.toPlanarBoundaryAnnulusBoundaryData →
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
        source.toPlanarBoundaryAnnulusBoundaryData →
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim canonical-annulus split-source S4 salvage statement. -/
theorem
    section92Step4CanonicalAnnulusClosedWalkAttachmentFaceAndNoncrossingUpgradeRegimeDischargedS4SalvageTarget :
    Section92Step4CanonicalAnnulusClosedWalkAttachmentFaceAndNoncrossingUpgradeRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime source hboundary hface hnoncross
  exact
    data.closedCollarWindingFreedomEscape_not_simplyRealizable_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      regime source hboundary hface hnoncross

/--
End-to-end repaired annulus S4 target with the closed-walk source obligation
split into attachment-face placement and noncrossing upgrade.
-/
def
    Section92Step4RepairedAnnulusClosedWalkAttachmentFaceAndNoncrossingUpgradeRegimeDischargedS4SalvageTarget :
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
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceTarget
        source.toPlanarBoundaryAnnulusBoundaryData →
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
        source.toPlanarBoundaryAnnulusBoundaryData →
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim repaired-annulus split-source S4 salvage statement. -/
theorem
    section92Step4RepairedAnnulusClosedWalkAttachmentFaceAndNoncrossingUpgradeRegimeDischargedS4SalvageTarget :
    Section92Step4RepairedAnnulusClosedWalkAttachmentFaceAndNoncrossingUpgradeRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime source hboundary hface hnoncross
  exact
    data.closedCollarWindingFreedomEscape_not_simplyRealizable_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      regime source hboundary hface hnoncross

end Mettapedia.GraphTheory.FourColor
