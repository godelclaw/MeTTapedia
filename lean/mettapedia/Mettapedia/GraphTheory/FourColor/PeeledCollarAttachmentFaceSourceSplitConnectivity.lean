import Mettapedia.GraphTheory.FourColor.PeeledCollarAttachmentFaceSourceSplit

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryAnnulusBoundaryData

/--
Split attachment-face placement plus noncrossing upgrade, together with
selected-boundary arc geometry, supplies the selected-boundary arc source
target used by the cut-lift route.
-/
theorem attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (hface : data.PeeledCollarOffCarrierAttachmentFaceSourceTarget)
    (hnoncross :
      data.PeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget) :
    data.PeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget :=
  data.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_faceSourceTarget
    harc
    (data.attachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      hface hnoncross)

/--
Bundled selected-boundary arc geometry supplies the arc half of the split
attachment-face source bridge.
-/
theorem attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_selectedBoundaryArcGeometry_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (geom : PlanarBoundarySelectedBoundaryArcGeometry emb)
    (hface : data.PeeledCollarOffCarrierAttachmentFaceSourceTarget)
    (hnoncross :
      data.PeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget) :
    data.PeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget :=
  data.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
    geom.boundarySelectedBoundaryArcOnFace hface hnoncross

end PlanarBoundaryAnnulusBoundaryData

namespace MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs

/--
Canonical-annulus upstream inheritance from the selected-boundary arc source:
the source target supplies mapped-cut-deleted boundary connectivity, hence the
small-cut lift, and the ambient regime supplies cyclic five-edge-connectivity.
-/
theorem cyclicallyFiveEdgeConnected_of_noncrossingSelectedBoundaryArcSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
        data) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  (MinimalCounterexampleOffCarrierMappedCutAvoidingSharedEndpointConnectedPeeledCollarRouteInputs.mk
    regime
    (data.mappedCutAvoidingSharedEndpointConnectivityTarget_of_noncrossingSelectedBoundaryArcSourceTarget
      h))
      |>.cyclicallyFiveEdgeConnected

/--
Canonical-annulus upstream inheritance from split attachment-face placement
and noncrossing upgrade.
-/
theorem cyclicallyFiveEdgeConnected_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (hface :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceTarget
        data)
    (hnoncross :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
        data) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  cyclicallyFiveEdgeConnected_of_noncrossingSelectedBoundaryArcSourceTarget
    regime
    (data.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      harc hface hnoncross)

/--
Canonical-annulus split-source no-cyclic-two-cut consequence.
-/
theorem closedCollarForbidsCyclicTwoCut_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (hface :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceTarget
        data)
    (hnoncross :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
        data) :
    ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph :=
  closedCollarForbidsCyclicTwoCut_of_cyclicallyFiveEdgeConnected
    (cyclicallyFiveEdgeConnected_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      regime harc hface hnoncross)

/--
Canonical-annulus split-source S4 salvage through the upstream cyclic
five-edge-connectivity bridge.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (hface :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceTarget
        data)
    (hnoncross :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
        data) :
    ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomSeparatorEquippedEscape_not_realizable_of_cyclicallyFiveEdgeConnected
    (cyclicallyFiveEdgeConnected_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      regime harc hface hnoncross)

end MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs

namespace MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs

/--
Repaired-annulus upstream inheritance from the selected-boundary arc source.
-/
theorem cyclicallyFiveEdgeConnected_of_noncrossingSelectedBoundaryArcSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
        data) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  (MinimalCounterexampleOffCarrierMappedCutAvoidingSharedEndpointConnectedPeeledCollarRouteInputs.mk
    regime
    (data.mappedCutAvoidingSharedEndpointConnectivityTarget_of_noncrossingSelectedBoundaryArcSourceTarget
      h))
      |>.cyclicallyFiveEdgeConnected

/--
Repaired-annulus upstream inheritance from split attachment-face placement and
noncrossing upgrade.
-/
theorem cyclicallyFiveEdgeConnected_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (hface :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceTarget
        data)
    (hnoncross :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
        data) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  cyclicallyFiveEdgeConnected_of_noncrossingSelectedBoundaryArcSourceTarget
    regime
    (data.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      harc hface hnoncross)

/--
Repaired-annulus split-source no-cyclic-two-cut consequence.
-/
theorem closedCollarForbidsCyclicTwoCut_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (hface :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceTarget
        data)
    (hnoncross :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
        data) :
    ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph :=
  closedCollarForbidsCyclicTwoCut_of_cyclicallyFiveEdgeConnected
    (cyclicallyFiveEdgeConnected_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      regime harc hface hnoncross)

/--
Repaired-annulus split-source S4 salvage through the upstream cyclic
five-edge-connectivity bridge.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (hface :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceTarget
        data)
    (hnoncross :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
        data) :
    ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomSeparatorEquippedEscape_not_realizable_of_cyclicallyFiveEdgeConnected
    (cyclicallyFiveEdgeConnected_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      regime harc hface hnoncross)

end MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs

/--
Upstream canonical-annulus target: split attachment-face source obligations
and selected-boundary arc geometry supply cyclic five-edge-connectivity for
the peeled collar.
-/
def
    Section92Step4CanonicalAnnulusAttachmentFaceAndNoncrossingUpgradeCyclicallyFiveEdgeConnectedTarget :
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
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceTarget
        data →
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
        data →
        CyclicallyFiveEdgeConnected data.inducedBoundaryGraph

/-- Verbatim canonical-annulus split-source cyclic-connectivity statement. -/
theorem
    section92Step4CanonicalAnnulusAttachmentFaceAndNoncrossingUpgradeCyclicallyFiveEdgeConnectedTarget :
    Section92Step4CanonicalAnnulusAttachmentFaceAndNoncrossingUpgradeCyclicallyFiveEdgeConnectedTarget := by
  intro V _ G emb data regime harc hface hnoncross
  exact
    MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs.cyclicallyFiveEdgeConnected_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      regime harc hface hnoncross

/--
Upstream repaired-annulus target: split attachment-face source obligations and
selected-boundary arc geometry supply cyclic five-edge-connectivity.
-/
def
    Section92Step4RepairedAnnulusAttachmentFaceAndNoncrossingUpgradeCyclicallyFiveEdgeConnectedTarget :
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
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceTarget
        data →
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
        data →
        CyclicallyFiveEdgeConnected data.inducedBoundaryGraph

/-- Verbatim repaired-annulus split-source cyclic-connectivity statement. -/
theorem
    section92Step4RepairedAnnulusAttachmentFaceAndNoncrossingUpgradeCyclicallyFiveEdgeConnectedTarget :
    Section92Step4RepairedAnnulusAttachmentFaceAndNoncrossingUpgradeCyclicallyFiveEdgeConnectedTarget := by
  intro V _ G emb data regime harc hface hnoncross
  exact
    MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs.cyclicallyFiveEdgeConnected_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      regime harc hface hnoncross

/--
End-to-end canonical-annulus S4 target through the split-source upstream
cyclic-connectivity bridge.
-/
def
    Section92Step4CanonicalAnnulusAttachmentFaceAndNoncrossingUpgradeRegimeDischargedS4SalvageTarget :
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
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceTarget
        data →
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
        data →
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim canonical-annulus split-source S4 statement through cyclic connectivity. -/
theorem
    section92Step4CanonicalAnnulusAttachmentFaceAndNoncrossingUpgradeRegimeDischargedS4SalvageTarget :
    Section92Step4CanonicalAnnulusAttachmentFaceAndNoncrossingUpgradeRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime harc hface hnoncross
  exact
    MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      regime harc hface hnoncross

/--
End-to-end repaired-annulus S4 target through the split-source upstream
cyclic-connectivity bridge.
-/
def
    Section92Step4RepairedAnnulusAttachmentFaceAndNoncrossingUpgradeRegimeDischargedS4SalvageTarget :
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
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceTarget
        data →
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
        data →
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim repaired-annulus split-source S4 statement through cyclic connectivity. -/
theorem
    section92Step4RepairedAnnulusAttachmentFaceAndNoncrossingUpgradeRegimeDischargedS4SalvageTarget :
    Section92Step4RepairedAnnulusAttachmentFaceAndNoncrossingUpgradeRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime harc hface hnoncross
  exact
    MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      regime harc hface hnoncross

end Mettapedia.GraphTheory.FourColor
