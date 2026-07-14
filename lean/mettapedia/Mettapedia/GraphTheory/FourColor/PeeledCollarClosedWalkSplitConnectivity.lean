import Mettapedia.GraphTheory.FourColor.PeeledCollarAttachmentFaceSourceSplitConnectivity

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryAnnulusCollarGeometry

/--
Canonical annulus cyclic five-edge-connectivity from an aligned closed-walk
source whose remaining face-source obligation is split into attachment-face
placement and noncrossing upgrade.
-/
theorem cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
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
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs.cyclicallyFiveEdgeConnected_of_noncrossingSelectedBoundaryArcSourceTarget
    regime
    (data.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_closedWalkAnnulusBoundarySource_faceSourceTarget
      source hboundary
      (source.toPlanarBoundaryAnnulusBoundaryData
        |>.attachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
          hface hnoncross))

/--
Canonical annulus no-cyclic-two-cut consequence from a closed-walk split
source.
-/
theorem closedCollarForbidsCyclicTwoCut_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
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
    ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph :=
  closedCollarForbidsCyclicTwoCut_of_cyclicallyFiveEdgeConnected
    (data.cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      regime source hboundary hface hnoncross)

/--
Canonical annulus S4 salvage through the upstream cyclic-connectivity bridge
from a closed-walk split source.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_throughConnectivity_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
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
  closedCollarWindingFreedomSeparatorEquippedEscape_not_realizable_of_cyclicallyFiveEdgeConnected
    (data.cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      regime source hboundary hface hnoncross)

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Repaired annulus cyclic five-edge-connectivity from an aligned closed-walk
source whose remaining face-source obligation is split into attachment-face
placement and noncrossing upgrade.
-/
theorem cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
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
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs.cyclicallyFiveEdgeConnected_of_noncrossingSelectedBoundaryArcSourceTarget
    regime
    (data.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_closedWalkAnnulusBoundarySource_faceSourceTarget
      source hboundary
      (source.toPlanarBoundaryAnnulusBoundaryData
        |>.attachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
          hface hnoncross))

/--
Repaired annulus no-cyclic-two-cut consequence from a closed-walk split
source.
-/
theorem closedCollarForbidsCyclicTwoCut_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
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
    ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph :=
  closedCollarForbidsCyclicTwoCut_of_cyclicallyFiveEdgeConnected
    (data.cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      regime source hboundary hface hnoncross)

/--
Repaired annulus S4 salvage through the upstream cyclic-connectivity bridge
from a closed-walk split source.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_throughConnectivity_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
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
  closedCollarWindingFreedomSeparatorEquippedEscape_not_realizable_of_cyclicallyFiveEdgeConnected
    (data.cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      regime source hboundary hface hnoncross)

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Closed-walk-source canonical-annulus cyclic-connectivity target with split
attachment-face source obligations.
-/
def
    Section92Step4CanonicalAnnulusClosedWalkAttachmentFaceAndNoncrossingUpgradeCyclicallyFiveEdgeConnectedTarget :
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
        CyclicallyFiveEdgeConnected data.inducedBoundaryGraph

/-- Verbatim canonical closed-walk split-source cyclic-connectivity statement. -/
theorem
    section92Step4CanonicalAnnulusClosedWalkAttachmentFaceAndNoncrossingUpgradeCyclicallyFiveEdgeConnectedTarget :
    Section92Step4CanonicalAnnulusClosedWalkAttachmentFaceAndNoncrossingUpgradeCyclicallyFiveEdgeConnectedTarget := by
  intro V _ G emb data regime source hboundary hface hnoncross
  exact
    data.cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      regime source hboundary hface hnoncross

/--
Closed-walk-source repaired-annulus cyclic-connectivity target with split
attachment-face source obligations.
-/
def
    Section92Step4RepairedAnnulusClosedWalkAttachmentFaceAndNoncrossingUpgradeCyclicallyFiveEdgeConnectedTarget :
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
        CyclicallyFiveEdgeConnected data.inducedBoundaryGraph

/-- Verbatim repaired closed-walk split-source cyclic-connectivity statement. -/
theorem
    section92Step4RepairedAnnulusClosedWalkAttachmentFaceAndNoncrossingUpgradeCyclicallyFiveEdgeConnectedTarget :
    Section92Step4RepairedAnnulusClosedWalkAttachmentFaceAndNoncrossingUpgradeCyclicallyFiveEdgeConnectedTarget := by
  intro V _ G emb data regime source hboundary hface hnoncross
  exact
    data.cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      regime source hboundary hface hnoncross

/--
Closed-walk-source canonical-annulus S4 target routed through the upstream
cyclic-connectivity bridge.
-/
def
    Section92Step4CanonicalAnnulusClosedWalkAttachmentFaceAndNoncrossingUpgradeThroughConnectivityRegimeDischargedS4SalvageTarget :
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

/-- Verbatim canonical closed-walk split-source S4 statement through cyclic connectivity. -/
theorem
    section92Step4CanonicalAnnulusClosedWalkAttachmentFaceAndNoncrossingUpgradeThroughConnectivityRegimeDischargedS4SalvageTarget :
    Section92Step4CanonicalAnnulusClosedWalkAttachmentFaceAndNoncrossingUpgradeThroughConnectivityRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime source hboundary hface hnoncross
  exact
    data.closedCollarWindingFreedomEscape_not_simplyRealizable_throughConnectivity_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      regime source hboundary hface hnoncross

/--
Closed-walk-source repaired-annulus S4 target routed through the upstream
cyclic-connectivity bridge.
-/
def
    Section92Step4RepairedAnnulusClosedWalkAttachmentFaceAndNoncrossingUpgradeThroughConnectivityRegimeDischargedS4SalvageTarget :
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

/-- Verbatim repaired closed-walk split-source S4 statement through cyclic connectivity. -/
theorem
    section92Step4RepairedAnnulusClosedWalkAttachmentFaceAndNoncrossingUpgradeThroughConnectivityRegimeDischargedS4SalvageTarget :
    Section92Step4RepairedAnnulusClosedWalkAttachmentFaceAndNoncrossingUpgradeThroughConnectivityRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime source hboundary hface hnoncross
  exact
    data.closedCollarWindingFreedomEscape_not_simplyRealizable_throughConnectivity_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      regime source hboundary hface hnoncross

end Mettapedia.GraphTheory.FourColor
