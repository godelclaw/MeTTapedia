import Mettapedia.GraphTheory.FourColor.PeeledCollarRegimeFacePlacementFoundationIndex

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Source-level attachment-face placement target for the regime foundation
route.  This is the first geometric half of the face-placement foundation
target.
-/
def RegimeAttachmentFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) : Prop :=
  source.toPlanarBoundaryAnnulusBoundaryData
    |>.PeeledCollarOffCarrierAttachmentFaceSourceTarget

/--
Source-level noncrossing-upgrade target for the regime foundation route.
This is the second geometric half of the face-placement foundation target.
-/
def RegimeFaceNoncrossingUpgradeFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) : Prop :=
  source.toPlanarBoundaryAnnulusBoundaryData
    |>.PeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget

/--
The split source-level geometric foundation targets supply the named
face-placement foundation target.
-/
theorem
    regimeFacePlacementFoundationTarget_of_regimeAttachmentFaceSourceFoundationTarget_of_regimeFaceNoncrossingUpgradeFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hface : source.RegimeAttachmentFaceSourceFoundationTarget)
    (hnoncross : source.RegimeFaceNoncrossingUpgradeFoundationTarget) :
    source.RegimeFacePlacementFoundationTarget :=
  source.facePlacementNoncrossingTarget_of_noncrossingFaceSourceTarget
    (source.toPlanarBoundaryAnnulusBoundaryData
      |>.attachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
        hface hnoncross)

/--
The split source-level geometric foundation targets supply the full indexed
source route consequences.
-/
theorem routeIndexConsequences_of_regimeAttachmentFaceSourceFoundationTarget_of_regimeFaceNoncrossingUpgradeFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (hface : source.RegimeAttachmentFaceSourceFoundationTarget)
    (hnoncross : source.RegimeFaceNoncrossingUpgradeFoundationTarget) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      CyclicallyFiveEdgeConnected
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
  section92Step4ClosedWalkRegimeFacePlacementFoundationRouteIndexTarget
    source regime
    (source.regimeFacePlacementFoundationTarget_of_regimeAttachmentFaceSourceFoundationTarget_of_regimeFaceNoncrossingUpgradeFoundationTarget
      hface hnoncross)

end PlanarBoundaryClosedWalkAnnulusBoundarySource

namespace PlanarBoundaryAnnulusCollarGeometry

/--
Canonical aligned attachment-face placement target for the regime foundation
route.
-/
def RegimeAttachmentFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceTarget data

/--
Canonical aligned noncrossing-upgrade target for the regime foundation route.
-/
def RegimeFaceNoncrossingUpgradeFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
    data

/--
Canonical aligned split geometric foundation targets supply the source-level
face-placement foundation target.
-/
theorem
    sourceRegimeFacePlacementFoundationTarget_of_regimeAttachmentFaceSourceFoundationTarget_of_regimeFaceNoncrossingUpgradeFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (hface : data.RegimeAttachmentFaceSourceFoundationTarget)
    (hnoncross : data.RegimeFaceNoncrossingUpgradeFoundationTarget) :
    source.RegimeFacePlacementFoundationTarget :=
  source.regimeFacePlacementFoundationTarget_of_regimeAttachmentFaceSourceFoundationTarget_of_regimeFaceNoncrossingUpgradeFoundationTarget
    (by
      change source.toPlanarBoundaryAnnulusBoundaryData
        |>.PeeledCollarOffCarrierAttachmentFaceSourceTarget
      simpa [RegimeAttachmentFaceSourceFoundationTarget,
        PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceTarget,
        hboundary] using hface)
    (by
      change source.toPlanarBoundaryAnnulusBoundaryData
        |>.PeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
      simpa [RegimeFaceNoncrossingUpgradeFoundationTarget,
        PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget,
        hboundary] using hnoncross)

/--
Canonical aligned split geometric foundation targets supply the full indexed
canonical route consequences.
-/
theorem routeIndexConsequences_of_regimeAttachmentFaceSourceFoundationTarget_of_regimeFaceNoncrossingUpgradeFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (hface : data.RegimeAttachmentFaceSourceFoundationTarget)
    (hnoncross : data.RegimeFaceNoncrossingUpgradeFoundationTarget) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
        data.inducedBoundaryGraph :=
  section92Step4CanonicalClosedWalkRegimeFacePlacementFoundationRouteIndexTarget
    data regime source hboundary
    (data.sourceRegimeFacePlacementFoundationTarget_of_regimeAttachmentFaceSourceFoundationTarget_of_regimeFaceNoncrossingUpgradeFoundationTarget
      source hboundary hface hnoncross)

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Repaired aligned attachment-face placement target for the regime foundation
route.
-/
def RegimeAttachmentFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    Prop :=
  PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceTarget
    data

/--
Repaired aligned noncrossing-upgrade target for the regime foundation route.
-/
def RegimeFaceNoncrossingUpgradeFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    Prop :=
  PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
    data

/--
Repaired aligned split geometric foundation targets supply the source-level
face-placement foundation target.
-/
theorem
    sourceRegimeFacePlacementFoundationTarget_of_regimeAttachmentFaceSourceFoundationTarget_of_regimeFaceNoncrossingUpgradeFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (hface : data.RegimeAttachmentFaceSourceFoundationTarget)
    (hnoncross : data.RegimeFaceNoncrossingUpgradeFoundationTarget) :
    source.RegimeFacePlacementFoundationTarget :=
  source.regimeFacePlacementFoundationTarget_of_regimeAttachmentFaceSourceFoundationTarget_of_regimeFaceNoncrossingUpgradeFoundationTarget
    (by
      change source.toPlanarBoundaryAnnulusBoundaryData
        |>.PeeledCollarOffCarrierAttachmentFaceSourceTarget
      simpa [RegimeAttachmentFaceSourceFoundationTarget,
        PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceTarget,
        hboundary] using hface)
    (by
      change source.toPlanarBoundaryAnnulusBoundaryData
        |>.PeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
      simpa [RegimeFaceNoncrossingUpgradeFoundationTarget,
        PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget,
        hboundary] using hnoncross)

/--
Repaired aligned split geometric foundation targets supply the full indexed
repaired route consequences.
-/
theorem routeIndexConsequences_of_regimeAttachmentFaceSourceFoundationTarget_of_regimeFaceNoncrossingUpgradeFoundationTarget
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
    (hface : data.RegimeAttachmentFaceSourceFoundationTarget)
    (hnoncross : data.RegimeFaceNoncrossingUpgradeFoundationTarget) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
        data.inducedBoundaryGraph :=
  section92Step4RepairedClosedWalkRegimeFacePlacementFoundationRouteIndexTarget
    data regime source hboundary
    (data.sourceRegimeFacePlacementFoundationTarget_of_regimeAttachmentFaceSourceFoundationTarget_of_regimeFaceNoncrossingUpgradeFoundationTarget
      source hboundary hface hnoncross)

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Source-level split-foundation route index: proving the two geometric split
targets is enough to obtain the face-placement foundation target and all
downstream source consequences.
-/
def Section92Step4ClosedWalkRegimeFacePlacementSplitFoundationRouteIndexTarget :
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
      source.RegimeAttachmentFaceSourceFoundationTarget →
      source.RegimeFaceNoncrossingUpgradeFoundationTarget →
        source.RegimeFacePlacementFoundationTarget ∧
        PeeledCollarSmallCyclicCutLiftsToAmbient G
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/-- Verbatim source-level split-foundation route index. -/
theorem section92Step4ClosedWalkRegimeFacePlacementSplitFoundationRouteIndexTarget :
    Section92Step4ClosedWalkRegimeFacePlacementSplitFoundationRouteIndexTarget := by
  intro V _ G emb source regime hface hnoncross
  have hfoundation :
      source.RegimeFacePlacementFoundationTarget :=
    source.regimeFacePlacementFoundationTarget_of_regimeAttachmentFaceSourceFoundationTarget_of_regimeFaceNoncrossingUpgradeFoundationTarget
      hface hnoncross
  rcases
    source.routeIndexConsequences_of_regimeAttachmentFaceSourceFoundationTarget_of_regimeFaceNoncrossingUpgradeFoundationTarget
      regime hface hnoncross with
    ⟨hlift, hcyc, htwo, hs4⟩
  exact ⟨hfoundation, hlift, hcyc, htwo, hs4⟩

end Mettapedia.GraphTheory.FourColor
