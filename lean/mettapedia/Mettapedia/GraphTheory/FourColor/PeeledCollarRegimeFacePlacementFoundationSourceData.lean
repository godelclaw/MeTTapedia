import Mettapedia.GraphTheory.FourColor.PeeledCollarRegimeFacePlacementFoundationSplit

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Source-level chosen attachment-face data target for the regime foundation
route.  This is equivalent to the named face-placement foundation target, but
keeps the side, placement family, and noncrossing proof bundled per carrier
cut.
-/
def RegimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) : Prop :=
  PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
    source.toPlanarBoundaryAnnulusBoundaryData

/--
The named face-placement foundation target is equivalent to chosen
attachment-face source data on the extracted boundary split.
-/
theorem
    regimeFacePlacementFoundationTarget_iff_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    source.RegimeFacePlacementFoundationTarget ↔
      source.RegimeAttachmentFaceSourceDataFoundationTarget := by
  exact source.facePlacementNoncrossingTarget_iff_attachmentFaceSourceDataTarget

/-- Chosen attachment-face source data supplies the face-placement foundation target. -/
theorem regimeFacePlacementFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeAttachmentFaceSourceDataFoundationTarget) :
    source.RegimeFacePlacementFoundationTarget :=
  (source.regimeFacePlacementFoundationTarget_iff_regimeAttachmentFaceSourceDataFoundationTarget).2
    h

/-- The face-placement foundation target forgets to chosen attachment-face source data. -/
theorem regimeAttachmentFaceSourceDataFoundationTarget_of_regimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeFacePlacementFoundationTarget) :
    source.RegimeAttachmentFaceSourceDataFoundationTarget :=
  (source.regimeFacePlacementFoundationTarget_iff_regimeAttachmentFaceSourceDataFoundationTarget).1
    h

/-- Chosen source data also supplies the split attachment-face placement half. -/
theorem regimeAttachmentFaceSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeAttachmentFaceSourceDataFoundationTarget) :
    source.RegimeAttachmentFaceSourceFoundationTarget :=
  source.toPlanarBoundaryAnnulusBoundaryData
    |>.attachmentFaceSourceTarget_of_attachmentFaceSourceDataTarget h

/--
Chosen attachment-face source data supplies the full indexed source route
consequences.
-/
theorem routeIndexConsequences_of_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h : source.RegimeAttachmentFaceSourceDataFoundationTarget) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      CyclicallyFiveEdgeConnected
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
  section92Step4ClosedWalkRegimeFacePlacementFoundationRouteIndexTarget
    source regime
    (source.regimeFacePlacementFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      h)

end PlanarBoundaryClosedWalkAnnulusBoundarySource

namespace PlanarBoundaryAnnulusCollarGeometry

/-- Canonical aligned chosen attachment-face source-data foundation target. -/
def RegimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
    data

/--
Canonical aligned chosen source data supplies the source-level chosen
source-data foundation target.
-/
theorem
    sourceRegimeAttachmentFaceSourceDataFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h : data.RegimeAttachmentFaceSourceDataFoundationTarget) :
    source.RegimeAttachmentFaceSourceDataFoundationTarget := by
  change
    PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
      source.toPlanarBoundaryAnnulusBoundaryData
  simpa [RegimeAttachmentFaceSourceDataFoundationTarget,
    PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceDataTarget,
    hboundary] using h

/--
Canonical aligned chosen source data supplies the source-level face-placement
foundation target.
-/
theorem sourceRegimeFacePlacementFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h : data.RegimeAttachmentFaceSourceDataFoundationTarget) :
    source.RegimeFacePlacementFoundationTarget :=
  source.regimeFacePlacementFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
    (data.sourceRegimeAttachmentFaceSourceDataFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      source hboundary h)

/--
Canonical aligned chosen source data supplies the full indexed route
consequences.
-/
theorem routeIndexConsequences_of_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h : data.RegimeAttachmentFaceSourceDataFoundationTarget) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
        data.inducedBoundaryGraph :=
  section92Step4CanonicalClosedWalkRegimeFacePlacementFoundationRouteIndexTarget
    data regime source hboundary
    (data.sourceRegimeFacePlacementFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      source hboundary h)

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/-- Repaired aligned chosen attachment-face source-data foundation target. -/
def RegimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    Prop :=
  PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
    data

/--
Repaired aligned chosen source data supplies the source-level chosen
source-data foundation target.
-/
theorem
    sourceRegimeAttachmentFaceSourceDataFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (h : data.RegimeAttachmentFaceSourceDataFoundationTarget) :
    source.RegimeAttachmentFaceSourceDataFoundationTarget := by
  change
    PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
      source.toPlanarBoundaryAnnulusBoundaryData
  simpa [RegimeAttachmentFaceSourceDataFoundationTarget,
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceDataTarget,
    hboundary] using h

/--
Repaired aligned chosen source data supplies the source-level face-placement
foundation target.
-/
theorem sourceRegimeFacePlacementFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (h : data.RegimeAttachmentFaceSourceDataFoundationTarget) :
    source.RegimeFacePlacementFoundationTarget :=
  source.regimeFacePlacementFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
    (data.sourceRegimeAttachmentFaceSourceDataFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      source hboundary h)

/--
Repaired aligned chosen source data supplies the full indexed route
consequences.
-/
theorem routeIndexConsequences_of_regimeAttachmentFaceSourceDataFoundationTarget
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
    (h : data.RegimeAttachmentFaceSourceDataFoundationTarget) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
        data.inducedBoundaryGraph :=
  section92Step4RepairedClosedWalkRegimeFacePlacementFoundationRouteIndexTarget
    data regime source hboundary
    (data.sourceRegimeFacePlacementFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      source hboundary h)

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Source-level source-data foundation route index: chosen source-side
attachment-face data is an equivalent form of the face-placement foundation
target and supplies the downstream source consequences.
-/
def Section92Step4ClosedWalkRegimeAttachmentFaceSourceDataFoundationRouteIndexTarget :
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
      source.RegimeAttachmentFaceSourceDataFoundationTarget →
        source.RegimeFacePlacementFoundationTarget ∧
        source.RegimeAttachmentFaceSourceFoundationTarget ∧
        PeeledCollarSmallCyclicCutLiftsToAmbient G
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/-- Verbatim source-level route index for the chosen source-data foundation target. -/
theorem section92Step4ClosedWalkRegimeAttachmentFaceSourceDataFoundationRouteIndexTarget :
    Section92Step4ClosedWalkRegimeAttachmentFaceSourceDataFoundationRouteIndexTarget := by
  intro V _ G emb source regime h
  have hfoundation :
      source.RegimeFacePlacementFoundationTarget :=
    source.regimeFacePlacementFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      h
  have hconsequences :=
    source.routeIndexConsequences_of_regimeAttachmentFaceSourceDataFoundationTarget
      regime h
  exact
    ⟨hfoundation,
      source.regimeAttachmentFaceSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
        h,
      hconsequences.1,
      hconsequences.2.1,
      hconsequences.2.2.1,
      hconsequences.2.2.2⟩

end Mettapedia.GraphTheory.FourColor
