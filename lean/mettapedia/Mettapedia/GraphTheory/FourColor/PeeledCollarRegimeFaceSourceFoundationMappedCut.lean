import Mettapedia.GraphTheory.FourColor.PeeledCollarMappedCutFaceRouteEquiv

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Source-level noncrossing face-source foundation target for the regime route.
This is the planar-normal-form obligation in the same language as the
off-carrier attachment face-source layer.
-/
def RegimeNoncrossingFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) : Prop :=
  PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
    source.toPlanarBoundaryAnnulusBoundaryData

/--
The named face-placement foundation target is equivalent to the noncrossing
face-source foundation target.
-/
theorem
    regimeFacePlacementFoundationTarget_iff_regimeNoncrossingFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    source.RegimeFacePlacementFoundationTarget ↔
      source.RegimeNoncrossingFaceSourceFoundationTarget := by
  simpa [RegimeFacePlacementFoundationTarget,
    RegimeNoncrossingFaceSourceFoundationTarget] using
    source.facePlacementNoncrossingTarget_iff_noncrossingFaceSourceTarget

/-- Noncrossing face-source data supplies the named face-placement foundation target. -/
theorem regimeFacePlacementFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeNoncrossingFaceSourceFoundationTarget) :
    source.RegimeFacePlacementFoundationTarget :=
  (source.regimeFacePlacementFoundationTarget_iff_regimeNoncrossingFaceSourceFoundationTarget).2
    h

/-- The face-placement foundation target supplies noncrossing face-source data. -/
theorem regimeNoncrossingFaceSourceFoundationTarget_of_regimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeFacePlacementFoundationTarget) :
    source.RegimeNoncrossingFaceSourceFoundationTarget :=
  (source.regimeFacePlacementFoundationTarget_iff_regimeNoncrossingFaceSourceFoundationTarget).1
    h

/--
The noncrossing face-source foundation target is equivalent to the
cut-avoiding face-route target.
-/
theorem regimeNoncrossingFaceSourceFoundationTarget_iff_mappedCutAvoidingFaceRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    source.RegimeNoncrossingFaceSourceFoundationTarget ↔
      source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget :=
  (source.regimeFacePlacementFoundationTarget_iff_regimeNoncrossingFaceSourceFoundationTarget).symm.trans
    source.regimeFacePlacementFoundationTarget_iff_mappedCutAvoidingFaceRouteTarget

/-- Noncrossing face-source data supplies cut-avoiding face routes. -/
theorem mappedCutAvoidingFaceRouteTarget_of_regimeNoncrossingFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeNoncrossingFaceSourceFoundationTarget) :
    source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget :=
  (source.regimeNoncrossingFaceSourceFoundationTarget_iff_mappedCutAvoidingFaceRouteTarget).1
    h

/-- Cut-avoiding face routes supply noncrossing face-source data. -/
theorem regimeNoncrossingFaceSourceFoundationTarget_of_mappedCutAvoidingFaceRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget) :
    source.RegimeNoncrossingFaceSourceFoundationTarget :=
  (source.regimeNoncrossingFaceSourceFoundationTarget_iff_mappedCutAvoidingFaceRouteTarget).2
    h

/-- Noncrossing face-source data supplies chosen attachment-face source data. -/
theorem
    regimeAttachmentFaceSourceDataFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeNoncrossingFaceSourceFoundationTarget) :
    source.RegimeAttachmentFaceSourceDataFoundationTarget :=
  source.regimeAttachmentFaceSourceDataFoundationTarget_of_mappedCutAvoidingFaceRouteTarget
    (source.mappedCutAvoidingFaceRouteTarget_of_regimeNoncrossingFaceSourceFoundationTarget
      h)

/--
Noncrossing face-source data supplies the named equivalent foundation targets,
the mapped-cut face-route target, and all downstream source consequences.
-/
theorem routeIndexConsequences_of_regimeNoncrossingFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h : source.RegimeNoncrossingFaceSourceFoundationTarget) :
    source.RegimeAttachmentFaceSourceDataFoundationTarget ∧
      source.RegimeFacePlacementFoundationTarget ∧
      source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget ∧
      PeeledCollarSmallCyclicCutLiftsToAmbient G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      CyclicallyFiveEdgeConnected
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph := by
  have hmapped :
      source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget :=
    source.mappedCutAvoidingFaceRouteTarget_of_regimeNoncrossingFaceSourceFoundationTarget
      h
  have hconsequences :=
    source.routeIndexConsequences_of_mappedCutAvoidingFaceRouteTarget
      regime hmapped
  exact
    ⟨source.regimeAttachmentFaceSourceDataFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
        h,
      source.regimeFacePlacementFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
        h,
      hmapped,
      hconsequences.2.1,
      hconsequences.2.2.1,
      hconsequences.2.2.2.1,
      hconsequences.2.2.2.2⟩

end PlanarBoundaryClosedWalkAnnulusBoundarySource

namespace PlanarBoundaryAnnulusCollarGeometry

/-- Canonical aligned noncrossing face-source foundation target. -/
def RegimeNoncrossingFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
    data

/--
Canonical aligned noncrossing face-source data supplies the source-level
foundation target.
-/
theorem
    sourceRegimeNoncrossingFaceSourceFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h : data.RegimeNoncrossingFaceSourceFoundationTarget) :
    source.RegimeNoncrossingFaceSourceFoundationTarget := by
  change
    PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
      source.toPlanarBoundaryAnnulusBoundaryData
  simpa [RegimeNoncrossingFaceSourceFoundationTarget,
    PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget,
    hboundary] using h

/--
Canonical aligned noncrossing face-source data supplies the full indexed
canonical route consequences.
-/
theorem routeIndexConsequences_of_regimeNoncrossingFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h : data.RegimeNoncrossingFaceSourceFoundationTarget) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
        data.inducedBoundaryGraph :=
  section92Step4CanonicalClosedWalkRegimeFacePlacementFoundationRouteIndexTarget
    data regime source hboundary
    (source.regimeFacePlacementFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
      (data.sourceRegimeNoncrossingFaceSourceFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
        source hboundary h))

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/-- Repaired aligned noncrossing face-source foundation target. -/
def RegimeNoncrossingFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    Prop :=
  PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
    data

/--
Repaired aligned noncrossing face-source data supplies the source-level
foundation target.
-/
theorem
    sourceRegimeNoncrossingFaceSourceFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (h : data.RegimeNoncrossingFaceSourceFoundationTarget) :
    source.RegimeNoncrossingFaceSourceFoundationTarget := by
  change
    PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
      source.toPlanarBoundaryAnnulusBoundaryData
  simpa [RegimeNoncrossingFaceSourceFoundationTarget,
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget,
    hboundary] using h

/--
Repaired aligned noncrossing face-source data supplies the full indexed
repaired route consequences.
-/
theorem routeIndexConsequences_of_regimeNoncrossingFaceSourceFoundationTarget
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
    (h : data.RegimeNoncrossingFaceSourceFoundationTarget) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
        data.inducedBoundaryGraph :=
  section92Step4RepairedClosedWalkRegimeFacePlacementFoundationRouteIndexTarget
    data regime source hboundary
    (source.regimeFacePlacementFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
      (data.sourceRegimeNoncrossingFaceSourceFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
        source hboundary h))

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Source-level noncrossing face-source route index: the face-source obligation
is equivalent to the mapped-cut face-route target and supplies the downstream
source consequences.
-/
def Section92Step4ClosedWalkRegimeNoncrossingFaceSourceFoundationRouteIndexTarget :
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
      source.RegimeNoncrossingFaceSourceFoundationTarget →
        source.RegimeAttachmentFaceSourceDataFoundationTarget ∧
        source.RegimeFacePlacementFoundationTarget ∧
        source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget ∧
        PeeledCollarSmallCyclicCutLiftsToAmbient G
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/-- Verbatim source-level route index for the noncrossing face-source foundation target. -/
theorem section92Step4ClosedWalkRegimeNoncrossingFaceSourceFoundationRouteIndexTarget :
    Section92Step4ClosedWalkRegimeNoncrossingFaceSourceFoundationRouteIndexTarget := by
  intro V _ G emb source regime h
  exact
    source.routeIndexConsequences_of_regimeNoncrossingFaceSourceFoundationTarget
      regime h

end Mettapedia.GraphTheory.FourColor
