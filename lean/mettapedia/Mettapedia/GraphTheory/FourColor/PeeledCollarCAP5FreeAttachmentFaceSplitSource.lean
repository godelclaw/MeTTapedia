import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeSelectedBoundaryArcSource
import Mettapedia.GraphTheory.FourColor.PeeledCollarAttachmentFaceSourceSplitConnectivity

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Split attachment-face source bridges for the CAP5-free peeled-collar route.

This layer separates the selected-boundary-arc source obligation into the two
planar-normal-form pieces already present in the tree: attachment-face
placement and the face noncrossing upgrade.  The module proves that their
conjunction feeds the selected-boundary-arc, source-data, off-boundary, and S4
interfaces.
-/

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Source-level split foundation target: attachment-face placements plus the
face noncrossing upgrade for every small cyclic carrier cut.
-/
def RegimeAttachmentFaceSplitSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) : Prop :=
  PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceTarget
      source.toPlanarBoundaryAnnulusBoundaryData ∧
    PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget
      source.toPlanarBoundaryAnnulusBoundaryData

/--
The split source target supplies selected-boundary-arc source witnesses for a
closed-walk annulus source.
-/
theorem regimeSelectedBoundaryArcSourceFoundationTarget_of_regimeAttachmentFaceSplitSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeAttachmentFaceSplitSourceFoundationTarget) :
    source.RegimeSelectedBoundaryArcSourceFoundationTarget :=
  source.toPlanarBoundaryAnnulusBoundaryData
    |>.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_selectedBoundaryArcGeometry_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      source.toPlanarBoundarySelectedBoundaryArcGeometry h.1 h.2

/--
The split source target supplies chosen source data.
-/
theorem regimeAttachmentFaceSourceDataFoundationTarget_of_regimeAttachmentFaceSplitSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeAttachmentFaceSplitSourceFoundationTarget) :
    source.RegimeAttachmentFaceSourceDataFoundationTarget :=
  source.regimeAttachmentFaceSourceDataFoundationTarget_of_regimeSelectedBoundaryArcSourceFoundationTarget
    (source.regimeSelectedBoundaryArcSourceFoundationTarget_of_regimeAttachmentFaceSplitSourceFoundationTarget
      h)

/--
The split source target supplies noncrossing face-source data.
-/
theorem regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSplitSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeAttachmentFaceSplitSourceFoundationTarget) :
    source.RegimeNoncrossingFaceSourceFoundationTarget :=
  source.regimeNoncrossingFaceSourceFoundationTarget_of_regimeSelectedBoundaryArcSourceFoundationTarget
    (source.regimeSelectedBoundaryArcSourceFoundationTarget_of_regimeAttachmentFaceSplitSourceFoundationTarget
      h)

/--
Split source data supplies selected-boundary-arc source witnesses, chosen
source data, noncrossing face-source data, off-boundary no-crossing, local
constancy, separation, the small-cut lift, cyclic five-edge-connectivity, no
cyclic two-cut, and S4 no-escape.
-/
theorem routeIndexConsequences_of_regimeAttachmentFaceSplitSourceOffBoundaryTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h : source.RegimeAttachmentFaceSplitSourceFoundationTarget) :
    source.RegimeSelectedBoundaryArcSourceFoundationTarget ∧
      source.RegimeAttachmentFaceSourceDataFoundationTarget ∧
      source.RegimeNoncrossingFaceSourceFoundationTarget ∧
      PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
      PeeledCollarCutAmbientSideLocalConstanciesToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
      PeeledCollarCutAmbientSideSeparationsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
      PeeledCollarSmallCyclicCutLiftsToAmbient G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      CyclicallyFiveEdgeConnected
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph := by
  have hselected :
      source.RegimeSelectedBoundaryArcSourceFoundationTarget :=
    source.regimeSelectedBoundaryArcSourceFoundationTarget_of_regimeAttachmentFaceSplitSourceFoundationTarget
      h
  have hconsequences :=
    source.routeIndexConsequences_of_regimeSelectedBoundaryArcSourceOffBoundaryTarget
      regime hselected
  exact
    ⟨hselected,
      hconsequences.1,
      hconsequences.2.1,
      hconsequences.2.2.1,
      hconsequences.2.2.2.1,
      hconsequences.2.2.2.2.1,
      hconsequences.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2.2.2⟩

end PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Closed-walk split-source foundation target: the CAP5-free regime supplies the
two planar split obligations for every closed-walk boundary source.
-/
def CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      source.RegimeAttachmentFaceSplitSourceFoundationTarget

/--
The closed-walk CAP5-free split-source target supplies the closed-walk
selected-boundary-arc target.
-/
theorem cap5FreeClosedWalkSelectedBoundaryArcSourceFoundationTarget_of_attachmentFaceSplitSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarSelectedBoundaryArcSourceFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.regimeSelectedBoundaryArcSourceFoundationTarget_of_regimeAttachmentFaceSplitSourceFoundationTarget
      (hfoundation source regime)

/--
The closed-walk CAP5-free split-source target supplies the closed-walk
source-data target.
-/
theorem cap5FreeClosedWalkAttachmentFaceSourceDataFoundationTarget_of_attachmentFaceSplitSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarAttachmentFaceSourceDataFoundationTarget :=
  cap5FreeClosedWalkAttachmentFaceSourceDataFoundationTarget_of_selectedBoundaryArcSourceFoundationTarget
    (cap5FreeClosedWalkSelectedBoundaryArcSourceFoundationTarget_of_attachmentFaceSplitSourceFoundationTarget
      hfoundation)

namespace PlanarBoundaryAnnulusCollarGeometry

/--
Canonical aligned split-source foundation target.
-/
def RegimeAttachmentFaceSplitSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceTarget data ∧
    PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget data

/-- Canonical split-source data supplies selected-boundary-arc source witnesses. -/
theorem regimeSelectedBoundaryArcSourceFoundationTarget_of_regimeAttachmentFaceSplitSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_ :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h : data.RegimeAttachmentFaceSplitSourceFoundationTarget) :
    data.RegimeSelectedBoundaryArcSourceFoundationTarget :=
  data.boundaryData
    |>.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_selectedBoundaryArcGeometry_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      source.toPlanarBoundarySelectedBoundaryArcGeometry h.1 h.2

/-- Canonical split-source data supplies chosen source data. -/
theorem regimeAttachmentFaceSourceDataFoundationTarget_of_regimeAttachmentFaceSplitSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h : data.RegimeAttachmentFaceSplitSourceFoundationTarget) :
    data.RegimeAttachmentFaceSourceDataFoundationTarget :=
  data.regimeAttachmentFaceSourceDataFoundationTarget_of_regimeSelectedBoundaryArcSourceFoundationTarget
    (data.regimeSelectedBoundaryArcSourceFoundationTarget_of_regimeAttachmentFaceSplitSourceFoundationTarget
      source hboundary h)

/--
The closed-walk CAP5-free split-source target supplies the aligned canonical
split-source target.
-/
theorem regimeAttachmentFaceSplitSourceFoundationTarget_of_cap5FreeClosedWalkAttachmentFaceSplitSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget)
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph) :
    data.RegimeAttachmentFaceSplitSourceFoundationTarget := by
  have hsource :
      source.RegimeAttachmentFaceSplitSourceFoundationTarget :=
    hfoundation source
      (data.sourceRegime_of_boundaryData_eq source hboundary regime)
  constructor
  · simpa [RegimeAttachmentFaceSplitSourceFoundationTarget,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.RegimeAttachmentFaceSplitSourceFoundationTarget,
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceTarget,
      hboundary] using hsource.1
  · simpa [RegimeAttachmentFaceSplitSourceFoundationTarget,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.RegimeAttachmentFaceSplitSourceFoundationTarget,
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget,
      hboundary] using hsource.2

/--
The closed-walk CAP5-free split-source target supplies canonical split-source
data, selected-boundary-arc source witnesses, source data, face-source data,
off-boundary no-crossing, local constancy, separation, the small-cut lift,
cyclic five-edge-connectivity, no cyclic two-cut, and S4 no-escape.
-/
theorem routeIndexConsequences_of_cap5FreeClosedWalkAttachmentFaceSplitSourceOffBoundaryTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget)
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData) :
    data.RegimeAttachmentFaceSplitSourceFoundationTarget ∧
      data.RegimeSelectedBoundaryArcSourceFoundationTarget ∧
      data.RegimeAttachmentFaceSourceDataFoundationTarget ∧
      data.RegimeNoncrossingFaceSourceFoundationTarget ∧
      PlanarBoundaryAnnulusPeeledCollarOffBoundaryNoCrossingTarget
        data data.inducedBoundaryEmbedding ∧
      PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget
        data data.inducedBoundaryEmbedding ∧
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding ∧
      PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph ∧
      CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
        data.inducedBoundaryGraph := by
  have hsplit :
      data.RegimeAttachmentFaceSplitSourceFoundationTarget :=
    data.regimeAttachmentFaceSplitSourceFoundationTarget_of_cap5FreeClosedWalkAttachmentFaceSplitSourceFoundationTarget
      hfoundation source hboundary regime
  have hselectedFoundation :
      CAP5FreeClosedWalkPeeledCollarSelectedBoundaryArcSourceFoundationTarget :=
    cap5FreeClosedWalkSelectedBoundaryArcSourceFoundationTarget_of_attachmentFaceSplitSourceFoundationTarget
      hfoundation
  have hconsequences :=
    data.routeIndexConsequences_of_cap5FreeClosedWalkSelectedBoundaryArcSourceOffBoundaryTarget
      hselectedFoundation regime source hboundary
  exact
    ⟨hsplit,
      hconsequences.1,
      hconsequences.2.1,
      hconsequences.2.2.1,
      hconsequences.2.2.2.1,
      hconsequences.2.2.2.2.1,
      hconsequences.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2.2.2.2⟩

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Repaired aligned split-source foundation target.
-/
def RegimeAttachmentFaceSplitSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    Prop :=
  PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceTarget data ∧
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget data

/-- Repaired split-source data supplies selected-boundary-arc source witnesses. -/
theorem regimeSelectedBoundaryArcSourceFoundationTarget_of_regimeAttachmentFaceSplitSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_ :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (h : data.RegimeAttachmentFaceSplitSourceFoundationTarget) :
    data.RegimeSelectedBoundaryArcSourceFoundationTarget :=
  data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData
    |>.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_selectedBoundaryArcGeometry_of_attachmentFaceSourceTarget_of_faceNoncrossingUpgradeTarget
      source.toPlanarBoundarySelectedBoundaryArcGeometry h.1 h.2

/-- Repaired split-source data supplies chosen source data. -/
theorem regimeAttachmentFaceSourceDataFoundationTarget_of_regimeAttachmentFaceSplitSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (h : data.RegimeAttachmentFaceSplitSourceFoundationTarget) :
    data.RegimeAttachmentFaceSourceDataFoundationTarget :=
  data.regimeAttachmentFaceSourceDataFoundationTarget_of_regimeSelectedBoundaryArcSourceFoundationTarget
    (data.regimeSelectedBoundaryArcSourceFoundationTarget_of_regimeAttachmentFaceSplitSourceFoundationTarget
      source hboundary h)

/--
The closed-walk CAP5-free split-source target supplies the aligned repaired
split-source target.
-/
theorem regimeAttachmentFaceSplitSourceFoundationTarget_of_cap5FreeClosedWalkAttachmentFaceSplitSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget)
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph) :
    data.RegimeAttachmentFaceSplitSourceFoundationTarget := by
  have hsource :
      source.RegimeAttachmentFaceSplitSourceFoundationTarget :=
    hfoundation source
      (data.sourceRegime_of_boundaryData_eq source hboundary regime)
  constructor
  · simpa [RegimeAttachmentFaceSplitSourceFoundationTarget,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.RegimeAttachmentFaceSplitSourceFoundationTarget,
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceTarget,
      PlanarBoundaryAnnulusCollarGeometry.boundaryData,
      hboundary] using hsource.1
  · simpa [RegimeAttachmentFaceSplitSourceFoundationTarget,
      PlanarBoundaryClosedWalkAnnulusBoundarySource.RegimeAttachmentFaceSplitSourceFoundationTarget,
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceNoncrossingUpgradeTarget,
      PlanarBoundaryAnnulusCollarGeometry.boundaryData,
      hboundary] using hsource.2

/--
The closed-walk CAP5-free split-source target supplies repaired split-source
data, selected-boundary-arc source witnesses, source data, face-source data,
off-boundary no-crossing, local constancy, separation, the small-cut lift,
cyclic five-edge-connectivity, no cyclic two-cut, and S4 no-escape.
-/
theorem routeIndexConsequences_of_cap5FreeClosedWalkAttachmentFaceSplitSourceOffBoundaryTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget)
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData) :
    data.RegimeAttachmentFaceSplitSourceFoundationTarget ∧
      data.RegimeSelectedBoundaryArcSourceFoundationTarget ∧
      data.RegimeAttachmentFaceSourceDataFoundationTarget ∧
      data.RegimeNoncrossingFaceSourceFoundationTarget ∧
      PlanarBoundaryPreviousBoundaryPeeledCollarOffBoundaryNoCrossingTarget
        data data.inducedBoundaryEmbedding ∧
      PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget
        data data.inducedBoundaryEmbedding ∧
      PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding ∧
      PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph ∧
      CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
        data.inducedBoundaryGraph := by
  have hsplit :
      data.RegimeAttachmentFaceSplitSourceFoundationTarget :=
    data.regimeAttachmentFaceSplitSourceFoundationTarget_of_cap5FreeClosedWalkAttachmentFaceSplitSourceFoundationTarget
      hfoundation source hboundary regime
  have hselectedFoundation :
      CAP5FreeClosedWalkPeeledCollarSelectedBoundaryArcSourceFoundationTarget :=
    cap5FreeClosedWalkSelectedBoundaryArcSourceFoundationTarget_of_attachmentFaceSplitSourceFoundationTarget
      hfoundation
  have hconsequences :=
    data.routeIndexConsequences_of_cap5FreeClosedWalkSelectedBoundaryArcSourceOffBoundaryTarget
      hselectedFoundation regime source hboundary
  exact
    ⟨hsplit,
      hconsequences.1,
      hconsequences.2.1,
      hconsequences.2.2.1,
      hconsequences.2.2.2.1,
      hconsequences.2.2.2.2.1,
      hconsequences.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2.2.2.2⟩

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Closed-walk split-source CAP5-free off-boundary route index.
-/
def Section92Step4ClosedWalkCAP5FreeAttachmentFaceSplitSourceOffBoundaryRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
        source.RegimeAttachmentFaceSplitSourceFoundationTarget ∧
        source.RegimeSelectedBoundaryArcSourceFoundationTarget ∧
        source.RegimeAttachmentFaceSourceDataFoundationTarget ∧
        source.RegimeNoncrossingFaceSourceFoundationTarget ∧
        PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
        PeeledCollarCutAmbientSideLocalConstanciesToAmbient
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
        PeeledCollarCutAmbientSideSeparationsToAmbient
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
        PeeledCollarSmallCyclicCutLiftsToAmbient G
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/-- Route-index theorem for the closed-walk split-source target. -/
theorem section92Step4ClosedWalkCAP5FreeAttachmentFaceSplitSourceOffBoundaryRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeAttachmentFaceSplitSourceOffBoundaryRouteIndexTarget := by
  intro V _ G emb source regime
  have hsplit :
      source.RegimeAttachmentFaceSplitSourceFoundationTarget :=
    hfoundation source regime
  have hconsequences :=
    source.routeIndexConsequences_of_regimeAttachmentFaceSplitSourceOffBoundaryTarget
      regime hsplit
  exact
    ⟨hsplit,
      hconsequences.1,
      hconsequences.2.1,
      hconsequences.2.2.1,
      hconsequences.2.2.2.1,
      hconsequences.2.2.2.2.1,
      hconsequences.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2.2.2.2⟩

/--
Canonical annulus CAP5-free split-source/off-boundary route index.
-/
def
    Section92Step4CanonicalAnnulusCAP5FreeAttachmentFaceSplitSourceOffBoundaryRouteIndexTarget :
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
        data.RegimeAttachmentFaceSplitSourceFoundationTarget ∧
        data.RegimeSelectedBoundaryArcSourceFoundationTarget ∧
        data.RegimeAttachmentFaceSourceDataFoundationTarget ∧
        data.RegimeNoncrossingFaceSourceFoundationTarget ∧
        PlanarBoundaryAnnulusPeeledCollarOffBoundaryNoCrossingTarget
          data data.inducedBoundaryEmbedding ∧
        PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget
          data data.inducedBoundaryEmbedding ∧
        PlanarBoundaryAnnulusPeeledCollarSeparationTarget
          data data.inducedBoundaryEmbedding ∧
        PeeledCollarSmallCyclicCutLiftsToAmbient G
          data.inducedBoundaryGraph ∧
        CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          data.inducedBoundaryGraph

/-- Route-index theorem for the canonical split-source target. -/
theorem
    section92Step4CanonicalAnnulusCAP5FreeAttachmentFaceSplitSourceOffBoundaryRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget) :
    Section92Step4CanonicalAnnulusCAP5FreeAttachmentFaceSplitSourceOffBoundaryRouteIndexTarget := by
  intro V _ G emb data regime source hboundary
  exact
    PlanarBoundaryAnnulusCollarGeometry.routeIndexConsequences_of_cap5FreeClosedWalkAttachmentFaceSplitSourceOffBoundaryTarget
      hfoundation data regime source hboundary

/--
Repaired annulus CAP5-free split-source/off-boundary route index.
-/
def
    Section92Step4RepairedAnnulusCAP5FreeAttachmentFaceSplitSourceOffBoundaryRouteIndexTarget :
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
        data.RegimeAttachmentFaceSplitSourceFoundationTarget ∧
        data.RegimeSelectedBoundaryArcSourceFoundationTarget ∧
        data.RegimeAttachmentFaceSourceDataFoundationTarget ∧
        data.RegimeNoncrossingFaceSourceFoundationTarget ∧
        PlanarBoundaryPreviousBoundaryPeeledCollarOffBoundaryNoCrossingTarget
          data data.inducedBoundaryEmbedding ∧
        PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget
          data data.inducedBoundaryEmbedding ∧
        PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
          data data.inducedBoundaryEmbedding ∧
        PeeledCollarSmallCyclicCutLiftsToAmbient G
          data.inducedBoundaryGraph ∧
        CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          data.inducedBoundaryGraph

/-- Route-index theorem for the repaired split-source target. -/
theorem
    section92Step4RepairedAnnulusCAP5FreeAttachmentFaceSplitSourceOffBoundaryRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSplitSourceFoundationTarget) :
    Section92Step4RepairedAnnulusCAP5FreeAttachmentFaceSplitSourceOffBoundaryRouteIndexTarget := by
  intro V _ G emb data regime source hboundary
  exact
    PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry.routeIndexConsequences_of_cap5FreeClosedWalkAttachmentFaceSplitSourceOffBoundaryTarget
      hfoundation data regime source hboundary

end Mettapedia.GraphTheory.FourColor
