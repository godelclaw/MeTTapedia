import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeFoundationEquiv

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Selected-boundary-arc source bridges for the CAP5-free peeled-collar route.

The selected-boundary-arc source target is the face-local form that records
the selected boundary arc on each witness face.  For closed-walk annulus
sources, this is equivalent to the chosen source-data foundation target because
the source carries the selected-boundary arc geometry.
-/

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Source-level selected-boundary-arc foundation target for the regime route.
This is the face-local normal-form obligation with the selected arc recorded.
-/
def RegimeSelectedBoundaryArcSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) : Prop :=
  PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
    source.toPlanarBoundaryAnnulusBoundaryData

/--
Selected-boundary-arc source witnesses forget to chosen attachment-face
source data.
-/
theorem regimeAttachmentFaceSourceDataFoundationTarget_of_regimeSelectedBoundaryArcSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeSelectedBoundaryArcSourceFoundationTarget) :
    source.RegimeAttachmentFaceSourceDataFoundationTarget :=
  source.toPlanarBoundaryAnnulusBoundaryData
    |>.attachmentFaceSourceDataTarget_of_noncrossingSelectedBoundaryArcSourceTarget h

/--
Chosen attachment-face source data supplies selected-boundary-arc source
witnesses for closed-walk annulus sources.
-/
theorem regimeSelectedBoundaryArcSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeAttachmentFaceSourceDataFoundationTarget) :
    source.RegimeSelectedBoundaryArcSourceFoundationTarget :=
  source.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_faceSourceTarget
    (source.toPlanarBoundaryAnnulusBoundaryData
      |>.attachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceDataTarget h)

/--
For closed-walk annulus sources, selected-boundary-arc witnesses and chosen
source data are equivalent foundation interfaces.
-/
theorem regimeSelectedBoundaryArcSourceFoundationTarget_iff_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    source.RegimeSelectedBoundaryArcSourceFoundationTarget ↔
      source.RegimeAttachmentFaceSourceDataFoundationTarget :=
  ⟨source.regimeAttachmentFaceSourceDataFoundationTarget_of_regimeSelectedBoundaryArcSourceFoundationTarget,
    source.regimeSelectedBoundaryArcSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget⟩

/--
Selected-boundary-arc source witnesses supply noncrossing face-source data.
-/
theorem regimeNoncrossingFaceSourceFoundationTarget_of_regimeSelectedBoundaryArcSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeSelectedBoundaryArcSourceFoundationTarget) :
    source.RegimeNoncrossingFaceSourceFoundationTarget :=
  source.regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
    (source.regimeAttachmentFaceSourceDataFoundationTarget_of_regimeSelectedBoundaryArcSourceFoundationTarget
      h)

/--
Selected-boundary-arc source witnesses supply selected data, source data,
noncrossing face-source data, off-boundary no-crossing, local constancy,
separation, the small-cut lift, cyclic five-edge-connectivity, no cyclic
two-cut, and S4 no-escape.
-/
theorem routeIndexConsequences_of_regimeSelectedBoundaryArcSourceOffBoundaryTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h : source.RegimeSelectedBoundaryArcSourceFoundationTarget) :
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
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph := by
  have hsourceData :
      source.RegimeAttachmentFaceSourceDataFoundationTarget :=
    source.regimeAttachmentFaceSourceDataFoundationTarget_of_regimeSelectedBoundaryArcSourceFoundationTarget
      h
  have hconsequences :=
    source.routeIndexConsequences_of_regimeAttachmentFaceSourceDataOffBoundaryTarget
      regime hsourceData
  exact
    ⟨hsourceData,
      hconsequences.1,
      hconsequences.2.1,
      hconsequences.2.2.1,
      hconsequences.2.2.2.1,
      hconsequences.2.2.2.2.1,
      hconsequences.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2.2⟩

end PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Closed-walk selected-boundary-arc foundation target: the CAP5-free regime
supplies selected-boundary-arc source witnesses for every small cyclic carrier
cut of the closed-walk boundary source.
-/
def CAP5FreeClosedWalkPeeledCollarSelectedBoundaryArcSourceFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      source.RegimeSelectedBoundaryArcSourceFoundationTarget

/--
The closed-walk CAP5-free selected-boundary-arc target supplies the
closed-walk source-data target.
-/
theorem cap5FreeClosedWalkAttachmentFaceSourceDataFoundationTarget_of_selectedBoundaryArcSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarSelectedBoundaryArcSourceFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarAttachmentFaceSourceDataFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.regimeAttachmentFaceSourceDataFoundationTarget_of_regimeSelectedBoundaryArcSourceFoundationTarget
      (hfoundation source regime)

/--
The closed-walk CAP5-free source-data target supplies the closed-walk
selected-boundary-arc source target.
-/
theorem cap5FreeClosedWalkSelectedBoundaryArcSourceFoundationTarget_of_attachmentFaceSourceDataFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSourceDataFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarSelectedBoundaryArcSourceFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.regimeSelectedBoundaryArcSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      (hfoundation source regime)

/--
Closed-walk CAP5-free selected-boundary-arc and source-data targets are
equivalent.
-/
theorem cap5FreeClosedWalkSelectedBoundaryArcSourceFoundationTarget_iff_attachmentFaceSourceDataFoundationTarget :
    CAP5FreeClosedWalkPeeledCollarSelectedBoundaryArcSourceFoundationTarget ↔
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSourceDataFoundationTarget :=
  ⟨cap5FreeClosedWalkAttachmentFaceSourceDataFoundationTarget_of_selectedBoundaryArcSourceFoundationTarget,
    cap5FreeClosedWalkSelectedBoundaryArcSourceFoundationTarget_of_attachmentFaceSourceDataFoundationTarget⟩

namespace PlanarBoundaryAnnulusCollarGeometry

/-- Canonical aligned selected-boundary-arc source foundation target. -/
def RegimeSelectedBoundaryArcSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
    data

/-- Canonical selected-boundary-arc source witnesses forget to source data. -/
theorem regimeAttachmentFaceSourceDataFoundationTarget_of_regimeSelectedBoundaryArcSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (h : data.RegimeSelectedBoundaryArcSourceFoundationTarget) :
    data.RegimeAttachmentFaceSourceDataFoundationTarget :=
  planarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceDataTarget_of_noncrossingSelectedBoundaryArcSourceTarget
    h

/--
Canonical source data supplies selected-boundary-arc source witnesses when
aligned with a closed-walk boundary source.
-/
theorem regimeSelectedBoundaryArcSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h : data.RegimeAttachmentFaceSourceDataFoundationTarget) :
    data.RegimeSelectedBoundaryArcSourceFoundationTarget :=
  data.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_closedWalkAnnulusBoundarySource_faceSourceTarget
    source hboundary
    (source.regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      (data.sourceRegimeAttachmentFaceSourceDataFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
        source hboundary h))

/--
Canonical aligned source data and selected-boundary-arc source witnesses are
equivalent for a fixed closed-walk boundary source.
-/
theorem regimeSelectedBoundaryArcSourceFoundationTarget_iff_regimeAttachmentFaceSourceDataFoundationTarget_of_source
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData) :
    data.RegimeSelectedBoundaryArcSourceFoundationTarget ↔
      data.RegimeAttachmentFaceSourceDataFoundationTarget :=
  ⟨data.regimeAttachmentFaceSourceDataFoundationTarget_of_regimeSelectedBoundaryArcSourceFoundationTarget,
    data.regimeSelectedBoundaryArcSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      source hboundary⟩

/--
The closed-walk CAP5-free selected-boundary-arc theorem supplies the aligned
canonical selected-boundary-arc target.
-/
theorem regimeSelectedBoundaryArcSourceFoundationTarget_of_cap5FreeClosedWalkSelectedBoundaryArcSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarSelectedBoundaryArcSourceFoundationTarget)
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph) :
    data.RegimeSelectedBoundaryArcSourceFoundationTarget := by
  change PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
    data
  change data.boundaryData.PeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
  simpa [
    PlanarBoundaryClosedWalkAnnulusBoundarySource.RegimeSelectedBoundaryArcSourceFoundationTarget,
    hboundary] using
    hfoundation source
      (data.sourceRegime_of_boundaryData_eq source hboundary regime)

/--
The closed-walk CAP5-free selected-boundary-arc theorem supplies canonical
selected data, source data, face-source data, off-boundary no-crossing, local
constancy, separation, the small-cut lift, cyclic five-edge-connectivity, no
cyclic two-cut, and S4 no-escape.
-/
theorem routeIndexConsequences_of_cap5FreeClosedWalkSelectedBoundaryArcSourceOffBoundaryTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarSelectedBoundaryArcSourceFoundationTarget)
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData) :
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
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
        data.inducedBoundaryGraph := by
  have hselected :
      data.RegimeSelectedBoundaryArcSourceFoundationTarget :=
    data.regimeSelectedBoundaryArcSourceFoundationTarget_of_cap5FreeClosedWalkSelectedBoundaryArcSourceFoundationTarget
      hfoundation source hboundary regime
  have hsourceDataFoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSourceDataFoundationTarget :=
    cap5FreeClosedWalkAttachmentFaceSourceDataFoundationTarget_of_selectedBoundaryArcSourceFoundationTarget
      hfoundation
  have hconsequences :=
    data.routeIndexConsequences_of_cap5FreeClosedWalkAttachmentFaceSourceDataOffBoundaryTarget
      hsourceDataFoundation regime source hboundary
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

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/-- Repaired aligned selected-boundary-arc source foundation target. -/
def RegimeSelectedBoundaryArcSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    Prop :=
  PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
    data

/-- Repaired selected-boundary-arc source witnesses forget to source data. -/
theorem regimeAttachmentFaceSourceDataFoundationTarget_of_regimeSelectedBoundaryArcSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (h : data.RegimeSelectedBoundaryArcSourceFoundationTarget) :
    data.RegimeAttachmentFaceSourceDataFoundationTarget :=
  planarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceDataTarget_of_noncrossingSelectedBoundaryArcSourceTarget
    h

/--
Repaired source data supplies selected-boundary-arc source witnesses when
aligned with a closed-walk boundary source.
-/
theorem regimeSelectedBoundaryArcSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (h : data.RegimeAttachmentFaceSourceDataFoundationTarget) :
    data.RegimeSelectedBoundaryArcSourceFoundationTarget :=
  data.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_closedWalkAnnulusBoundarySource_faceSourceTarget
    source hboundary
    (source.regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      (data.sourceRegimeAttachmentFaceSourceDataFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
        source hboundary h))

/--
Repaired aligned source data and selected-boundary-arc source witnesses are
equivalent for a fixed closed-walk boundary source.
-/
theorem regimeSelectedBoundaryArcSourceFoundationTarget_iff_regimeAttachmentFaceSourceDataFoundationTarget_of_source
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData) :
    data.RegimeSelectedBoundaryArcSourceFoundationTarget ↔
      data.RegimeAttachmentFaceSourceDataFoundationTarget :=
  ⟨data.regimeAttachmentFaceSourceDataFoundationTarget_of_regimeSelectedBoundaryArcSourceFoundationTarget,
    data.regimeSelectedBoundaryArcSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      source hboundary⟩

/--
The closed-walk CAP5-free selected-boundary-arc theorem supplies the aligned
repaired selected-boundary-arc target.
-/
theorem regimeSelectedBoundaryArcSourceFoundationTarget_of_cap5FreeClosedWalkSelectedBoundaryArcSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarSelectedBoundaryArcSourceFoundationTarget)
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
    data.RegimeSelectedBoundaryArcSourceFoundationTarget := by
  change
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
      data
  change
    data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData
      |>.PeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget
  simpa [
    PlanarBoundaryClosedWalkAnnulusBoundarySource.RegimeSelectedBoundaryArcSourceFoundationTarget,
    hboundary] using
    hfoundation source
      (data.sourceRegime_of_boundaryData_eq source hboundary regime)

/--
The closed-walk CAP5-free selected-boundary-arc theorem supplies repaired
selected data, source data, face-source data, off-boundary no-crossing, local
constancy, separation, the small-cut lift, cyclic five-edge-connectivity, no
cyclic two-cut, and S4 no-escape.
-/
theorem routeIndexConsequences_of_cap5FreeClosedWalkSelectedBoundaryArcSourceOffBoundaryTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarSelectedBoundaryArcSourceFoundationTarget)
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
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
        data.inducedBoundaryGraph := by
  have hselected :
      data.RegimeSelectedBoundaryArcSourceFoundationTarget :=
    data.regimeSelectedBoundaryArcSourceFoundationTarget_of_cap5FreeClosedWalkSelectedBoundaryArcSourceFoundationTarget
      hfoundation source hboundary regime
  have hsourceDataFoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSourceDataFoundationTarget :=
    cap5FreeClosedWalkAttachmentFaceSourceDataFoundationTarget_of_selectedBoundaryArcSourceFoundationTarget
      hfoundation
  have hconsequences :=
    data.routeIndexConsequences_of_cap5FreeClosedWalkAttachmentFaceSourceDataOffBoundaryTarget
      hsourceDataFoundation regime source hboundary
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

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Canonical aligned selected-boundary-arc foundation target, with boundary-data
alignment stated explicitly.
-/
def CAP5FreeCanonicalAnnulusPeeledCollarSelectedBoundaryArcSourceFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData →
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph →
      data.RegimeSelectedBoundaryArcSourceFoundationTarget

/--
Repaired aligned selected-boundary-arc foundation target, with boundary-data
alignment stated explicitly.
-/
def CAP5FreeRepairedAnnulusPeeledCollarSelectedBoundaryArcSourceFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData →
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph →
      data.RegimeSelectedBoundaryArcSourceFoundationTarget

/--
The closed-walk selected-boundary-arc target supplies the canonical aligned
selected-boundary-arc target.
-/
theorem cap5FreeCanonicalAnnulusSelectedBoundaryArcSourceFoundationTarget_of_closedWalkSelectedBoundaryArcSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarSelectedBoundaryArcSourceFoundationTarget) :
    CAP5FreeCanonicalAnnulusPeeledCollarSelectedBoundaryArcSourceFoundationTarget := by
  intro V _ G emb data source hboundary regime
  exact
    data.regimeSelectedBoundaryArcSourceFoundationTarget_of_cap5FreeClosedWalkSelectedBoundaryArcSourceFoundationTarget
      hfoundation source hboundary regime

/--
The closed-walk selected-boundary-arc target supplies the repaired aligned
selected-boundary-arc target.
-/
theorem cap5FreeRepairedAnnulusSelectedBoundaryArcSourceFoundationTarget_of_closedWalkSelectedBoundaryArcSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarSelectedBoundaryArcSourceFoundationTarget) :
    CAP5FreeRepairedAnnulusPeeledCollarSelectedBoundaryArcSourceFoundationTarget := by
  intro V _ G emb data source hboundary regime
  exact
    data.regimeSelectedBoundaryArcSourceFoundationTarget_of_cap5FreeClosedWalkSelectedBoundaryArcSourceFoundationTarget
      hfoundation source hboundary regime

/--
The canonical selected-boundary-arc target supplies the canonical source-data
target.
-/
theorem cap5FreeCanonicalAnnulusAttachmentFaceSourceDataFoundationTarget_of_selectedBoundaryArcSourceFoundationTarget
    (hfoundation :
      CAP5FreeCanonicalAnnulusPeeledCollarSelectedBoundaryArcSourceFoundationTarget) :
    CAP5FreeCanonicalAnnulusPeeledCollarAttachmentFaceSourceDataFoundationTarget := by
  intro V _ G emb data source hboundary regime
  exact
    data.regimeAttachmentFaceSourceDataFoundationTarget_of_regimeSelectedBoundaryArcSourceFoundationTarget
      (hfoundation data source hboundary regime)

/--
The canonical source-data target supplies the canonical selected-boundary-arc
target.
-/
theorem cap5FreeCanonicalAnnulusSelectedBoundaryArcSourceFoundationTarget_of_attachmentFaceSourceDataFoundationTarget
    (hfoundation :
      CAP5FreeCanonicalAnnulusPeeledCollarAttachmentFaceSourceDataFoundationTarget) :
    CAP5FreeCanonicalAnnulusPeeledCollarSelectedBoundaryArcSourceFoundationTarget := by
  intro V _ G emb data source hboundary regime
  exact
    data.regimeSelectedBoundaryArcSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      source hboundary (hfoundation data source hboundary regime)

/--
Canonical selected-boundary-arc and source-data CAP5-free targets are
equivalent.
-/
theorem cap5FreeCanonicalAnnulusSelectedBoundaryArcSourceFoundationTarget_iff_attachmentFaceSourceDataFoundationTarget :
    CAP5FreeCanonicalAnnulusPeeledCollarSelectedBoundaryArcSourceFoundationTarget ↔
      CAP5FreeCanonicalAnnulusPeeledCollarAttachmentFaceSourceDataFoundationTarget :=
  ⟨cap5FreeCanonicalAnnulusAttachmentFaceSourceDataFoundationTarget_of_selectedBoundaryArcSourceFoundationTarget,
    cap5FreeCanonicalAnnulusSelectedBoundaryArcSourceFoundationTarget_of_attachmentFaceSourceDataFoundationTarget⟩

/--
The repaired selected-boundary-arc target supplies the repaired source-data
target.
-/
theorem cap5FreeRepairedAnnulusAttachmentFaceSourceDataFoundationTarget_of_selectedBoundaryArcSourceFoundationTarget
    (hfoundation :
      CAP5FreeRepairedAnnulusPeeledCollarSelectedBoundaryArcSourceFoundationTarget) :
    CAP5FreeRepairedAnnulusPeeledCollarAttachmentFaceSourceDataFoundationTarget := by
  intro V _ G emb data source hboundary regime
  exact
    data.regimeAttachmentFaceSourceDataFoundationTarget_of_regimeSelectedBoundaryArcSourceFoundationTarget
      (hfoundation data source hboundary regime)

/--
The repaired source-data target supplies the repaired selected-boundary-arc
target.
-/
theorem cap5FreeRepairedAnnulusSelectedBoundaryArcSourceFoundationTarget_of_attachmentFaceSourceDataFoundationTarget
    (hfoundation :
      CAP5FreeRepairedAnnulusPeeledCollarAttachmentFaceSourceDataFoundationTarget) :
    CAP5FreeRepairedAnnulusPeeledCollarSelectedBoundaryArcSourceFoundationTarget := by
  intro V _ G emb data source hboundary regime
  exact
    data.regimeSelectedBoundaryArcSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      source hboundary (hfoundation data source hboundary regime)

/--
Repaired selected-boundary-arc and source-data CAP5-free targets are
equivalent.
-/
theorem cap5FreeRepairedAnnulusSelectedBoundaryArcSourceFoundationTarget_iff_attachmentFaceSourceDataFoundationTarget :
    CAP5FreeRepairedAnnulusPeeledCollarSelectedBoundaryArcSourceFoundationTarget ↔
      CAP5FreeRepairedAnnulusPeeledCollarAttachmentFaceSourceDataFoundationTarget :=
  ⟨cap5FreeRepairedAnnulusAttachmentFaceSourceDataFoundationTarget_of_selectedBoundaryArcSourceFoundationTarget,
    cap5FreeRepairedAnnulusSelectedBoundaryArcSourceFoundationTarget_of_attachmentFaceSourceDataFoundationTarget⟩

/--
Closed-walk selected-boundary-arc CAP5-free off-boundary route index.
-/
def Section92Step4ClosedWalkCAP5FreeSelectedBoundaryArcSourceOffBoundaryRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
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
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/-- Route-index theorem for the closed-walk selected-boundary-arc target. -/
theorem section92Step4ClosedWalkCAP5FreeSelectedBoundaryArcSourceOffBoundaryRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarSelectedBoundaryArcSourceFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeSelectedBoundaryArcSourceOffBoundaryRouteIndexTarget := by
  intro V _ G emb source regime
  have hselected :
      source.RegimeSelectedBoundaryArcSourceFoundationTarget :=
    hfoundation source regime
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

/--
Canonical annulus CAP5-free selected-boundary-arc/off-boundary route index.
-/
def
    Section92Step4CanonicalAnnulusCAP5FreeSelectedBoundaryArcSourceOffBoundaryRouteIndexTarget :
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
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Route-index theorem for the canonical selected-boundary-arc target. -/
theorem
    section92Step4CanonicalAnnulusCAP5FreeSelectedBoundaryArcSourceOffBoundaryRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarSelectedBoundaryArcSourceFoundationTarget) :
    Section92Step4CanonicalAnnulusCAP5FreeSelectedBoundaryArcSourceOffBoundaryRouteIndexTarget := by
  intro V _ G emb data regime source hboundary
  exact
    PlanarBoundaryAnnulusCollarGeometry.routeIndexConsequences_of_cap5FreeClosedWalkSelectedBoundaryArcSourceOffBoundaryTarget
      hfoundation data regime source hboundary

/--
Repaired annulus CAP5-free selected-boundary-arc/off-boundary route index.
-/
def
    Section92Step4RepairedAnnulusCAP5FreeSelectedBoundaryArcSourceOffBoundaryRouteIndexTarget :
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
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Route-index theorem for the repaired selected-boundary-arc target. -/
theorem
    section92Step4RepairedAnnulusCAP5FreeSelectedBoundaryArcSourceOffBoundaryRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarSelectedBoundaryArcSourceFoundationTarget) :
    Section92Step4RepairedAnnulusCAP5FreeSelectedBoundaryArcSourceOffBoundaryRouteIndexTarget := by
  intro V _ G emb data regime source hboundary
  exact
    PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry.routeIndexConsequences_of_cap5FreeClosedWalkSelectedBoundaryArcSourceOffBoundaryTarget
      hfoundation data regime source hboundary

end Mettapedia.GraphTheory.FourColor
