import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeOffBoundaryFaceSource
import Mettapedia.GraphTheory.FourColor.PeeledCollarRegimeFacePlacementFoundationSourceData

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Chosen source-data bridges into the CAP5-free off-boundary interface.

The source-data target is the narrow per-cut package expected from the
planar-normal-form proof: a cut-compatible ambient side, attachment-face
placements, and face noncrossing for those placements.  This module exposes
that target as a CAP5-free foundation input and proves that it feeds the
off-boundary, local-constancy, separation, small-cut-lift, and S4 route
interfaces.
-/

variable {V : Type} [DecidableEq V]

/--
Closed-walk source-data foundation target: the CAP5-free regime supplies the
chosen attachment-face source-data package for every small cyclic carrier cut
of the closed-walk boundary source.
-/
def CAP5FreeClosedWalkPeeledCollarAttachmentFaceSourceDataFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      source.RegimeAttachmentFaceSourceDataFoundationTarget

/--
Canonical aligned source-data foundation target.  This is the data-level form
of the closed-walk source-data target, with boundary-data alignment explicit.
-/
def CAP5FreeCanonicalAnnulusPeeledCollarAttachmentFaceSourceDataFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData →
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph →
      data.RegimeAttachmentFaceSourceDataFoundationTarget

/--
Repaired aligned source-data foundation target, with the previous-boundary
witness geometry aligned to a closed-walk boundary source.
-/
def CAP5FreeRepairedAnnulusPeeledCollarAttachmentFaceSourceDataFoundationTarget :
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
      data.RegimeAttachmentFaceSourceDataFoundationTarget

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Chosen attachment-face source data supplies the noncrossing face-source target.
-/
theorem regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeAttachmentFaceSourceDataFoundationTarget) :
    source.RegimeNoncrossingFaceSourceFoundationTarget :=
  source.toPlanarBoundaryAnnulusBoundaryData
    |>.attachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceDataTarget h

/--
Chosen attachment-face source data supplies off-boundary no-crossing for the
source's canonical induced collar embedding.
-/
theorem offBoundaryNoCrossingsToAmbient_of_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeAttachmentFaceSourceDataFoundationTarget) :
    PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
  source.offBoundaryNoCrossingsToAmbient_of_regimeNoncrossingFaceSourceFoundationTarget
    (source.regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      h)

/--
Chosen attachment-face source data supplies noncrossing face-source data,
off-boundary no-crossing, local constancy, separation, the small-cut lift,
cyclic five-edge-connectivity, no cyclic two-cut, and S4 no-escape.
-/
theorem routeIndexConsequences_of_regimeAttachmentFaceSourceDataOffBoundaryTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h : source.RegimeAttachmentFaceSourceDataFoundationTarget) :
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
  have hface :
      source.RegimeNoncrossingFaceSourceFoundationTarget :=
    source.regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      h
  have hoffBoundary :
      PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
    source.offBoundaryNoCrossingsToAmbient_of_regimeNoncrossingFaceSourceFoundationTarget
      hface
  have hlocal :
      PeeledCollarCutAmbientSideLocalConstanciesToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
    peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_ambientSideOffBoundaryNoCrossings
      hoffBoundary
  have hseparate :
      PeeledCollarCutAmbientSideSeparationsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
    peeledCollarCutAmbientSideSeparationsToAmbient_of_ambientSideOffBoundaryNoCrossings
      hoffBoundary
  have hlift :
      PeeledCollarSmallCyclicCutLiftsToAmbient G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
    peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideOffBoundaryNoCrossings
      hoffBoundary
  let inputs :
      MinimalCounterexamplePeeledCollarRouteInputs G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph := {
    regime := regime
    smallCutLift := hlift
  }
  exact
    ⟨hface,
      hoffBoundary,
      hlocal,
      hseparate,
      hlift,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

end PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
The closed-walk source-data foundation target supplies the closed-walk
face-source foundation target.
-/
theorem cap5FreeClosedWalkFaceSourceFoundationTarget_of_attachmentFaceSourceDataFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSourceDataFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      (hfoundation source regime)

namespace PlanarBoundaryAnnulusCollarGeometry

/--
The closed-walk CAP5-free source-data theorem supplies the aligned canonical
source-data target.
-/
theorem regimeAttachmentFaceSourceDataFoundationTarget_of_cap5FreeClosedWalkAttachmentFaceSourceDataFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSourceDataFoundationTarget)
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph) :
    data.RegimeAttachmentFaceSourceDataFoundationTarget := by
  have hsource :
      source.RegimeAttachmentFaceSourceDataFoundationTarget :=
    hfoundation source
      (data.sourceRegime_of_boundaryData_eq source hboundary regime)
  change PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
    data
  change data.boundaryData.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
  rw [hboundary]
  exact hsource

/--
Canonical aligned source-data data supplies the canonical noncrossing
face-source target.
-/
theorem regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (h : data.RegimeAttachmentFaceSourceDataFoundationTarget) :
    data.RegimeNoncrossingFaceSourceFoundationTarget := by
  change PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
    data
  exact data.attachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceDataTarget h

/--
Canonical aligned source-data data supplies the canonical off-boundary target.
-/
theorem offBoundaryNoCrossingTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h : data.RegimeAttachmentFaceSourceDataFoundationTarget) :
    PlanarBoundaryAnnulusPeeledCollarOffBoundaryNoCrossingTarget
      data data.inducedBoundaryEmbedding :=
  data.offBoundaryNoCrossingTarget_of_regimeNoncrossingFaceSourceFoundationTarget
    source hboundary
    (data.regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      h)

/--
The closed-walk CAP5-free source-data theorem supplies canonical source-data,
noncrossing face-source data, off-boundary no-crossing, local constancy,
separation, the small-cut lift, cyclic five-edge-connectivity, no cyclic
two-cut, and S4 no-escape.
-/
theorem routeIndexConsequences_of_cap5FreeClosedWalkAttachmentFaceSourceDataOffBoundaryTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSourceDataFoundationTarget)
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData) :
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
  have hdata :
      data.RegimeAttachmentFaceSourceDataFoundationTarget :=
    data.regimeAttachmentFaceSourceDataFoundationTarget_of_cap5FreeClosedWalkAttachmentFaceSourceDataFoundationTarget
      hfoundation source hboundary regime
  have hface :
      data.RegimeNoncrossingFaceSourceFoundationTarget :=
    data.regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      hdata
  have hoffBoundary :
      PlanarBoundaryAnnulusPeeledCollarOffBoundaryNoCrossingTarget
        data data.inducedBoundaryEmbedding :=
    data.offBoundaryNoCrossingTarget_of_regimeNoncrossingFaceSourceFoundationTarget
      source hboundary hface
  have hlocal :
      PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget
        data data.inducedBoundaryEmbedding :=
    peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_ambientSideOffBoundaryNoCrossings
      hoffBoundary
  have hseparate :
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding :=
    planarBoundaryAnnulusPeeledCollarSeparationTarget_of_localConstancyTarget
      hlocal
  have hlift :
      PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph :=
    peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideOffBoundaryNoCrossings
      hoffBoundary
  let inputs :
      MinimalCounterexamplePeeledCollarRouteInputs G
        data.inducedBoundaryGraph := {
    regime := regime
    smallCutLift := hlift
  }
  exact
    ⟨hdata,
      hface,
      hoffBoundary,
      hlocal,
      hseparate,
      hlift,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
The closed-walk CAP5-free source-data theorem supplies the aligned repaired
source-data target.
-/
theorem regimeAttachmentFaceSourceDataFoundationTarget_of_cap5FreeClosedWalkAttachmentFaceSourceDataFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSourceDataFoundationTarget)
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
    data.RegimeAttachmentFaceSourceDataFoundationTarget := by
  have hsource :
      source.RegimeAttachmentFaceSourceDataFoundationTarget :=
    hfoundation source
      (data.sourceRegime_of_boundaryData_eq source hboundary regime)
  change
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
      data
  change
    data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData
      |>.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
  rw [hboundary]
  exact hsource

/--
Repaired aligned source-data data supplies the repaired noncrossing
face-source target.
-/
theorem regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (h : data.RegimeAttachmentFaceSourceDataFoundationTarget) :
    data.RegimeNoncrossingFaceSourceFoundationTarget := by
  change
    PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget
      data
  exact data.attachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceDataTarget h

/--
Repaired aligned source-data data supplies the repaired off-boundary target.
-/
theorem offBoundaryNoCrossingTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (h : data.RegimeAttachmentFaceSourceDataFoundationTarget) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffBoundaryNoCrossingTarget
      data data.inducedBoundaryEmbedding :=
  data.offBoundaryNoCrossingTarget_of_regimeNoncrossingFaceSourceFoundationTarget
    source hboundary
    (data.regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      h)

/--
The closed-walk CAP5-free source-data theorem supplies repaired source-data,
noncrossing face-source data, off-boundary no-crossing, local constancy,
separation, the small-cut lift, cyclic five-edge-connectivity, no cyclic
two-cut, and S4 no-escape.
-/
theorem routeIndexConsequences_of_cap5FreeClosedWalkAttachmentFaceSourceDataOffBoundaryTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSourceDataFoundationTarget)
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
  have hdata :
      data.RegimeAttachmentFaceSourceDataFoundationTarget :=
    data.regimeAttachmentFaceSourceDataFoundationTarget_of_cap5FreeClosedWalkAttachmentFaceSourceDataFoundationTarget
      hfoundation source hboundary regime
  have hface :
      data.RegimeNoncrossingFaceSourceFoundationTarget :=
    data.regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      hdata
  have hoffBoundary :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffBoundaryNoCrossingTarget
        data data.inducedBoundaryEmbedding :=
    data.offBoundaryNoCrossingTarget_of_regimeNoncrossingFaceSourceFoundationTarget
      source hboundary hface
  have hlocal :
      PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget
        data data.inducedBoundaryEmbedding :=
    peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_ambientSideOffBoundaryNoCrossings
      hoffBoundary
  have hseparate :
      PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding :=
    planarBoundaryPreviousBoundaryPeeledCollarSeparationTarget_of_localConstancyTarget
      hlocal
  have hlift :
      PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph :=
    peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideOffBoundaryNoCrossings
      hoffBoundary
  let inputs :
      MinimalCounterexamplePeeledCollarRouteInputs G
        data.inducedBoundaryGraph := {
    regime := regime
    smallCutLift := hlift
  }
  exact
    ⟨hdata,
      hface,
      hoffBoundary,
      hlocal,
      hseparate,
      hlift,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Closed-walk source-data CAP5-free off-boundary route index.
-/
def Section92Step4ClosedWalkCAP5FreeAttachmentFaceSourceDataOffBoundaryRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
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

/-- Route-index theorem for the closed-walk source-data off-boundary target. -/
theorem section92Step4ClosedWalkCAP5FreeAttachmentFaceSourceDataOffBoundaryRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSourceDataFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeAttachmentFaceSourceDataOffBoundaryRouteIndexTarget := by
  intro V _ G emb source regime
  have hdata :
      source.RegimeAttachmentFaceSourceDataFoundationTarget :=
    hfoundation source regime
  have hconsequences :=
    source.routeIndexConsequences_of_regimeAttachmentFaceSourceDataOffBoundaryTarget
      regime hdata
  exact
    ⟨hdata,
      hconsequences.1,
      hconsequences.2.1,
      hconsequences.2.2.1,
      hconsequences.2.2.2.1,
      hconsequences.2.2.2.2.1,
      hconsequences.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2.1,
      hconsequences.2.2.2.2.2.2.2⟩

/--
Canonical annulus CAP5-free source-data/off-boundary route index.
-/
def
    Section92Step4CanonicalAnnulusCAP5FreeAttachmentFaceSourceDataOffBoundaryRouteIndexTarget :
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

/-- Route-index theorem for the canonical source-data off-boundary target. -/
theorem
    section92Step4CanonicalAnnulusCAP5FreeAttachmentFaceSourceDataOffBoundaryRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSourceDataFoundationTarget) :
    Section92Step4CanonicalAnnulusCAP5FreeAttachmentFaceSourceDataOffBoundaryRouteIndexTarget := by
  intro V _ G emb data regime source hboundary
  exact
    PlanarBoundaryAnnulusCollarGeometry.routeIndexConsequences_of_cap5FreeClosedWalkAttachmentFaceSourceDataOffBoundaryTarget
      hfoundation data regime source hboundary

/--
Repaired annulus CAP5-free source-data/off-boundary route index.
-/
def
    Section92Step4RepairedAnnulusCAP5FreeAttachmentFaceSourceDataOffBoundaryRouteIndexTarget :
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

/-- Route-index theorem for the repaired source-data off-boundary target. -/
theorem
    section92Step4RepairedAnnulusCAP5FreeAttachmentFaceSourceDataOffBoundaryRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSourceDataFoundationTarget) :
    Section92Step4RepairedAnnulusCAP5FreeAttachmentFaceSourceDataOffBoundaryRouteIndexTarget := by
  intro V _ G emb data regime source hboundary
  exact
    PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry.routeIndexConsequences_of_cap5FreeClosedWalkAttachmentFaceSourceDataOffBoundaryTarget
      hfoundation data regime source hboundary

end Mettapedia.GraphTheory.FourColor
