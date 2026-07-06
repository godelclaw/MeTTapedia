import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeOffBoundaryFoundation
import Mettapedia.GraphTheory.FourColor.PeeledCollarClosedWalkCutAvoidingFaceRouteIndex

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Face-source bridges into the CAP5-free off-boundary interface.

The face-source route already proves the graph-facing small-cut lift through
off-carrier walk consistency.  This module exposes the stronger intermediate
facts needed by the off-boundary foundation layer: off-boundary no-crossing,
local constancy, and separation.
-/

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryAnnulusBoundaryData

/--
Annulus-boundary off-carrier walk consistency supplies off-boundary
no-crossing for the canonical induced collar embedding.
-/
theorem peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
      data.inducedBoundaryEmbedding :=
  peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_ambientSideSeparations
    (data.peeledCollarCutAmbientSideSeparationsToAmbient_of_offCarrierWalkConsistencyTarget
      h)

end PlanarBoundaryAnnulusBoundaryData

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Mapped-cut face routes supply off-boundary no-crossing for the source's
canonical induced collar embedding.
-/
theorem offBoundaryNoCrossingsToAmbient_of_mappedCutAvoidingFaceRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget) :
    PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
  source.toPlanarBoundaryAnnulusBoundaryData
    |>.peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_offCarrierWalkConsistencyTarget
      (source.offCarrierWalkConsistencyTarget_of_mappedCutAvoidingFaceRouteTarget
        h)

/--
Noncrossing face-source data supplies off-boundary no-crossing for the
source's canonical induced collar embedding.
-/
theorem offBoundaryNoCrossingsToAmbient_of_regimeNoncrossingFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.RegimeNoncrossingFaceSourceFoundationTarget) :
    PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
  source.offBoundaryNoCrossingsToAmbient_of_mappedCutAvoidingFaceRouteTarget
    (source.mappedCutAvoidingFaceRouteTarget_of_regimeNoncrossingFaceSourceFoundationTarget
      h)

end PlanarBoundaryClosedWalkAnnulusBoundarySource

namespace PlanarBoundaryAnnulusCollarGeometry

/--
Canonical off-carrier walk consistency supplies the canonical off-boundary
target.
-/
theorem offBoundaryNoCrossingTarget_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    PlanarBoundaryAnnulusPeeledCollarOffBoundaryNoCrossingTarget
      data data.inducedBoundaryEmbedding :=
  data.boundaryData
    |>.peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_offCarrierWalkConsistencyTarget
      h

/--
Canonical aligned noncrossing face-source data supplies the canonical
off-boundary target.
-/
theorem offBoundaryNoCrossingTarget_of_regimeNoncrossingFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h : data.RegimeNoncrossingFaceSourceFoundationTarget) :
    PlanarBoundaryAnnulusPeeledCollarOffBoundaryNoCrossingTarget
      data data.inducedBoundaryEmbedding := by
  have hsource :
      source.RegimeNoncrossingFaceSourceFoundationTarget :=
    data.sourceRegimeNoncrossingFaceSourceFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
      source hboundary h
  have hoffSource :
      PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
    source.offBoundaryNoCrossingsToAmbient_of_regimeNoncrossingFaceSourceFoundationTarget
      hsource
  change PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
    data.inducedBoundaryEmbedding
  change PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
    data.boundaryData.inducedBoundaryEmbedding
  rw [hboundary]
  exact hoffSource

/--
The closed-walk CAP5-free face-source foundation theorem supplies canonical
off-boundary no-crossing, local constancy, separation, the small-cut lift,
cyclic five-edge-connectivity, no cyclic two-cut, and S4 no-escape.
-/
theorem routeIndexConsequences_of_cap5FreeClosedWalkFaceSourceOffBoundaryTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget)
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData) :
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
  have hface :
      data.RegimeNoncrossingFaceSourceFoundationTarget :=
    data.regimeNoncrossingFaceSourceFoundationTarget_of_cap5FreeClosedWalkFaceSourceFoundationTarget
      hfoundation source hboundary regime
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
    ⟨hoffBoundary,
      hlocal,
      hseparate,
      hlift,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Repaired off-carrier walk consistency supplies the repaired off-boundary
target.
-/
theorem offBoundaryNoCrossingTarget_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffBoundaryNoCrossingTarget
      data data.inducedBoundaryEmbedding :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.offBoundaryNoCrossingTarget_of_offCarrierWalkConsistencyTarget h

/--
Repaired aligned noncrossing face-source data supplies the repaired
off-boundary target.
-/
theorem offBoundaryNoCrossingTarget_of_regimeNoncrossingFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (h : data.RegimeNoncrossingFaceSourceFoundationTarget) :
    PlanarBoundaryPreviousBoundaryPeeledCollarOffBoundaryNoCrossingTarget
      data data.inducedBoundaryEmbedding := by
  have hsource :
      source.RegimeNoncrossingFaceSourceFoundationTarget :=
    data.sourceRegimeNoncrossingFaceSourceFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
      source hboundary h
  have hoffSource :
      PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
    source.offBoundaryNoCrossingsToAmbient_of_regimeNoncrossingFaceSourceFoundationTarget
      hsource
  change PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
    data.inducedBoundaryEmbedding
  change PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
    data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData.inducedBoundaryEmbedding
  rw [hboundary]
  exact hoffSource

/--
The closed-walk CAP5-free face-source foundation theorem supplies repaired
off-boundary no-crossing, local constancy, separation, the small-cut lift,
cyclic five-edge-connectivity, no cyclic two-cut, and S4 no-escape.
-/
theorem routeIndexConsequences_of_cap5FreeClosedWalkFaceSourceOffBoundaryTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget)
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
  have hface :
      data.RegimeNoncrossingFaceSourceFoundationTarget :=
    data.regimeNoncrossingFaceSourceFoundationTarget_of_cap5FreeClosedWalkFaceSourceFoundationTarget
      hfoundation source hboundary regime
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
    ⟨hoffBoundary,
      hlocal,
      hseparate,
      hlift,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Canonical annulus CAP5-free face-source/off-boundary route index.
-/
def
    Section92Step4CanonicalAnnulusCAP5FreeFaceSourceOffBoundaryRouteIndexTarget :
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

/-- Route-index theorem for the canonical face-source/off-boundary bridge. -/
theorem
    section92Step4CanonicalAnnulusCAP5FreeFaceSourceOffBoundaryRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget) :
    Section92Step4CanonicalAnnulusCAP5FreeFaceSourceOffBoundaryRouteIndexTarget := by
  intro V _ G emb data regime source hboundary
  exact
    data.routeIndexConsequences_of_cap5FreeClosedWalkFaceSourceOffBoundaryTarget
      hfoundation regime source hboundary

/--
Repaired annulus CAP5-free face-source/off-boundary route index.
-/
def
    Section92Step4RepairedAnnulusCAP5FreeFaceSourceOffBoundaryRouteIndexTarget :
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

/-- Route-index theorem for the repaired face-source/off-boundary bridge. -/
theorem
    section92Step4RepairedAnnulusCAP5FreeFaceSourceOffBoundaryRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget) :
    Section92Step4RepairedAnnulusCAP5FreeFaceSourceOffBoundaryRouteIndexTarget := by
  intro V _ G emb data regime source hboundary
  exact
    data.routeIndexConsequences_of_cap5FreeClosedWalkFaceSourceOffBoundaryTarget
      hfoundation regime source hboundary

end Mettapedia.GraphTheory.FourColor
