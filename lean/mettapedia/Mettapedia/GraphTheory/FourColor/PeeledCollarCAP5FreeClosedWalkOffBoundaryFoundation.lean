import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeOffBoundaryFaceSource
import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeRegimeRouteIndex

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Closed-walk off-boundary foundation target for the CAP5-free peeled-collar
regime route.

This is the next proof-facing target below the selected-source small-cut lift:
for every small cyclic cut in the selected closed-walk collar, the filled
ambient side has no off-boundary crossing.  Existing cut-lift infrastructure
then supplies local constancy, separation, the small-cut lift, cyclic
five-edge-connectivity, no cyclic two-cut, and S4 no-escape.
-/

/--
Closed-walk off-boundary no-crossing foundation target for the selected induced
peeled collar embedding.
-/
def CAP5FreeClosedWalkPeeledCollarOffBoundaryNoCrossingFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding

/--
The closed-walk off-boundary no-crossing foundation target supplies the
selected-source small-cut lift foundation target.
-/
theorem cap5FreeClosedWalkSmallCutLiftFoundationTarget_of_offBoundaryNoCrossingFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffBoundaryNoCrossingFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarSmallCutLiftFoundationTarget := by
  intro V _ G emb source regime
  exact
    peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideOffBoundaryNoCrossings
      (hfoundation source regime)

/--
The closed-walk face-source foundation target supplies the closed-walk
off-boundary no-crossing foundation target.
-/
theorem
    cap5FreeClosedWalkOffBoundaryNoCrossingFoundationTarget_of_faceSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffBoundaryNoCrossingFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.offBoundaryNoCrossingsToAmbient_of_regimeNoncrossingFaceSourceFoundationTarget
      (hfoundation source regime)

/--
Public index with the closed-walk off-boundary no-crossing target as the
closed-walk foundation field.
-/
def CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarOffBoundaryNoCrossingFoundationTarget

/--
The off-boundary public index supplies the selected-source small-cut route
foundation index.
-/
theorem
    cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_of_closedWalkOffBoundaryNoCrossingFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex) :
    CAP5FreePeeledCollarRegimeRouteFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkSmallCutLiftFoundationTarget_of_offBoundaryNoCrossingFoundationTarget
      hindex.2.2⟩

/--
The older face-source public foundation index supplies the off-boundary public
index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_of_foundationTargetIndex
    (hindex : CAP5FreePeeledCollarFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffBoundaryNoCrossingFoundationTarget_of_faceSourceFoundationTarget
      hindex.2.2⟩

/--
The split-source public foundation index supplies the off-boundary public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_of_splitSourceFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarSplitSourceFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex :=
  cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_of_foundationTargetIndex
    (cap5FreePeeledCollarFoundationTargetIndex_of_splitSourceFoundationTargetIndex
      hindex)

/--
Closed-walk off-boundary route target: off-boundary no-crossing supplies local
constancy, separation, the selected-source small-cut lift, cyclic
five-edge-connectivity, no cyclic two-cut, and S4 no-escape.
-/
def Section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
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

/--
Route-index theorem for the closed-walk off-boundary no-crossing foundation
target.
-/
theorem section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffBoundaryNoCrossingFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget := by
  intro V _ G emb source regime
  have hoffBoundary :
      PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
    hfoundation source regime
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
    ⟨hoffBoundary,
      hlocal,
      hseparate,
      hlift,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

/--
The off-boundary public index supplies the off-boundary route target and the
compact regime route index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_routeIndexTargets
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRegimeRouteIndexTarget :=
  ⟨section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget
      hindex.1,
    section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget
      hindex.2.1,
    section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget
      hindex.2.2,
    section92Step4CAP5FreeRegimeRouteIndexTarget_of_regimeRouteFoundationTargetIndex
      (cap5FreePeeledCollarRegimeRouteFoundationTargetIndex_of_closedWalkOffBoundaryNoCrossingFoundationTargetIndex
        hindex)⟩

end Mettapedia.GraphTheory.FourColor
