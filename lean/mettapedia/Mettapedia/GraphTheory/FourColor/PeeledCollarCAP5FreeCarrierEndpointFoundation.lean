import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeBoundarySupportFoundation

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Closed-walk carrier-endpoint and off-carrier foundation targets for the
CAP5-free peeled-collar regime route.

These targets expose the older annulus-carrier route at the closed-walk
CAP5-free level.  Carrier endpoint support now feeds the boundary-support
route directly, and off-carrier walk consistency feeds both carrier endpoint
support and off-boundary no-crossing.
-/

/--
Closed-walk carrier-endpoint foundation target for the selected induced
peeled collar embedding.
-/
def CAP5FreeClosedWalkPeeledCollarCarrierEndpointSupportFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarCarrierEndpointSupportTarget

/--
Closed-walk off-carrier walk-consistency foundation target for the selected
induced peeled collar embedding.
-/
def CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierWalkConsistencyTarget

/--
Closed-walk off-carrier route-input foundation target for the selected
induced peeled collar embedding.  This is equivalent to the off-carrier
walk-consistency target, but exposes the exact regime-route input record
consumed by the downstream cyclic-connectivity and S4 APIs.
-/
def CAP5FreeClosedWalkPeeledCollarOffCarrierRouteInputsFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      Nonempty
        (MinimalCounterexampleOffCarrierWalkConsistentPeeledCollarRouteInputs G
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)

/--
Off-carrier walk consistency supplies the closed-walk route-input foundation
target.
-/
theorem
    cap5FreeClosedWalkOffCarrierRouteInputsFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierRouteInputsFoundationTarget := by
  intro V _ G emb source regime
  exact ⟨
    { regime := regime
      offCarrierWalkConsistencies := hfoundation source regime }⟩

/--
The closed-walk route-input foundation target supplies off-carrier walk
consistency.
-/
theorem
    cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_offCarrierRouteInputsFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierRouteInputsFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget := by
  intro V _ G emb source regime
  rcases hfoundation source regime with ⟨inputs⟩
  exact inputs.offCarrierWalkConsistencies

/--
The route-input and off-carrier walk-consistency closed-walk foundation
targets are equivalent presentations of the same planar-normal-form
obligation.
-/
theorem
    cap5FreeClosedWalkOffCarrierRouteInputsFoundationTarget_iff_offCarrierWalkConsistencyFoundationTarget :
    CAP5FreeClosedWalkPeeledCollarOffCarrierRouteInputsFoundationTarget ↔
      CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget :=
  ⟨cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_offCarrierRouteInputsFoundationTarget,
    cap5FreeClosedWalkOffCarrierRouteInputsFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget⟩

/--
Off-carrier walk consistency supplies the closed-walk carrier-endpoint
foundation target.
-/
theorem
    cap5FreeClosedWalkCarrierEndpointSupportFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarCarrierEndpointSupportFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.carrierEndpointSupportTarget_of_offCarrierWalkConsistencyTarget
        (hfoundation source regime)

/--
Carrier-endpoint support supplies the closed-walk boundary-support foundation
target.
-/
theorem
    cap5FreeClosedWalkBoundarySupportFoundationTarget_of_carrierEndpointSupportFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarCarrierEndpointSupportFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarBoundarySupportFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_carrierEndpointSupportTarget
        (hfoundation source regime)

/--
Off-carrier walk consistency supplies the closed-walk boundary-support
foundation target.
-/
theorem
    cap5FreeClosedWalkBoundarySupportFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarBoundarySupportFoundationTarget :=
  cap5FreeClosedWalkBoundarySupportFoundationTarget_of_carrierEndpointSupportFoundationTarget
    (cap5FreeClosedWalkCarrierEndpointSupportFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
      hfoundation)

/--
Off-carrier walk consistency supplies the closed-walk off-boundary no-crossing
foundation target.
-/
theorem
    cap5FreeClosedWalkOffBoundaryNoCrossingFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffBoundaryNoCrossingFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_offCarrierWalkConsistencyTarget
        (hfoundation source regime)

/--
Closed-walk off-boundary no-crossing also supplies off-carrier walk
consistency, via the no-avoiding-walk separation bridge for the induced
boundary carrier.
-/
theorem
    cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_offBoundaryNoCrossingFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffBoundaryNoCrossingFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.offCarrierWalkConsistencyTarget_of_ambientSideSeparations
        (peeledCollarCutAmbientSideSeparationsToAmbient_of_ambientSideOffBoundaryNoCrossings
          (hfoundation source regime))

/--
Closed-walk off-carrier walk consistency and off-boundary no-crossing are
equivalent public foundation targets.
-/
theorem
    cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_iff_offBoundaryNoCrossingFoundationTarget :
    CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget ↔
      CAP5FreeClosedWalkPeeledCollarOffBoundaryNoCrossingFoundationTarget :=
  ⟨cap5FreeClosedWalkOffBoundaryNoCrossingFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget,
    cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_offBoundaryNoCrossingFoundationTarget⟩

/--
Carrier-endpoint support supplies the selected-source small-cut lift
foundation target.
-/
theorem cap5FreeClosedWalkSmallCutLiftFoundationTarget_of_carrierEndpointSupportFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarCarrierEndpointSupportFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarSmallCutLiftFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.peeledCollarSmallCyclicCutLiftsToAmbient_of_carrierEndpointSupportTarget
        (hfoundation source regime)

/--
Off-carrier walk consistency supplies the selected-source small-cut lift
foundation target.
-/
theorem cap5FreeClosedWalkSmallCutLiftFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarSmallCutLiftFoundationTarget :=
  cap5FreeClosedWalkSmallCutLiftFoundationTarget_of_carrierEndpointSupportFoundationTarget
    (cap5FreeClosedWalkCarrierEndpointSupportFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
      hfoundation)

/--
Public index with the closed-walk carrier-endpoint target as the closed-walk
foundation field.
-/
def CAP5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarCarrierEndpointSupportFoundationTarget

/--
Public index with the closed-walk off-carrier walk-consistency target as the
closed-walk foundation field.
-/
def CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget

/--
Public index with the closed-walk off-carrier route-input target as the
closed-walk foundation field.
-/
def CAP5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarOffCarrierRouteInputsFoundationTarget

/--
The off-carrier public index supplies the off-carrier route-input public
index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffCarrierRouteInputsFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
      hindex.2.2⟩

/--
The off-carrier route-input public index supplies the off-carrier public
index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_offCarrierRouteInputsFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_offCarrierRouteInputsFoundationTarget
      hindex.2.2⟩

/--
The off-carrier and route-input public indices are equivalent presentations of
the same closed-walk foundation checklist.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex_iff_offCarrierWalkConsistencyFoundationTargetIndex :
    CAP5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex ↔
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :=
  ⟨cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_offCarrierRouteInputsFoundationTargetIndex,
    cap5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex⟩

/--
The off-carrier public index supplies the carrier-endpoint public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkCarrierEndpointSupportFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
      hindex.2.2⟩

/--
The carrier-endpoint public index supplies the boundary-support public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex_of_carrierEndpointSupportFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkBoundarySupportFoundationTarget_of_carrierEndpointSupportFoundationTarget
      hindex.2.2⟩

/--
The off-carrier public index supplies the boundary-support public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex :=
  cap5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex_of_carrierEndpointSupportFoundationTargetIndex
    (cap5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex
      hindex)

/--
The off-carrier public index supplies the off-boundary public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffBoundaryNoCrossingFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
      hindex.2.2⟩

/--
The off-boundary public index supplies the off-carrier public index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_offBoundaryNoCrossingFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex) :
    CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :=
  ⟨hindex.1,
    hindex.2.1,
    cap5FreeClosedWalkOffCarrierWalkConsistencyFoundationTarget_of_offBoundaryNoCrossingFoundationTarget
      hindex.2.2⟩

/--
The off-carrier and off-boundary public indices are equivalent presentations
of the same closed-walk cut-lift foundation checklist.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_iff_offBoundaryNoCrossingFoundationTargetIndex :
    CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex ↔
      CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex :=
  ⟨cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex,
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_offBoundaryNoCrossingFoundationTargetIndex⟩

/--
Closed-walk carrier-endpoint route target: carrier endpoint support supplies
boundary support, the selected-source small-cut lift, cyclic
five-edge-connectivity, no cyclic two-cut, and S4 no-escape.
-/
def Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarCarrierEndpointSupportTarget ∧
        PeeledCollarCutAmbientSideBoundarySupportsToAmbient
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
Route-index theorem for the closed-walk carrier-endpoint foundation target.
-/
theorem section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarCarrierEndpointSupportFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget := by
  intro V _ G emb source regime
  have hcarrier :
      source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarCarrierEndpointSupportTarget :=
    hfoundation source regime
  have hsupport :
      PeeledCollarCutAmbientSideBoundarySupportsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_carrierEndpointSupportTarget
        hcarrier
  have hlift :
      PeeledCollarSmallCyclicCutLiftsToAmbient G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.peeledCollarSmallCyclicCutLiftsToAmbient_of_carrierEndpointSupportTarget
        hcarrier
  let inputs :
      MinimalCounterexamplePeeledCollarRouteInputs G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph := {
    regime := regime
    smallCutLift := hlift
  }
  exact
    ⟨hcarrier,
      hsupport,
      hlift,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

/--
Closed-walk off-carrier route target: off-carrier walk consistency supplies
carrier endpoint support, boundary support, off-boundary no-crossing, the
selected-source small-cut lift, cyclic five-edge-connectivity, no cyclic
two-cut, and S4 no-escape.
-/
def Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierWalkConsistencyTarget ∧
        source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarCarrierEndpointSupportTarget ∧
        PeeledCollarCutAmbientSideBoundarySupportsToAmbient
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
        PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
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
Closed-walk off-carrier route-input route target: the planar target returns
the exact route-input record, and that record supplies cyclic
five-edge-connectivity, no cyclic two-cut, and S4 no-escape.
-/
def Section92Step4ClosedWalkCAP5FreeOffCarrierRouteInputsFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      Nonempty
          (MinimalCounterexampleOffCarrierWalkConsistentPeeledCollarRouteInputs G
            source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet) ∧
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/--
Route-index theorem for the closed-walk off-carrier route-input foundation
target.
-/
theorem section92Step4ClosedWalkCAP5FreeOffCarrierRouteInputsFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierRouteInputsFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeOffCarrierRouteInputsFoundationRouteIndexTarget := by
  intro V _ G emb source regime
  rcases hfoundation source regime with ⟨inputs⟩
  exact
    ⟨⟨inputs⟩,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

/--
Route-index theorem for the closed-walk off-carrier foundation target.
-/
theorem section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget := by
  intro V _ G emb source regime
  have hoffCarrier :
      source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierWalkConsistencyTarget :=
    hfoundation source regime
  have hcarrier :
      source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarCarrierEndpointSupportTarget :=
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.carrierEndpointSupportTarget_of_offCarrierWalkConsistencyTarget
        hoffCarrier
  have hcarrierRoute :
      source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarCarrierEndpointSupportTarget ∧
        PeeledCollarCutAmbientSideBoundarySupportsToAmbient
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
        PeeledCollarSmallCyclicCutLiftsToAmbient G
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
    section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget
      (cap5FreeClosedWalkCarrierEndpointSupportFoundationTarget_of_offCarrierWalkConsistencyFoundationTarget
        hfoundation)
      source regime
  have hoffBoundary :
      PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_offCarrierWalkConsistencyTarget
        hoffCarrier
  exact
    ⟨hoffCarrier,
      hcarrier,
      hcarrierRoute.2.1,
      hoffBoundary,
      hcarrierRoute.2.2.1,
      hcarrierRoute.2.2.2.1,
      hcarrierRoute.2.2.2.2.1,
      hcarrierRoute.2.2.2.2.2⟩

/--
Closed-walk S4 salvage target for the carrier-endpoint foundation route.  This
is the downstream statement with cyclic five-edge-connectivity supplied by the
CAP5-free regime route, not assumed.
-/
def Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/--
Closed-walk S4 salvage target for the off-carrier walk-consistency foundation
route.
-/
def Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/--
The carrier-endpoint foundation target supplies the explicit closed-walk S4
salvage target.
-/
theorem section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportRegimeDischargedS4SalvageTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarCarrierEndpointSupportFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportRegimeDischargedS4SalvageTarget := by
  intro V _ G emb source regime
  exact
    (section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget
      hfoundation source regime).2.2.2.2.2

/--
The off-carrier walk-consistency foundation target supplies the explicit
closed-walk S4 salvage target.
-/
theorem section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyRegimeDischargedS4SalvageTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarOffCarrierWalkConsistencyFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyRegimeDischargedS4SalvageTarget := by
  intro V _ G emb source regime
  exact
    (section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget
      hfoundation source regime).2.2.2.2.2.2.2

/--
The carrier-endpoint public index supplies the carrier-endpoint route target,
the boundary-support route target, and the compact regime route index.
-/
theorem
    cap5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex_routeIndexTargets
    (hindex :
      CAP5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeBoundarySupportFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRegimeRouteIndexTarget := by
  have hboundaryIndex :
      CAP5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex_of_carrierEndpointSupportFoundationTargetIndex
      hindex
  have hboundaryRoutes :
      Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeBoundarySupportFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget ∧
        Section92Step4CAP5FreeRegimeRouteIndexTarget :=
    cap5FreePeeledCollarClosedWalkBoundarySupportFoundationTargetIndex_routeIndexTargets
      hboundaryIndex
  exact
    ⟨hboundaryRoutes.1,
      hboundaryRoutes.2.1,
      section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget
        hindex.2.2,
      hboundaryRoutes.2.2.1,
      hboundaryRoutes.2.2.2.2⟩

/--
The off-carrier public index supplies the off-carrier route target, the
carrier-endpoint route target, the off-boundary route target, and the compact
regime route index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_routeIndexTargets
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRegimeRouteIndexTarget := by
  have hcarrierIndex :
      CAP5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex
      hindex
  have hcarrierRoutes :
      Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeBoundarySupportFoundationRouteIndexTarget ∧
        Section92Step4CAP5FreeRegimeRouteIndexTarget :=
    cap5FreePeeledCollarClosedWalkCarrierEndpointSupportFoundationTargetIndex_routeIndexTargets
      hcarrierIndex
  have hoffIndex :
      CAP5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_of_offCarrierWalkConsistencyFoundationTargetIndex
      hindex
  have hoffRoutes :
      Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget ∧
        Section92Step4CAP5FreeRegimeRouteIndexTarget :=
    cap5FreePeeledCollarClosedWalkOffBoundaryNoCrossingFoundationTargetIndex_routeIndexTargets
      hoffIndex
  exact
    ⟨hcarrierRoutes.1,
      hcarrierRoutes.2.1,
      section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget
        hindex.2.2,
      hcarrierRoutes.2.2.1,
      hoffRoutes.2.2.1,
      hoffRoutes.2.2.2⟩

/--
The off-carrier route-input public index supplies the route-input target, the
off-carrier route target, the carrier-endpoint route target, the off-boundary
route target, and the compact regime route index.
-/
theorem
    cap5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex_routeIndexTargets
    (hindex :
      CAP5FreePeeledCollarClosedWalkOffCarrierRouteInputsFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierRouteInputsFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRegimeRouteIndexTarget := by
  have hoffIndex :
      CAP5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex :=
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_of_offCarrierRouteInputsFoundationTargetIndex
      hindex
  have hoffRoutes :
      Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeOffCarrierWalkConsistencyFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeCarrierEndpointSupportFoundationRouteIndexTarget ∧
        Section92Step4ClosedWalkCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget ∧
        Section92Step4CAP5FreeRegimeRouteIndexTarget :=
    cap5FreePeeledCollarClosedWalkOffCarrierWalkConsistencyFoundationTargetIndex_routeIndexTargets
      hoffIndex
  exact
    ⟨hoffRoutes.1,
      hoffRoutes.2.1,
      section92Step4ClosedWalkCAP5FreeOffCarrierRouteInputsFoundationRouteIndexTarget
        hindex.2.2,
      hoffRoutes.2.2.1,
      hoffRoutes.2.2.2.1,
      hoffRoutes.2.2.2.2.1,
      hoffRoutes.2.2.2.2.2⟩

end Mettapedia.GraphTheory.FourColor
