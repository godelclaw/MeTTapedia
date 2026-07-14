import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeFoundationTargets

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Graph-facing CAP5-free peeled-collar foundation targets.

The smallest reusable obligation is the small-cut lift: every small cyclic cut
inside the peeled collar lifts to an ambient small cyclic cut of no larger
edge support.  The ambient CAP5-free minimal-counterexample regime already
supplies the no-small-cyclic-cut obstruction, so this lift is enough to inherit
cyclic five-edge-connectivity.
-/

/--
Graph-facing small-cut lift foundation target for the CAP5-free peeled-collar
regime.  This is the nearest remaining planar-normal-form theorem target below
all separation, local-constancy, and face-route formulations.
-/
def CAP5FreePeeledCollarSmallCutLiftFoundationTarget : Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W},
      MinimalCounterexamplePeeledCollarRegime G W H →
        PeeledCollarSmallCyclicCutLiftsToAmbient G H

/--
Checker-facing candidate-lift foundation target.  This is the form expected
from a proof that starts with realized `CyclicSeparatorCandidate`s.
-/
def CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget : Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W},
      MinimalCounterexamplePeeledCollarRegime G W H →
        PeeledCollarRealizedCandidateLiftsToAmbientSmallCut G H

/--
Canonical annulus small-cut lift foundation target for the canonical induced
peeled collar graph selected by an annulus geometry.
-/
def CAP5FreeCanonicalAnnulusPeeledCollarSmallCutLiftFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph →
      PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph

/--
Repaired annulus small-cut lift foundation target for the previous-boundary
witness geometry variant.
-/
def CAP5FreeRepairedAnnulusPeeledCollarSmallCutLiftFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph →
      PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph

/-- For the induced collar selected by a closed-walk boundary source, every
small cyclic collar cut lifts to the ambient graph without increasing its
support. -/
def ClosedWalkActualCollarSmallCyclicCutLiftsToAmbient :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      PeeledCollarSmallCyclicCutLiftsToAmbient G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/-- Small-cut lifting instantiates inherited cyclic five-edge connectivity from
the ambient minimal-counterexample regime. -/
theorem closedWalkActualCollar_cyclicallyFiveEdgeConnected_of_smallCyclicCutLift
    (hcutLift : ClosedWalkActualCollarSmallCyclicCutLiftsToAmbient)
    {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime : MinimalCounterexamplePeeledCollarRegime G
      (BoundaryEdgeSetEndpointVertex
        (G := G)
        source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph) :
    CyclicallyFiveEdgeConnected
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
  peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_smallCutLift
    regime (hcutLift source regime)

/--
Candidate-lift foundations are stronger than small-cut lift foundations.
-/
theorem cap5FreePeeledCollarSmallCutLiftFoundationTarget_of_realizedCandidateLift
    (hfoundation :
      CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget) :
    CAP5FreePeeledCollarSmallCutLiftFoundationTarget := by
  intro V W _ _ G H regime
  exact
    peeledCollarSmallCyclicCutLiftsToAmbient_of_realizedCandidateLift
      (hfoundation regime)

/--
Small-cut lift foundations also supply candidate-lift foundations.
-/
theorem cap5FreePeeledCollarRealizedCandidateLiftFoundationTarget_of_smallCutLift
    (hfoundation :
      CAP5FreePeeledCollarSmallCutLiftFoundationTarget) :
    CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget := by
  intro V W _ _ G H regime
  exact
    peeledCollarRealizedCandidateLiftsToAmbientSmallCut_of_smallCutLift
      (hfoundation regime)

/--
The graph-facing small-cut lift and realized-candidate lift CAP5-free
foundation targets are equivalent.
-/
theorem cap5FreePeeledCollarRealizedCandidateLiftFoundationTarget_iff_smallCutLift :
    CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget ↔
      CAP5FreePeeledCollarSmallCutLiftFoundationTarget :=
  ⟨cap5FreePeeledCollarSmallCutLiftFoundationTarget_of_realizedCandidateLift,
    cap5FreePeeledCollarRealizedCandidateLiftFoundationTarget_of_smallCutLift⟩

namespace MinimalCounterexamplePeeledCollarRegime

/--
A graph-facing CAP5-free small-cut lift foundation theorem supplies the lift,
cyclic five-edge-connectivity, no cyclic two-cut, and the closed-collar S4
no-escape consequence for any selected peeled collar.
-/
theorem routeIndexConsequences_of_cap5FreeSmallCutLiftFoundationTarget
    (hfoundation : CAP5FreePeeledCollarSmallCutLiftFoundationTarget)
    {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G H ∧
      CyclicallyFiveEdgeConnected H ∧
      ClosedCollarForbidsCyclicTwoCut H ∧
      ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization H := by
  have hlift : PeeledCollarSmallCyclicCutLiftsToAmbient G H :=
    hfoundation regime
  let inputs : MinimalCounterexamplePeeledCollarRouteInputs G H := {
    regime := regime
    smallCutLift := hlift
  }
  exact
    ⟨hlift,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

/--
A checker-facing realized-candidate lift foundation theorem supplies the same
downstream graph consequences.
-/
theorem routeIndexConsequences_of_cap5FreeRealizedCandidateLiftFoundationTarget
    (hfoundation :
      CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget)
    {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H) :
    PeeledCollarRealizedCandidateLiftsToAmbientSmallCut G H ∧
      PeeledCollarSmallCyclicCutLiftsToAmbient G H ∧
      CyclicallyFiveEdgeConnected H ∧
      ClosedCollarForbidsCyclicTwoCut H ∧
      ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization H := by
  have hcandidate :
      PeeledCollarRealizedCandidateLiftsToAmbientSmallCut G H :=
    hfoundation regime
  have hsmall :
      PeeledCollarSmallCyclicCutLiftsToAmbient G H :=
    peeledCollarSmallCyclicCutLiftsToAmbient_of_realizedCandidateLift
      hcandidate
  let inputs : MinimalCounterexamplePeeledCollarRouteInputs G H := {
    regime := regime
    smallCutLift := hsmall
  }
  exact
    ⟨hcandidate,
      hsmall,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

/--
A checker-facing realized-candidate lift foundation supplies the first-class
realized-candidate route-input record for a selected peeled collar.
-/
def realizedCandidateRouteInputs_of_cap5FreeRealizedCandidateLiftFoundationTarget
    (hfoundation :
      CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget)
    {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H) :
    MinimalCounterexampleRealizedCandidatePeeledCollarRouteInputs G H where
  regime := regime
  realizedCandidateLift := hfoundation regime

end MinimalCounterexamplePeeledCollarRegime

namespace PlanarBoundaryAnnulusCollarGeometry

/--
Canonical separation foundations are stronger than canonical small-cut lift
foundations.
-/
theorem cap5FreeSmallCutLiftFoundationTarget_of_separationFoundationTarget
    (hfoundation :
      CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget) :
    CAP5FreeCanonicalAnnulusPeeledCollarSmallCutLiftFoundationTarget := by
  intro V _ G emb data regime
  exact
    peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideSeparations
      (hfoundation data regime)

/--
A canonical CAP5-free small-cut lift foundation theorem supplies the lift,
cyclic five-edge-connectivity, no cyclic two-cut, and S4 no-escape for the
canonical induced peeled collar graph.
-/
theorem routeIndexConsequences_of_cap5FreeSmallCutLiftFoundationTarget
    (hfoundation :
      CAP5FreeCanonicalAnnulusPeeledCollarSmallCutLiftFoundationTarget)
    {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph ∧
      CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
        data.inducedBoundaryGraph := by
  have hlift :
      PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph :=
    hfoundation data regime
  let inputs :
      MinimalCounterexamplePeeledCollarRouteInputs G
        data.inducedBoundaryGraph := {
    regime := regime
    smallCutLift := hlift
  }
  exact
    ⟨hlift,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Repaired separation foundations are stronger than repaired small-cut lift
foundations.
-/
theorem cap5FreeSmallCutLiftFoundationTarget_of_separationFoundationTarget
    (hfoundation :
      CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget) :
    CAP5FreeRepairedAnnulusPeeledCollarSmallCutLiftFoundationTarget := by
  intro V _ G emb data regime
  exact
    peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideSeparations
      (hfoundation data regime)

/--
A repaired CAP5-free small-cut lift foundation theorem supplies the lift,
cyclic five-edge-connectivity, no cyclic two-cut, and S4 no-escape for the
repaired induced peeled collar graph.
-/
theorem routeIndexConsequences_of_cap5FreeSmallCutLiftFoundationTarget
    (hfoundation :
      CAP5FreeRepairedAnnulusPeeledCollarSmallCutLiftFoundationTarget)
    {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph ∧
      CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
        data.inducedBoundaryGraph := by
  have hlift :
      PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph :=
    hfoundation data regime
  let inputs :
      MinimalCounterexamplePeeledCollarRouteInputs G
        data.inducedBoundaryGraph := {
    regime := regime
    smallCutLift := hlift
  }
  exact
    ⟨hlift,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
A closed-walk source small-cut lift foundation theorem supplies the lift,
cyclic five-edge-connectivity, no cyclic two-cut, and S4 no-escape for the
selected induced peeled collar graph.
-/
theorem routeIndexConsequences_of_cap5FreeSmallCutLiftFoundationTarget
    (hfoundation :
      ClosedWalkActualCollarSmallCyclicCutLiftsToAmbient)
    {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      CyclicallyFiveEdgeConnected
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph := by
  have hlift :
      PeeledCollarSmallCyclicCutLiftsToAmbient G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
    hfoundation source regime
  let inputs :
      MinimalCounterexamplePeeledCollarRouteInputs G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph := {
    regime := regime
    smallCutLift := hlift
  }
  exact
    ⟨hlift,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

/--
A closed-walk source small-cut lift foundation supplies the checker-facing
realized-candidate route-input record for the selected induced peeled collar.
-/
def realizedCandidateRouteInputs_of_cap5FreeSmallCutLiftFoundationTarget
    (hfoundation :
      ClosedWalkActualCollarSmallCyclicCutLiftsToAmbient)
    {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph) :
    MinimalCounterexampleRealizedCandidatePeeledCollarRouteInputs G
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph where
  regime := regime
  realizedCandidateLift :=
    peeledCollarRealizedCandidateLiftsToAmbientSmallCut_of_smallCutLift
      (hfoundation source regime)

/--
The existing closed-walk face-source foundation supplies the selected-source
small-cut lift foundation.
-/
theorem cap5FreeSmallCutLiftFoundationTarget_of_faceSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget) :
    ClosedWalkActualCollarSmallCyclicCutLiftsToAmbient := by
  intro V _ G emb source regime
  exact
    (source.routeIndexConsequences_of_cap5FreeFaceSourceFoundationTarget
      hfoundation regime).2.2.2.2.1

end PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Graph-facing CAP5-free small-cut lift route index.  Once the named foundation
target is proved, cyclic five-edge-connectivity is supplied by the regime and
the small-cut lift, not hypothesized.
-/
def Section92Step4CAP5FreeSmallCutLiftFoundationRouteIndexTarget : Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W},
      MinimalCounterexamplePeeledCollarRegime G W H →
        PeeledCollarSmallCyclicCutLiftsToAmbient G H ∧
        CyclicallyFiveEdgeConnected H ∧
        ClosedCollarForbidsCyclicTwoCut H ∧
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization H

/-- Route-index theorem for the graph-facing small-cut lift foundation target. -/
theorem section92Step4CAP5FreeSmallCutLiftFoundationRouteIndexTarget
    (hfoundation : CAP5FreePeeledCollarSmallCutLiftFoundationTarget) :
    Section92Step4CAP5FreeSmallCutLiftFoundationRouteIndexTarget := by
  intro V W _ _ G H regime
  exact
    regime.routeIndexConsequences_of_cap5FreeSmallCutLiftFoundationTarget
      hfoundation

/--
Checker-facing CAP5-free realized-candidate route index.
-/
def Section92Step4CAP5FreeRealizedCandidateLiftFoundationRouteIndexTarget :
    Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W},
      MinimalCounterexamplePeeledCollarRegime G W H →
        PeeledCollarRealizedCandidateLiftsToAmbientSmallCut G H ∧
        PeeledCollarSmallCyclicCutLiftsToAmbient G H ∧
        CyclicallyFiveEdgeConnected H ∧
        ClosedCollarForbidsCyclicTwoCut H ∧
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization H

/-- Route-index theorem for the checker-facing realized-candidate lift target. -/
theorem section92Step4CAP5FreeRealizedCandidateLiftFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget) :
    Section92Step4CAP5FreeRealizedCandidateLiftFoundationRouteIndexTarget := by
  intro V W _ _ G H regime
  exact
    regime.routeIndexConsequences_of_cap5FreeRealizedCandidateLiftFoundationTarget
      hfoundation

/--
Checker-facing realized-candidate route-input index.  This exposes the
route-input record itself, together with its immediate no-realization,
cyclic-connectivity, two-cut, and S4 consequences.
-/
def Section92Step4CAP5FreeRealizedCandidateRouteInputsFoundationRouteIndexTarget :
    Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H),
      ∃ inputs :
          MinimalCounterexampleRealizedCandidatePeeledCollarRouteInputs G H,
        inputs.regime = regime ∧
          (∀ candidate : CyclicSeparatorCandidate H, ¬ candidate.Realizes) ∧
          CyclicallyFiveEdgeConnected H ∧
          ClosedCollarForbidsCyclicTwoCut H ∧
          ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization H

/--
Route-index theorem for the checker-facing realized-candidate route-input
target.
-/
theorem section92Step4CAP5FreeRealizedCandidateRouteInputsFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget) :
    Section92Step4CAP5FreeRealizedCandidateRouteInputsFoundationRouteIndexTarget := by
  intro V W _ _ G H regime
  let inputs :
      MinimalCounterexampleRealizedCandidatePeeledCollarRouteInputs G H :=
    { regime := regime
      realizedCandidateLift := hfoundation regime }
  exact
    ⟨inputs,
      rfl,
      fun candidate => inputs.not_realizes candidate,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

/--
The realized-candidate lift foundation supplies both the raw consequence route
index and the first-class route-input route index.
-/
theorem cap5FreePeeledCollarRealizedCandidateLiftFoundationTarget_routeInputRouteIndexTargets
    (hfoundation :
      CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget) :
    Section92Step4CAP5FreeRealizedCandidateLiftFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRealizedCandidateRouteInputsFoundationRouteIndexTarget :=
  ⟨section92Step4CAP5FreeRealizedCandidateLiftFoundationRouteIndexTarget
      hfoundation,
    section92Step4CAP5FreeRealizedCandidateRouteInputsFoundationRouteIndexTarget
      hfoundation⟩

/--
Canonical annulus CAP5-free small-cut lift route index.
-/
def Section92Step4CanonicalAnnulusCAP5FreeSmallCutLiftFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph →
      PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph ∧
        CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          data.inducedBoundaryGraph

/-- Route-index theorem for the canonical annulus small-cut lift target. -/
theorem section92Step4CanonicalAnnulusCAP5FreeSmallCutLiftFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeCanonicalAnnulusPeeledCollarSmallCutLiftFoundationTarget) :
    Section92Step4CanonicalAnnulusCAP5FreeSmallCutLiftFoundationRouteIndexTarget := by
  intro V _ G emb data regime
  exact
    data.routeIndexConsequences_of_cap5FreeSmallCutLiftFoundationTarget
      hfoundation regime

/--
Repaired annulus CAP5-free small-cut lift route index.
-/
def Section92Step4RepairedAnnulusCAP5FreeSmallCutLiftFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph →
      PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph ∧
        CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          data.inducedBoundaryGraph

/-- Route-index theorem for the repaired annulus small-cut lift target. -/
theorem section92Step4RepairedAnnulusCAP5FreeSmallCutLiftFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeRepairedAnnulusPeeledCollarSmallCutLiftFoundationTarget) :
    Section92Step4RepairedAnnulusCAP5FreeSmallCutLiftFoundationRouteIndexTarget := by
  intro V _ G emb data regime
  exact
    data.routeIndexConsequences_of_cap5FreeSmallCutLiftFoundationTarget
      hfoundation regime

/--
Closed-walk source CAP5-free small-cut lift route index.
-/
def Section92Step4ClosedWalkCAP5FreeSmallCutLiftFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      PeeledCollarSmallCyclicCutLiftsToAmbient G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/-- Route-index theorem for the closed-walk source small-cut lift target. -/
theorem section92Step4ClosedWalkCAP5FreeSmallCutLiftFoundationRouteIndexTarget
    (hfoundation :
      ClosedWalkActualCollarSmallCyclicCutLiftsToAmbient) :
    Section92Step4ClosedWalkCAP5FreeSmallCutLiftFoundationRouteIndexTarget := by
  intro V _ G emb source regime
  exact
    source.routeIndexConsequences_of_cap5FreeSmallCutLiftFoundationTarget
      hfoundation regime

/--
Closed-walk source route-input index for a small-cut lift foundation.  This is
the selected-collar form of the checker-facing route-input record.
-/
def Section92Step4ClosedWalkCAP5FreeSmallCutLiftRouteInputsFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph),
      ∃ inputs :
          MinimalCounterexampleRealizedCandidatePeeledCollarRouteInputs G
            source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph,
        inputs.regime = regime ∧
          PeeledCollarSmallCyclicCutLiftsToAmbient G
            source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
          (∀ candidate :
              CyclicSeparatorCandidate
                source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph,
              ¬ candidate.Realizes) ∧
          CyclicallyFiveEdgeConnected
            source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
          ClosedCollarForbidsCyclicTwoCut
            source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
          ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
            source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/--
Route-index theorem for the closed-walk checker-facing route-input target.
-/
theorem section92Step4ClosedWalkCAP5FreeSmallCutLiftRouteInputsFoundationRouteIndexTarget
    (hfoundation :
      ClosedWalkActualCollarSmallCyclicCutLiftsToAmbient) :
    Section92Step4ClosedWalkCAP5FreeSmallCutLiftRouteInputsFoundationRouteIndexTarget := by
  intro V _ G emb source regime
  have hlift :
      PeeledCollarSmallCyclicCutLiftsToAmbient G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
    hfoundation source regime
  let inputs :
      MinimalCounterexampleRealizedCandidatePeeledCollarRouteInputs G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
    { regime := regime
      realizedCandidateLift :=
        peeledCollarRealizedCandidateLiftsToAmbientSmallCut_of_smallCutLift
          hlift }
  exact
    ⟨inputs,
      rfl,
      hlift,
      fun candidate => inputs.not_realizes candidate,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

/--
The closed-walk face-source foundation supplies the corresponding small-cut
lift route index.
-/
theorem section92Step4ClosedWalkCAP5FreeSmallCutLiftFoundationRouteIndexTarget_of_faceSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeSmallCutLiftFoundationRouteIndexTarget :=
  section92Step4ClosedWalkCAP5FreeSmallCutLiftFoundationRouteIndexTarget
    (PlanarBoundaryClosedWalkAnnulusBoundarySource.cap5FreeSmallCutLiftFoundationTarget_of_faceSourceFoundationTarget
      hfoundation)

/--
The closed-walk face-source foundation also supplies the checker-facing
route-input route index for the selected induced collar.
-/
theorem section92Step4ClosedWalkCAP5FreeSmallCutLiftRouteInputsFoundationRouteIndexTarget_of_faceSourceFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeSmallCutLiftRouteInputsFoundationRouteIndexTarget :=
  section92Step4ClosedWalkCAP5FreeSmallCutLiftRouteInputsFoundationRouteIndexTarget
    (PlanarBoundaryClosedWalkAnnulusBoundarySource.cap5FreeSmallCutLiftFoundationTarget_of_faceSourceFoundationTarget
      hfoundation)

/--
The separation foundation index supplies the corresponding small-cut lift
route indices.
-/
theorem cap5FreeSeparationFoundationTargets_smallCutLiftRouteIndexTargets
    (hcanonical :
      CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget)
    (hrepaired :
      CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget) :
    Section92Step4CanonicalAnnulusCAP5FreeSmallCutLiftFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSmallCutLiftFoundationRouteIndexTarget := by
  exact
    ⟨section92Step4CanonicalAnnulusCAP5FreeSmallCutLiftFoundationRouteIndexTarget
        (PlanarBoundaryAnnulusCollarGeometry.cap5FreeSmallCutLiftFoundationTarget_of_separationFoundationTarget
            hcanonical),
      section92Step4RepairedAnnulusCAP5FreeSmallCutLiftFoundationRouteIndexTarget
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry.cap5FreeSmallCutLiftFoundationTarget_of_separationFoundationTarget
            hrepaired)⟩

end Mettapedia.GraphTheory.FourColor
