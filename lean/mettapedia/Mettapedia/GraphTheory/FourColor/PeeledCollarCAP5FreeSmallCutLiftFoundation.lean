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
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H := by
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
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H := by
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
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
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
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
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
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H

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
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H

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
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
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
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
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
