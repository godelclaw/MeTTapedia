import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeSmallCutLiftFoundation

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Local-constancy CAP5-free peeled-collar foundation targets.

This is the proof-facing layer below the small-cut lift: for every small
cyclic collar cut, the filled ambient side is locally constant on every
ambient edge incident to an endpoint outside the mapped cut support.  The
existing annulus extraction bridge converts this local statement to
no-avoiding-walk separation and then to the graph-facing small-cut lift.
-/

/--
Embedded local-constancy foundation target for a selected peeled-collar
embedding.
-/
def CAP5FreeEmbeddedPeeledCollarLocalConstancyFoundationTarget :
    Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : H ↪g G),
      MinimalCounterexamplePeeledCollarRegime G W H →
        PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ

/--
Canonical annulus local-constancy foundation target for the canonical induced
peeled collar graph selected by an annulus geometry.
-/
def CAP5FreeCanonicalAnnulusPeeledCollarLocalConstancyFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph →
      PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget
        data data.inducedBoundaryEmbedding

/--
Repaired annulus local-constancy foundation target for the previous-boundary
witness geometry variant.
-/
def CAP5FreeRepairedAnnulusPeeledCollarLocalConstancyFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph →
      PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget
        data data.inducedBoundaryEmbedding

namespace MinimalCounterexamplePeeledCollarRegime

/--
An embedded local-constancy foundation theorem supplies local constancy, the
small-cut lift, cyclic five-edge-connectivity, no cyclic two-cut, and S4
no-escape for the selected peeled-collar embedding.
-/
theorem routeIndexConsequences_of_cap5FreeEmbeddedLocalConstancyFoundationTarget
    (hfoundation :
      CAP5FreeEmbeddedPeeledCollarLocalConstancyFoundationTarget)
    {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : H ↪g G)
    (regime : MinimalCounterexamplePeeledCollarRegime G W H) :
    PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ ∧
      PeeledCollarSmallCyclicCutLiftsToAmbient G H ∧
      CyclicallyFiveEdgeConnected H ∧
      ClosedCollarForbidsCyclicTwoCut H ∧
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H := by
  have hlocal : PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ :=
    hfoundation φ regime
  have hlift : PeeledCollarSmallCyclicCutLiftsToAmbient G H :=
    peeledCollarSmallCyclicCutLiftsToAmbient_of_localConstancies hlocal
  let inputs : MinimalCounterexamplePeeledCollarRouteInputs G H := {
    regime := regime
    smallCutLift := hlift
  }
  exact
    ⟨hlocal,
      hlift,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

end MinimalCounterexamplePeeledCollarRegime

namespace PlanarBoundaryAnnulusCollarGeometry

/--
Canonical local constancy and canonical separation are equivalent CAP5-free
foundation targets.
-/
theorem cap5FreeLocalConstancyFoundationTarget_iff_separationFoundationTarget :
    CAP5FreeCanonicalAnnulusPeeledCollarLocalConstancyFoundationTarget ↔
      CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget := by
  constructor
  · intro hlocal V _ G emb data regime
    exact
      planarBoundaryAnnulusPeeledCollarSeparationTarget_of_localConstancyTarget
        (hlocal data regime)
  · intro hseparate V _ G emb data regime
    exact
      planarBoundaryAnnulusPeeledCollarLocalConstancyTarget_of_separationTarget
        (hseparate data regime)

/-- Canonical local constancy supplies the canonical small-cut lift target. -/
theorem cap5FreeSmallCutLiftFoundationTarget_of_localConstancyFoundationTarget
    (hfoundation :
      CAP5FreeCanonicalAnnulusPeeledCollarLocalConstancyFoundationTarget) :
    CAP5FreeCanonicalAnnulusPeeledCollarSmallCutLiftFoundationTarget := by
  intro V _ G emb data regime
  exact
    peeledCollarSmallCyclicCutLiftsToAmbient_of_annulusExtractionTarget
      (hfoundation data regime)

/--
A canonical CAP5-free local-constancy foundation theorem supplies local
constancy, separation, the small-cut lift, cyclic five-edge-connectivity, no
cyclic two-cut, and S4 no-escape.
-/
theorem routeIndexConsequences_of_cap5FreeLocalConstancyFoundationTarget
    (hfoundation :
      CAP5FreeCanonicalAnnulusPeeledCollarLocalConstancyFoundationTarget)
    {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph) :
    PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget
        data data.inducedBoundaryEmbedding ∧
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding ∧
      PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph ∧
      CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
        data.inducedBoundaryGraph := by
  have hlocal :
      PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget
        data data.inducedBoundaryEmbedding :=
    hfoundation data regime
  have hseparate :
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding :=
    planarBoundaryAnnulusPeeledCollarSeparationTarget_of_localConstancyTarget
      hlocal
  have hlift :
      PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph :=
    peeledCollarSmallCyclicCutLiftsToAmbient_of_annulusExtractionTarget
      hlocal
  let inputs :
      MinimalCounterexamplePeeledCollarRouteInputs G
        data.inducedBoundaryGraph := {
    regime := regime
    smallCutLift := hlift
  }
  exact
    ⟨hlocal,
      hseparate,
      hlift,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Repaired local constancy and repaired separation are equivalent CAP5-free
foundation targets.
-/
theorem cap5FreeLocalConstancyFoundationTarget_iff_separationFoundationTarget :
    CAP5FreeRepairedAnnulusPeeledCollarLocalConstancyFoundationTarget ↔
      CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget := by
  constructor
  · intro hlocal V _ G emb data regime
    exact
      planarBoundaryPreviousBoundaryPeeledCollarSeparationTarget_of_localConstancyTarget
        (hlocal data regime)
  · intro hseparate V _ G emb data regime
    exact
      planarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget_of_separationTarget
        (hseparate data regime)

/-- Repaired local constancy supplies the repaired small-cut lift target. -/
theorem cap5FreeSmallCutLiftFoundationTarget_of_localConstancyFoundationTarget
    (hfoundation :
      CAP5FreeRepairedAnnulusPeeledCollarLocalConstancyFoundationTarget) :
    CAP5FreeRepairedAnnulusPeeledCollarSmallCutLiftFoundationTarget := by
  intro V _ G emb data regime
  exact
    peeledCollarSmallCyclicCutLiftsToAmbient_of_previousBoundaryAnnulusExtractionTarget
      (hfoundation data regime)

/--
A repaired CAP5-free local-constancy foundation theorem supplies local
constancy, separation, the small-cut lift, cyclic five-edge-connectivity, no
cyclic two-cut, and S4 no-escape.
-/
theorem routeIndexConsequences_of_cap5FreeLocalConstancyFoundationTarget
    (hfoundation :
      CAP5FreeRepairedAnnulusPeeledCollarLocalConstancyFoundationTarget)
    {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph) :
    PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget
        data data.inducedBoundaryEmbedding ∧
      PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding ∧
      PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph ∧
      CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
        data.inducedBoundaryGraph := by
  have hlocal :
      PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget
        data data.inducedBoundaryEmbedding :=
    hfoundation data regime
  have hseparate :
      PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding :=
    planarBoundaryPreviousBoundaryPeeledCollarSeparationTarget_of_localConstancyTarget
      hlocal
  have hlift :
      PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph :=
    peeledCollarSmallCyclicCutLiftsToAmbient_of_previousBoundaryAnnulusExtractionTarget
      hlocal
  let inputs :
      MinimalCounterexamplePeeledCollarRouteInputs G
        data.inducedBoundaryGraph := {
    regime := regime
    smallCutLift := hlift
  }
  exact
    ⟨hlocal,
      hseparate,
      hlift,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Embedded CAP5-free local-constancy route index.
-/
def Section92Step4EmbeddedCAP5FreeLocalConstancyFoundationRouteIndexTarget :
    Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : H ↪g G),
      MinimalCounterexamplePeeledCollarRegime G W H →
        PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ ∧
        PeeledCollarSmallCyclicCutLiftsToAmbient G H ∧
        CyclicallyFiveEdgeConnected H ∧
        ClosedCollarForbidsCyclicTwoCut H ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H

/-- Route-index theorem for the embedded local-constancy target. -/
theorem section92Step4EmbeddedCAP5FreeLocalConstancyFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeEmbeddedPeeledCollarLocalConstancyFoundationTarget) :
    Section92Step4EmbeddedCAP5FreeLocalConstancyFoundationRouteIndexTarget := by
  intro V W _ _ G H φ regime
  exact
    regime.routeIndexConsequences_of_cap5FreeEmbeddedLocalConstancyFoundationTarget
      hfoundation φ

/--
Canonical annulus CAP5-free local-constancy route index.
-/
def
    Section92Step4CanonicalAnnulusCAP5FreeLocalConstancyFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph →
      PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget
          data data.inducedBoundaryEmbedding ∧
        PlanarBoundaryAnnulusPeeledCollarSeparationTarget
          data data.inducedBoundaryEmbedding ∧
        PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph ∧
        CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Route-index theorem for the canonical annulus local-constancy target. -/
theorem
    section92Step4CanonicalAnnulusCAP5FreeLocalConstancyFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeCanonicalAnnulusPeeledCollarLocalConstancyFoundationTarget) :
    Section92Step4CanonicalAnnulusCAP5FreeLocalConstancyFoundationRouteIndexTarget := by
  intro V _ G emb data regime
  exact
    data.routeIndexConsequences_of_cap5FreeLocalConstancyFoundationTarget
      hfoundation regime

/--
Repaired annulus CAP5-free local-constancy route index.
-/
def
    Section92Step4RepairedAnnulusCAP5FreeLocalConstancyFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph →
      PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget
          data data.inducedBoundaryEmbedding ∧
        PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
          data data.inducedBoundaryEmbedding ∧
        PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph ∧
        CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Route-index theorem for the repaired annulus local-constancy target. -/
theorem
    section92Step4RepairedAnnulusCAP5FreeLocalConstancyFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeRepairedAnnulusPeeledCollarLocalConstancyFoundationTarget) :
    Section92Step4RepairedAnnulusCAP5FreeLocalConstancyFoundationRouteIndexTarget := by
  intro V _ G emb data regime
  exact
    data.routeIndexConsequences_of_cap5FreeLocalConstancyFoundationTarget
      hfoundation regime

/--
Canonical and repaired local-constancy foundation targets are equivalent to
the corresponding separation foundation targets.
-/
theorem cap5FreeLocalConstancyFoundationTargets_iff_separationFoundationTargets :
    CAP5FreeCanonicalAnnulusPeeledCollarLocalConstancyFoundationTarget ∧
      CAP5FreeRepairedAnnulusPeeledCollarLocalConstancyFoundationTarget ↔
    CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
      CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget := by
  constructor
  · intro h
    exact
      ⟨PlanarBoundaryAnnulusCollarGeometry.cap5FreeLocalConstancyFoundationTarget_iff_separationFoundationTarget.1
          h.1,
        PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry.cap5FreeLocalConstancyFoundationTarget_iff_separationFoundationTarget.1
          h.2⟩
  · intro h
    exact
      ⟨PlanarBoundaryAnnulusCollarGeometry.cap5FreeLocalConstancyFoundationTarget_iff_separationFoundationTarget.2
          h.1,
        PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry.cap5FreeLocalConstancyFoundationTarget_iff_separationFoundationTarget.2
          h.2⟩

end Mettapedia.GraphTheory.FourColor
