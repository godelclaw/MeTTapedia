import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeLocalConstancyFoundation

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Off-boundary CAP5-free peeled-collar foundation targets.

This is the edge-local form of the remaining planar-normal-form theorem.  For
every small cyclic collar cut, the filled ambient side may only cross an
ambient edge whose endpoints lie in the mapped cut endpoint support.  The
already-proved local-constancy bridge shows that this is equivalent to the
local side-constancy target and therefore supplies the same small-cut lift and
S4 consequences.
-/

/--
Canonical annulus off-boundary no-crossing target for the selected induced
peeled collar embedding.
-/
def PlanarBoundaryAnnulusPeeledCollarOffBoundaryNoCrossingTarget
    {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (_data : PlanarBoundaryAnnulusCollarGeometry emb)
    {W : Type} {H : SimpleGraph W} (φ : H ↪g G) : Prop :=
  PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient φ

/--
Repaired previous-boundary annulus off-boundary no-crossing target.
-/
def PlanarBoundaryPreviousBoundaryPeeledCollarOffBoundaryNoCrossingTarget
    {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (_data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    {W : Type} {H : SimpleGraph W} (φ : H ↪g G) : Prop :=
  PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient φ

/--
Embedded off-boundary foundation target for a selected peeled-collar embedding.
-/
def CAP5FreeEmbeddedPeeledCollarOffBoundaryNoCrossingFoundationTarget :
    Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : H ↪g G),
      MinimalCounterexamplePeeledCollarRegime G W H →
        PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient φ

/--
Canonical annulus off-boundary foundation target for the canonical induced
peeled collar graph selected by an annulus geometry.
-/
def CAP5FreeCanonicalAnnulusPeeledCollarOffBoundaryNoCrossingFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph →
      PlanarBoundaryAnnulusPeeledCollarOffBoundaryNoCrossingTarget
        data data.inducedBoundaryEmbedding

/--
Repaired annulus off-boundary foundation target for the previous-boundary
witness geometry variant.
-/
def CAP5FreeRepairedAnnulusPeeledCollarOffBoundaryNoCrossingFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph →
      PlanarBoundaryPreviousBoundaryPeeledCollarOffBoundaryNoCrossingTarget
        data data.inducedBoundaryEmbedding

/--
Embedded off-boundary no-crossing and embedded local constancy are equivalent
CAP5-free foundation targets.
-/
theorem cap5FreeEmbeddedPeeledCollarOffBoundaryNoCrossingFoundationTarget_iff_localConstancyFoundationTarget :
    CAP5FreeEmbeddedPeeledCollarOffBoundaryNoCrossingFoundationTarget ↔
      CAP5FreeEmbeddedPeeledCollarLocalConstancyFoundationTarget := by
  constructor
  · intro hoff V W _ _ G H φ regime
    exact
      peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_ambientSideOffBoundaryNoCrossings
        (hoff φ regime)
  · intro hlocal V W _ _ G H φ regime
    exact
      peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_localConstancies
        (hlocal φ regime)

namespace MinimalCounterexamplePeeledCollarRegime

/--
An embedded off-boundary foundation theorem supplies off-boundary no-crossing,
local constancy, the small-cut lift, cyclic five-edge-connectivity, no cyclic
two-cut, and S4 no-escape for the selected peeled-collar embedding.
-/
theorem routeIndexConsequences_of_cap5FreeEmbeddedOffBoundaryNoCrossingFoundationTarget
    (hfoundation :
      CAP5FreeEmbeddedPeeledCollarOffBoundaryNoCrossingFoundationTarget)
    {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : H ↪g G)
    (regime : MinimalCounterexamplePeeledCollarRegime G W H) :
    PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient φ ∧
      PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ ∧
      PeeledCollarSmallCyclicCutLiftsToAmbient G H ∧
      CyclicallyFiveEdgeConnected H ∧
      ClosedCollarForbidsCyclicTwoCut H ∧
      ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization H := by
  have hoffBoundary :
      PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient φ :=
    hfoundation φ regime
  have hlocal : PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ :=
    peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_ambientSideOffBoundaryNoCrossings
      hoffBoundary
  have hlift : PeeledCollarSmallCyclicCutLiftsToAmbient G H :=
    peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideOffBoundaryNoCrossings
      hoffBoundary
  let inputs : MinimalCounterexamplePeeledCollarRouteInputs G H := {
    regime := regime
    smallCutLift := hlift
  }
  exact
    ⟨hoffBoundary,
      hlocal,
      hlift,
      inputs.cyclicallyFiveEdgeConnected,
      inputs.closedCollarForbidsCyclicTwoCut,
      inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

end MinimalCounterexamplePeeledCollarRegime

namespace PlanarBoundaryAnnulusCollarGeometry

/--
Canonical off-boundary no-crossing and canonical local constancy are
equivalent CAP5-free foundation targets.
-/
theorem cap5FreeOffBoundaryNoCrossingFoundationTarget_iff_localConstancyFoundationTarget :
    CAP5FreeCanonicalAnnulusPeeledCollarOffBoundaryNoCrossingFoundationTarget ↔
      CAP5FreeCanonicalAnnulusPeeledCollarLocalConstancyFoundationTarget := by
  constructor
  · intro hoff V _ G emb data regime
    exact
      peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_ambientSideOffBoundaryNoCrossings
        (hoff data regime)
  · intro hlocal V _ G emb data regime
    exact
      peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_localConstancies
        (hlocal data regime)

/-- Canonical off-boundary no-crossing supplies the canonical small-cut lift. -/
theorem cap5FreeSmallCutLiftFoundationTarget_of_offBoundaryNoCrossingFoundationTarget
    (hfoundation :
      CAP5FreeCanonicalAnnulusPeeledCollarOffBoundaryNoCrossingFoundationTarget) :
    CAP5FreeCanonicalAnnulusPeeledCollarSmallCutLiftFoundationTarget := by
  intro V _ G emb data regime
  exact
    peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideOffBoundaryNoCrossings
      (hfoundation data regime)

/--
A canonical CAP5-free off-boundary foundation theorem supplies off-boundary
no-crossing, local constancy, separation, the small-cut lift, cyclic
five-edge-connectivity, no cyclic two-cut, and S4 no-escape.
-/
theorem routeIndexConsequences_of_cap5FreeOffBoundaryNoCrossingFoundationTarget
    (hfoundation :
      CAP5FreeCanonicalAnnulusPeeledCollarOffBoundaryNoCrossingFoundationTarget)
    {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph) :
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
  have hoffBoundary :
      PlanarBoundaryAnnulusPeeledCollarOffBoundaryNoCrossingTarget
        data data.inducedBoundaryEmbedding :=
    hfoundation data regime
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
Repaired off-boundary no-crossing and repaired local constancy are equivalent
CAP5-free foundation targets.
-/
theorem cap5FreeOffBoundaryNoCrossingFoundationTarget_iff_localConstancyFoundationTarget :
    CAP5FreeRepairedAnnulusPeeledCollarOffBoundaryNoCrossingFoundationTarget ↔
      CAP5FreeRepairedAnnulusPeeledCollarLocalConstancyFoundationTarget := by
  constructor
  · intro hoff V _ G emb data regime
    exact
      peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_ambientSideOffBoundaryNoCrossings
        (hoff data regime)
  · intro hlocal V _ G emb data regime
    exact
      peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_localConstancies
        (hlocal data regime)

/-- Repaired off-boundary no-crossing supplies the repaired small-cut lift. -/
theorem cap5FreeSmallCutLiftFoundationTarget_of_offBoundaryNoCrossingFoundationTarget
    (hfoundation :
      CAP5FreeRepairedAnnulusPeeledCollarOffBoundaryNoCrossingFoundationTarget) :
    CAP5FreeRepairedAnnulusPeeledCollarSmallCutLiftFoundationTarget := by
  intro V _ G emb data regime
  exact
    peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideOffBoundaryNoCrossings
      (hfoundation data regime)

/--
A repaired CAP5-free off-boundary foundation theorem supplies off-boundary
no-crossing, local constancy, separation, the small-cut lift, cyclic
five-edge-connectivity, no cyclic two-cut, and S4 no-escape.
-/
theorem routeIndexConsequences_of_cap5FreeOffBoundaryNoCrossingFoundationTarget
    (hfoundation :
      CAP5FreeRepairedAnnulusPeeledCollarOffBoundaryNoCrossingFoundationTarget)
    {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph) :
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
  have hoffBoundary :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffBoundaryNoCrossingTarget
        data data.inducedBoundaryEmbedding :=
    hfoundation data regime
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
Embedded CAP5-free off-boundary route index.
-/
def Section92Step4EmbeddedCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget :
    Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : H ↪g G),
      MinimalCounterexamplePeeledCollarRegime G W H →
        PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient φ ∧
        PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ ∧
        PeeledCollarSmallCyclicCutLiftsToAmbient G H ∧
        CyclicallyFiveEdgeConnected H ∧
        ClosedCollarForbidsCyclicTwoCut H ∧
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization H

/-- Route-index theorem for the embedded off-boundary target. -/
theorem section92Step4EmbeddedCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeEmbeddedPeeledCollarOffBoundaryNoCrossingFoundationTarget) :
    Section92Step4EmbeddedCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget := by
  intro V W _ _ G H φ regime
  exact
    regime.routeIndexConsequences_of_cap5FreeEmbeddedOffBoundaryNoCrossingFoundationTarget
      hfoundation φ

/--
Canonical annulus CAP5-free off-boundary route index.
-/
def
    Section92Step4CanonicalAnnulusCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph →
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
          data.inducedBoundaryGraph

/-- Route-index theorem for the canonical annulus off-boundary target. -/
theorem
    section92Step4CanonicalAnnulusCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeCanonicalAnnulusPeeledCollarOffBoundaryNoCrossingFoundationTarget) :
    Section92Step4CanonicalAnnulusCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget := by
  intro V _ G emb data regime
  exact
    data.routeIndexConsequences_of_cap5FreeOffBoundaryNoCrossingFoundationTarget
      hfoundation regime

/--
Repaired annulus CAP5-free off-boundary route index.
-/
def
    Section92Step4RepairedAnnulusCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph →
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
          data.inducedBoundaryGraph

/-- Route-index theorem for the repaired annulus off-boundary target. -/
theorem
    section92Step4RepairedAnnulusCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreeRepairedAnnulusPeeledCollarOffBoundaryNoCrossingFoundationTarget) :
    Section92Step4RepairedAnnulusCAP5FreeOffBoundaryNoCrossingFoundationRouteIndexTarget := by
  intro V _ G emb data regime
  exact
    data.routeIndexConsequences_of_cap5FreeOffBoundaryNoCrossingFoundationTarget
      hfoundation regime

/--
Canonical and repaired off-boundary foundation targets are equivalent to the
corresponding local-constancy foundation targets.
-/
theorem cap5FreeOffBoundaryNoCrossingFoundationTargets_iff_localConstancyFoundationTargets :
    CAP5FreeCanonicalAnnulusPeeledCollarOffBoundaryNoCrossingFoundationTarget ∧
      CAP5FreeRepairedAnnulusPeeledCollarOffBoundaryNoCrossingFoundationTarget ↔
    CAP5FreeCanonicalAnnulusPeeledCollarLocalConstancyFoundationTarget ∧
      CAP5FreeRepairedAnnulusPeeledCollarLocalConstancyFoundationTarget := by
  constructor
  · intro h
    exact
      ⟨PlanarBoundaryAnnulusCollarGeometry.cap5FreeOffBoundaryNoCrossingFoundationTarget_iff_localConstancyFoundationTarget.1
          h.1,
        PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry.cap5FreeOffBoundaryNoCrossingFoundationTarget_iff_localConstancyFoundationTarget.1
          h.2⟩
  · intro h
    exact
      ⟨PlanarBoundaryAnnulusCollarGeometry.cap5FreeOffBoundaryNoCrossingFoundationTarget_iff_localConstancyFoundationTarget.2
          h.1,
        PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry.cap5FreeOffBoundaryNoCrossingFoundationTarget_iff_localConstancyFoundationTarget.2
          h.2⟩

end Mettapedia.GraphTheory.FourColor
