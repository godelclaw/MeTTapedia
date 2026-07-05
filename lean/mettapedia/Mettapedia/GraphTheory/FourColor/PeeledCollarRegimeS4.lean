import Mettapedia.GraphTheory.FourColor.PeeledCollarCutLiftEmbedding
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarWindingRealization

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

variable {V W : Type} [DecidableEq V] [DecidableEq W]

/--
Index of the regime route inputs consumed by the S4 collar salvage.  The route
does not consume cyclic five-edge-connectivity as an input; it consumes the
ambient normal form together with the named small-cut lift foundation target.
-/
structure MinimalCounterexamplePeeledCollarRouteInputs
    (G : SimpleGraph V) (H : SimpleGraph W) where
  regime : MinimalCounterexamplePeeledCollarRegime G W H
  smallCutLift : PeeledCollarSmallCyclicCutLiftsToAmbient G H

namespace MinimalCounterexamplePeeledCollarRouteInputs

/-- The indexed route inputs supply cyclic five-edge-connectivity for the
peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexamplePeeledCollarRouteInputs G H) :
    CyclicallyFiveEdgeConnected H :=
  peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_smallCutLift
    inputs.regime inputs.smallCutLift

/-- The indexed route inputs supply the no-cyclic-two-cut fact consumed by the
closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexamplePeeledCollarRouteInputs G H) :
    ClosedCollarForbidsCyclicTwoCut H :=
  closedCollarForbidsCyclicTwoCut_of_cyclicallyFiveEdgeConnected
    inputs.cyclicallyFiveEdgeConnected

/--
Regime-discharged S4 winding salvage for a selected peeled collar: the
existing all-size winding theorem now receives cyclic five-edge-connectivity
from the minimal-counterexample route inputs rather than as an independent
collar hypothesis.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexamplePeeledCollarRouteInputs G H) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H :=
  closedCollarWindingFreedomEscape_not_simplyRealizable_allSizes_of_cyclicallyFiveEdgeConnected
    inputs.cyclicallyFiveEdgeConnected

end MinimalCounterexamplePeeledCollarRouteInputs

/--
More concrete index of the regime route inputs: the collar is embedded in the
ambient graph, and every small cyclic collar cut has an ambient side extension
with exactly the mapped crossing support.  This is the reusable interface for
the remaining planar normal-form foundation target.
-/
structure MinimalCounterexampleEmbeddedPeeledCollarRouteInputs
    (G : SimpleGraph V) (H : SimpleGraph W) where
  regime : MinimalCounterexamplePeeledCollarRegime G W H
  embedding : H ↪g G
  cutSideExtensions : PeeledCollarCutSideExtensionsToAmbient embedding

namespace MinimalCounterexampleEmbeddedPeeledCollarRouteInputs

/-- Concrete embedding-side route inputs supply the older graph-facing route
input record. -/
def toRouteInputs
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleEmbeddedPeeledCollarRouteInputs G H) :
    MinimalCounterexamplePeeledCollarRouteInputs G H where
  regime := inputs.regime
  smallCutLift :=
    peeledCollarSmallCyclicCutLiftsToAmbient_of_cutSideExtensions
      inputs.cutSideExtensions

/-- The concrete embedded route inputs supply cyclic five-edge-connectivity for
the peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleEmbeddedPeeledCollarRouteInputs G H) :
    CyclicallyFiveEdgeConnected H :=
  inputs.toRouteInputs.cyclicallyFiveEdgeConnected

/-- The concrete embedded route inputs supply the no-cyclic-two-cut fact
consumed by the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleEmbeddedPeeledCollarRouteInputs G H) :
    ClosedCollarForbidsCyclicTwoCut H :=
  inputs.toRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Embedded-regime S4 winding salvage: cyclic five-edge-connectivity is obtained
from the minimal-counterexample normal form plus concrete side-extension
transport for peeled-collar cuts.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleEmbeddedPeeledCollarRouteInputs G H) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H :=
  inputs.toRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable

end MinimalCounterexampleEmbeddedPeeledCollarRouteInputs

/--
End-to-end S4 salvage target discharged by the minimal-counterexample peeled
collar route.  The route input record supplies the upstream collar
connectivity bridge; the downstream closed-collar theorem then rules out the
winding-freedom escape.
-/
def Section92Step4RegimeDischargedS4SalvageTarget : Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W},
      MinimalCounterexamplePeeledCollarRouteInputs G H →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H

/-- Verbatim end-to-end regime-discharged S4 salvage statement. -/
theorem section92Step4RegimeDischargedS4SalvageTarget :
    Section92Step4RegimeDischargedS4SalvageTarget := by
  intro V W _ _ G H inputs
  exact inputs.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the concrete embedded peeled-collar route
interface.
-/
def Section92Step4EmbeddedRegimeDischargedS4SalvageTarget : Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W},
      MinimalCounterexampleEmbeddedPeeledCollarRouteInputs G H →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H

/-- Verbatim end-to-end embedded-regime S4 salvage statement. -/
theorem section92Step4EmbeddedRegimeDischargedS4SalvageTarget :
    Section92Step4EmbeddedRegimeDischargedS4SalvageTarget := by
  intro V W _ _ G H inputs
  exact inputs.closedCollarWindingFreedomEscape_not_simplyRealizable

end Mettapedia.GraphTheory.FourColor
