import Mettapedia.GraphTheory.FourColor.PeeledCollarAnnulusExtraction
import Mettapedia.GraphTheory.FourColor.PeeledCollarBoundarySupportExtraction
import Mettapedia.GraphTheory.FourColor.PeeledCollarBoundaryCarrierEndpointRange
import Mettapedia.GraphTheory.FourColor.PeeledCollarBoundaryCarrierWalkExtension
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
Separation-facing index of the regime route inputs: the remaining planar
normal-form obligation is stated as no-avoiding-walk side separation for every
small cyclic collar cut.
-/
structure MinimalCounterexampleSeparatedPeeledCollarRouteInputs
    (G : SimpleGraph V) (H : SimpleGraph W) where
  regime : MinimalCounterexamplePeeledCollarRegime G W H
  embedding : H ↪g G
  ambientSideSeparations :
    PeeledCollarCutAmbientSideSeparationsToAmbient embedding

namespace MinimalCounterexampleSeparatedPeeledCollarRouteInputs

/-- Separation-facing route inputs supply the embedded route input record. -/
def toEmbeddedRouteInputs
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleSeparatedPeeledCollarRouteInputs G H) :
    MinimalCounterexampleEmbeddedPeeledCollarRouteInputs G H where
  regime := inputs.regime
  embedding := inputs.embedding
  cutSideExtensions :=
    peeledCollarCutSideExtensionsToAmbient_of_ambientSideSeparations
      inputs.ambientSideSeparations

/-- The separation-facing route inputs supply cyclic five-edge-connectivity for
the peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleSeparatedPeeledCollarRouteInputs G H) :
    CyclicallyFiveEdgeConnected H :=
  inputs.toEmbeddedRouteInputs.cyclicallyFiveEdgeConnected

/-- The separation-facing route inputs supply the no-cyclic-two-cut fact
consumed by the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleSeparatedPeeledCollarRouteInputs G H) :
    ClosedCollarForbidsCyclicTwoCut H :=
  inputs.toEmbeddedRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Separation-regime S4 winding salvage: the existing all-size closed-collar
winding theorem receives cyclic five-edge-connectivity from no-avoiding-walk
side separation plus the minimal-counterexample normal form.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleSeparatedPeeledCollarRouteInputs G H) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H :=
  inputs.toEmbeddedRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable

end MinimalCounterexampleSeparatedPeeledCollarRouteInputs

/--
Edge-barrier index of the regime route inputs: the remaining planar normal-form
obligation is stated edgewise, as every ambient side-crossing edge belonging to
the mapped collar-cut support.
-/
structure MinimalCounterexampleBarrierPeeledCollarRouteInputs
    (G : SimpleGraph V) (H : SimpleGraph W) where
  regime : MinimalCounterexamplePeeledCollarRegime G W H
  embedding : H ↪g G
  ambientSideBarriers :
    PeeledCollarCutAmbientSideBarriersToAmbient embedding

namespace MinimalCounterexampleBarrierPeeledCollarRouteInputs

/-- Edge-barrier route inputs supply the separation-facing route input record. -/
def toSeparatedRouteInputs
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleBarrierPeeledCollarRouteInputs G H) :
    MinimalCounterexampleSeparatedPeeledCollarRouteInputs G H where
  regime := inputs.regime
  embedding := inputs.embedding
  ambientSideSeparations :=
    peeledCollarCutAmbientSideSeparationsToAmbient_of_ambientSideBarriers
      inputs.ambientSideBarriers

/-- The edge-barrier route inputs supply cyclic five-edge-connectivity for the
peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleBarrierPeeledCollarRouteInputs G H) :
    CyclicallyFiveEdgeConnected H :=
  inputs.toSeparatedRouteInputs.cyclicallyFiveEdgeConnected

/-- The edge-barrier route inputs supply the no-cyclic-two-cut fact consumed by
the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleBarrierPeeledCollarRouteInputs G H) :
    ClosedCollarForbidsCyclicTwoCut H :=
  inputs.toSeparatedRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Barrier-regime S4 winding salvage: cyclic five-edge-connectivity is obtained
from the minimal-counterexample normal form plus edge-barrier data for every
small cyclic collar cut.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleBarrierPeeledCollarRouteInputs G H) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H :=
  inputs.toSeparatedRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable

end MinimalCounterexampleBarrierPeeledCollarRouteInputs

/--
Preimage-facing index of the regime route inputs: the remaining planar
normal-form obligation is stated as every ambient side-crossing edge having a
collar-edge preimage.
-/
structure MinimalCounterexamplePreimagePeeledCollarRouteInputs
    (G : SimpleGraph V) (H : SimpleGraph W) where
  regime : MinimalCounterexamplePeeledCollarRegime G W H
  embedding : H ↪g G
  ambientSidePreimages :
    PeeledCollarCutAmbientSidePreimagesToAmbient embedding

namespace MinimalCounterexamplePreimagePeeledCollarRouteInputs

/-- Preimage-facing route inputs supply the edge-barrier route input record. -/
def toBarrierRouteInputs
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexamplePreimagePeeledCollarRouteInputs G H) :
    MinimalCounterexampleBarrierPeeledCollarRouteInputs G H where
  regime := inputs.regime
  embedding := inputs.embedding
  ambientSideBarriers :=
    peeledCollarCutAmbientSideBarriersToAmbient_of_ambientSidePreimages
      inputs.ambientSidePreimages

/-- The preimage-facing route inputs supply cyclic five-edge-connectivity for
the peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexamplePreimagePeeledCollarRouteInputs G H) :
    CyclicallyFiveEdgeConnected H :=
  inputs.toBarrierRouteInputs.cyclicallyFiveEdgeConnected

/-- The preimage-facing route inputs supply the no-cyclic-two-cut fact consumed
by the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexamplePreimagePeeledCollarRouteInputs G H) :
    ClosedCollarForbidsCyclicTwoCut H :=
  inputs.toBarrierRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Preimage-regime S4 winding salvage: cyclic five-edge-connectivity is obtained
from the minimal-counterexample normal form plus collar-edge preimages for
ambient side-crossing edges.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexamplePreimagePeeledCollarRouteInputs G H) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H :=
  inputs.toBarrierRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable

end MinimalCounterexamplePreimagePeeledCollarRouteInputs

/--
Endpoint-range index of the regime route inputs: the remaining planar
normal-form obligation is stated as every endpoint of every ambient
side-crossing edge lying in the embedded collar vertex range.
-/
structure MinimalCounterexampleEndpointRangePeeledCollarRouteInputs
    (G : SimpleGraph V) (H : SimpleGraph W) where
  regime : MinimalCounterexamplePeeledCollarRegime G W H
  embedding : H ↪g G
  ambientSideEndpointRanges :
    PeeledCollarCutAmbientSideEndpointRangesToAmbient embedding

namespace MinimalCounterexampleEndpointRangePeeledCollarRouteInputs

/-- Endpoint-range route inputs supply the preimage-facing route input record. -/
def toPreimageRouteInputs
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleEndpointRangePeeledCollarRouteInputs G H) :
    MinimalCounterexamplePreimagePeeledCollarRouteInputs G H where
  regime := inputs.regime
  embedding := inputs.embedding
  ambientSidePreimages :=
    peeledCollarCutAmbientSidePreimagesToAmbient_of_ambientSideEndpointRanges
      inputs.ambientSideEndpointRanges

/-- The endpoint-range route inputs supply cyclic five-edge-connectivity for
the peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleEndpointRangePeeledCollarRouteInputs G H) :
    CyclicallyFiveEdgeConnected H :=
  inputs.toPreimageRouteInputs.cyclicallyFiveEdgeConnected

/-- The endpoint-range route inputs supply the no-cyclic-two-cut fact consumed
by the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleEndpointRangePeeledCollarRouteInputs G H) :
    ClosedCollarForbidsCyclicTwoCut H :=
  inputs.toPreimageRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Endpoint-range S4 winding salvage: cyclic five-edge-connectivity is obtained
from the minimal-counterexample normal form plus the planar-facing fact that
ambient side-crossing edges have endpoints in the embedded collar range.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleEndpointRangePeeledCollarRouteInputs G H) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H :=
  inputs.toPreimageRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable

end MinimalCounterexampleEndpointRangePeeledCollarRouteInputs

/--
Boundary-support index of the regime route inputs: the remaining planar
normal-form obligation is stated as every endpoint of every ambient
side-crossing edge lying in the endpoint support of the mapped collar cut.
-/
structure MinimalCounterexampleBoundarySupportPeeledCollarRouteInputs
    (G : SimpleGraph V) (H : SimpleGraph W) where
  regime : MinimalCounterexamplePeeledCollarRegime G W H
  embedding : H ↪g G
  ambientSideBoundarySupports :
    PeeledCollarCutAmbientSideBoundarySupportsToAmbient embedding

namespace MinimalCounterexampleBoundarySupportPeeledCollarRouteInputs

/-- Boundary-support route inputs supply the endpoint-range route input record. -/
def toEndpointRangeRouteInputs
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleBoundarySupportPeeledCollarRouteInputs G H) :
    MinimalCounterexampleEndpointRangePeeledCollarRouteInputs G H where
  regime := inputs.regime
  embedding := inputs.embedding
  ambientSideEndpointRanges :=
    peeledCollarCutAmbientSideEndpointRangesToAmbient_of_ambientSideBoundarySupports
      inputs.ambientSideBoundarySupports

/-- The boundary-support route inputs supply cyclic five-edge-connectivity for
the peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleBoundarySupportPeeledCollarRouteInputs G H) :
    CyclicallyFiveEdgeConnected H :=
  inputs.toEndpointRangeRouteInputs.cyclicallyFiveEdgeConnected

/-- The boundary-support route inputs supply the no-cyclic-two-cut fact
consumed by the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleBoundarySupportPeeledCollarRouteInputs G H) :
    ClosedCollarForbidsCyclicTwoCut H :=
  inputs.toEndpointRangeRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Boundary-support S4 winding salvage: cyclic five-edge-connectivity is obtained
from the minimal-counterexample normal form plus the planar-facing fact that
ambient side-crossing edge endpoints are supported by the mapped collar cut.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleBoundarySupportPeeledCollarRouteInputs G H) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H :=
  inputs.toEndpointRangeRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable

end MinimalCounterexampleBoundarySupportPeeledCollarRouteInputs

/--
Boundary-edge-set induced index of the regime route inputs: the peeled collar
carrier is the canonical graph induced by the endpoint support of a finite
ambient boundary edge set, with its natural embedding into the ambient graph.
-/
structure MinimalCounterexampleBoundaryEdgeSetInducedPeeledCollarRouteInputs
    (G : SimpleGraph V) (edges : Finset G.edgeSet) where
  regime :
    MinimalCounterexamplePeeledCollarRegime G
      (BoundaryEdgeSetEndpointVertex (G := G) edges)
      (BoundaryEdgeSetInducedGraph (G := G) edges)
  ambientSideBoundarySupports :
    PeeledCollarCutAmbientSideBoundarySupportsToAmbient
      (boundaryEdgeSetInducedGraphEmbedding (G := G) edges)

namespace MinimalCounterexampleBoundaryEdgeSetInducedPeeledCollarRouteInputs

/-- Boundary-edge-set induced route inputs supply the boundary-support route
input record. -/
def toBoundarySupportRouteInputs
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleBoundaryEdgeSetInducedPeeledCollarRouteInputs G edges) :
    MinimalCounterexampleBoundarySupportPeeledCollarRouteInputs G
      (BoundaryEdgeSetInducedGraph (G := G) edges) where
  regime := inputs.regime
  embedding := boundaryEdgeSetInducedGraphEmbedding (G := G) edges
  ambientSideBoundarySupports := inputs.ambientSideBoundarySupports

/-- The boundary-edge-set induced route inputs supply cyclic
five-edge-connectivity for the peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleBoundaryEdgeSetInducedPeeledCollarRouteInputs G edges) :
    CyclicallyFiveEdgeConnected
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toBoundarySupportRouteInputs.cyclicallyFiveEdgeConnected

/-- The boundary-edge-set induced route inputs supply the no-cyclic-two-cut
fact consumed by the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleBoundaryEdgeSetInducedPeeledCollarRouteInputs G edges) :
    ClosedCollarForbidsCyclicTwoCut
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toBoundarySupportRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Boundary-edge-set induced S4 winding salvage: cyclic five-edge-connectivity is
obtained from the minimal-counterexample normal form plus boundary-support
transport for the canonical endpoint-support induced collar graph.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleBoundaryEdgeSetInducedPeeledCollarRouteInputs G edges) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toBoundarySupportRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable

end MinimalCounterexampleBoundaryEdgeSetInducedPeeledCollarRouteInputs

/--
Boundary-carrier endpoint-support index of the regime route inputs: the
peeled collar carrier is the canonical graph induced by a finite ambient edge
set, and the remaining planar-normal-form obligation is only that ambient
side-crossing edges stay inside that carrier endpoint support.
-/
structure MinimalCounterexampleBoundaryCarrierEndpointSupportPeeledCollarRouteInputs
    (G : SimpleGraph V) (edges : Finset G.edgeSet) where
  regime :
    MinimalCounterexamplePeeledCollarRegime G
      (BoundaryEdgeSetEndpointVertex (G := G) edges)
      (BoundaryEdgeSetInducedGraph (G := G) edges)
  ambientSideCarrierEndpointSupports :
    BoundaryEdgeSetInducedCutAmbientSideEndpointSupportsToAmbient (G := G) edges

namespace MinimalCounterexampleBoundaryCarrierEndpointSupportPeeledCollarRouteInputs

/-- Boundary-carrier endpoint route inputs supply the endpoint-range route
input record. -/
def toEndpointRangeRouteInputs
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleBoundaryCarrierEndpointSupportPeeledCollarRouteInputs
        G edges) :
    MinimalCounterexampleEndpointRangePeeledCollarRouteInputs G
      (BoundaryEdgeSetInducedGraph (G := G) edges) where
  regime := inputs.regime
  embedding := boundaryEdgeSetInducedGraphEmbedding (G := G) edges
  ambientSideEndpointRanges :=
    peeledCollarCutAmbientSideEndpointRangesToAmbient_of_boundaryCarrierEndpointSupports
      inputs.ambientSideCarrierEndpointSupports

/-- The boundary-carrier endpoint route inputs supply cyclic
five-edge-connectivity for the peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleBoundaryCarrierEndpointSupportPeeledCollarRouteInputs
        G edges) :
    CyclicallyFiveEdgeConnected
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toEndpointRangeRouteInputs.cyclicallyFiveEdgeConnected

/-- The boundary-carrier endpoint route inputs supply the no-cyclic-two-cut
fact consumed by the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleBoundaryCarrierEndpointSupportPeeledCollarRouteInputs
        G edges) :
    ClosedCollarForbidsCyclicTwoCut
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toEndpointRangeRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Boundary-carrier endpoint S4 winding salvage: cyclic five-edge-connectivity is
obtained from the minimal-counterexample normal form plus the planar-facing
fact that ambient side-crossing edges stay inside the canonical carrier
endpoint support.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleBoundaryCarrierEndpointSupportPeeledCollarRouteInputs
        G edges) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toEndpointRangeRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable

end MinimalCounterexampleBoundaryCarrierEndpointSupportPeeledCollarRouteInputs

/--
Off-carrier walk-consistency index of the regime route inputs: the peeled
collar carrier is the canonical graph induced by a finite ambient edge set,
and the remaining planar-normal-form obligation is that any off-carrier walk
between carrier vertices preserves each small cyclic carrier-cut side.
-/
structure MinimalCounterexampleOffCarrierWalkConsistentPeeledCollarRouteInputs
    (G : SimpleGraph V) (edges : Finset G.edgeSet) where
  regime :
    MinimalCounterexamplePeeledCollarRegime G
      (BoundaryEdgeSetEndpointVertex (G := G) edges)
      (BoundaryEdgeSetInducedGraph (G := G) edges)
  offCarrierWalkConsistencies :
    BoundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient (G := G) edges

namespace MinimalCounterexampleOffCarrierWalkConsistentPeeledCollarRouteInputs

/-- Off-carrier walk-consistency route inputs supply the boundary-carrier
endpoint-support route input record. -/
def toBoundaryCarrierEndpointSupportRouteInputs
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierWalkConsistentPeeledCollarRouteInputs
        G edges) :
    MinimalCounterexampleBoundaryCarrierEndpointSupportPeeledCollarRouteInputs
      G edges where
  regime := inputs.regime
  ambientSideCarrierEndpointSupports :=
    boundaryCarrierEndpointSupports_of_offCarrierWalkConsistencies
      inputs.offCarrierWalkConsistencies

/-- The off-carrier walk-consistency route inputs supply cyclic
five-edge-connectivity for the peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierWalkConsistentPeeledCollarRouteInputs
        G edges) :
    CyclicallyFiveEdgeConnected
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toBoundaryCarrierEndpointSupportRouteInputs.cyclicallyFiveEdgeConnected

/-- The off-carrier walk-consistency route inputs supply the no-cyclic-two-cut
fact consumed by the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierWalkConsistentPeeledCollarRouteInputs
        G edges) :
    ClosedCollarForbidsCyclicTwoCut
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toBoundaryCarrierEndpointSupportRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Off-carrier walk-consistency S4 winding salvage: cyclic five-edge-connectivity
is obtained from the minimal-counterexample normal form plus the planar-facing
fact that off-carrier walks cannot join opposite sides of a small cyclic
carrier cut.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierWalkConsistentPeeledCollarRouteInputs
        G edges) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toBoundaryCarrierEndpointSupportRouteInputs
    |>.closedCollarWindingFreedomEscape_not_simplyRealizable

end MinimalCounterexampleOffCarrierWalkConsistentPeeledCollarRouteInputs

/--
Off-carrier component-attachment index of the regime route inputs: the
remaining planar-normal-form obligation is that each off-carrier component
attaches to only one side of every small cyclic cut in the canonical
endpoint-support carrier.
-/
structure MinimalCounterexampleOffCarrierComponentAttachmentPeeledCollarRouteInputs
    (G : SimpleGraph V) (edges : Finset G.edgeSet) where
  regime :
    MinimalCounterexamplePeeledCollarRegime G
      (BoundaryEdgeSetEndpointVertex (G := G) edges)
      (BoundaryEdgeSetInducedGraph (G := G) edges)
  offCarrierComponentOneSidedAttachments :
    BoundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachmentsToAmbient
      (G := G) edges

namespace MinimalCounterexampleOffCarrierComponentAttachmentPeeledCollarRouteInputs

/-- Component-attachment route inputs supply the off-carrier walk-consistency
route input record. -/
def toOffCarrierWalkConsistentRouteInputs
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierComponentAttachmentPeeledCollarRouteInputs
        G edges) :
    MinimalCounterexampleOffCarrierWalkConsistentPeeledCollarRouteInputs G
      edges where
  regime := inputs.regime
  offCarrierWalkConsistencies :=
    boundaryEdgeSetInducedCutOffCarrierWalkConsistenciesToAmbient_of_oppositeSideDisconnections
      (boundaryEdgeSetInducedCutOffCarrierOppositeSideDisconnectionsToAmbient_of_componentOneSidedAttachments
        inputs.offCarrierComponentOneSidedAttachments)

/-- The component-attachment route inputs supply cyclic five-edge-connectivity
for the peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierComponentAttachmentPeeledCollarRouteInputs
        G edges) :
    CyclicallyFiveEdgeConnected
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toOffCarrierWalkConsistentRouteInputs.cyclicallyFiveEdgeConnected

/-- The component-attachment route inputs supply the no-cyclic-two-cut fact
consumed by the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierComponentAttachmentPeeledCollarRouteInputs
        G edges) :
    ClosedCollarForbidsCyclicTwoCut
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toOffCarrierWalkConsistentRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Off-carrier component-attachment S4 winding salvage: cyclic
five-edge-connectivity is obtained from the minimal-counterexample normal form
plus the planar-facing fact that no off-carrier component attaches to both
sides of a small cyclic carrier cut.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierComponentAttachmentPeeledCollarRouteInputs
        G edges) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toOffCarrierWalkConsistentRouteInputs
    |>.closedCollarWindingFreedomEscape_not_simplyRealizable

end MinimalCounterexampleOffCarrierComponentAttachmentPeeledCollarRouteInputs

/--
Off-carrier attachment-carrier-connectivity index of the regime route inputs:
the remaining planar-normal-form obligation is that attachments of one
off-carrier component are connected in the carrier after deleting the small
carrier-cut edge support.
-/
structure MinimalCounterexampleOffCarrierAttachmentCarrierConnectedPeeledCollarRouteInputs
    (G : SimpleGraph V) (edges : Finset G.edgeSet) where
  regime :
    MinimalCounterexamplePeeledCollarRegime G
      (BoundaryEdgeSetEndpointVertex (G := G) edges)
      (BoundaryEdgeSetInducedGraph (G := G) edges)
  offCarrierAttachmentCarrierConnectivities :
    BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCarrierConnectivitiesToAmbient
      (G := G) edges

namespace MinimalCounterexampleOffCarrierAttachmentCarrierConnectedPeeledCollarRouteInputs

/-- Attachment-carrier-connectivity route inputs supply the component-attachment
route input record. -/
def toComponentAttachmentRouteInputs
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierAttachmentCarrierConnectedPeeledCollarRouteInputs
        G edges) :
    MinimalCounterexampleOffCarrierComponentAttachmentPeeledCollarRouteInputs G
      edges where
  regime := inputs.regime
  offCarrierComponentOneSidedAttachments :=
    boundaryEdgeSetInducedCutOffCarrierComponentOneSidedAttachmentsToAmbient_of_attachmentCarrierConnectivities
      inputs.offCarrierAttachmentCarrierConnectivities

/-- The attachment-carrier-connectivity route inputs supply cyclic
five-edge-connectivity for the peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierAttachmentCarrierConnectedPeeledCollarRouteInputs
        G edges) :
    CyclicallyFiveEdgeConnected
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toComponentAttachmentRouteInputs.cyclicallyFiveEdgeConnected

/-- The attachment-carrier-connectivity route inputs supply the no-cyclic-two-cut
fact consumed by the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierAttachmentCarrierConnectedPeeledCollarRouteInputs
        G edges) :
    ClosedCollarForbidsCyclicTwoCut
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toComponentAttachmentRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Off-carrier attachment-carrier-connectivity S4 winding salvage: cyclic
five-edge-connectivity is obtained from the minimal-counterexample normal form
plus the planar-facing carrier-walk connectivity of off-carrier attachments.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierAttachmentCarrierConnectedPeeledCollarRouteInputs
        G edges) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toComponentAttachmentRouteInputs
    |>.closedCollarWindingFreedomEscape_not_simplyRealizable

end MinimalCounterexampleOffCarrierAttachmentCarrierConnectedPeeledCollarRouteInputs

/--
Cut-avoiding shared-endpoint boundary-route index of the regime route inputs:
the remaining planar-normal-form obligation is that attachments of one
off-carrier component can be joined by a shared-endpoint selected-boundary
route avoiding the mapped carrier cut.
-/
structure MinimalCounterexampleOffCarrierCutAvoidingSharedEndpointPeeledCollarRouteInputs
    (G : SimpleGraph V) (edges : Finset G.edgeSet) where
  regime :
    MinimalCounterexamplePeeledCollarRegime G
      (BoundaryEdgeSetEndpointVertex (G := G) edges)
      (BoundaryEdgeSetInducedGraph (G := G) edges)
  offCarrierCutAvoidingSharedEndpointReachabilities :
    BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachabilitiesToAmbient
      (G := G) edges

namespace MinimalCounterexampleOffCarrierCutAvoidingSharedEndpointPeeledCollarRouteInputs

/-- Cut-avoiding shared-endpoint route inputs supply the
attachment-carrier-connectivity route input record. -/
def toAttachmentCarrierConnectedRouteInputs
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierCutAvoidingSharedEndpointPeeledCollarRouteInputs
        G edges) :
    MinimalCounterexampleOffCarrierAttachmentCarrierConnectedPeeledCollarRouteInputs
      G edges where
  regime := inputs.regime
  offCarrierAttachmentCarrierConnectivities :=
    boundaryEdgeSetInducedCutOffCarrierComponentAttachmentCarrierConnectivitiesToAmbient_of_cutAvoidingSharedEndpointReachabilities
      inputs.offCarrierCutAvoidingSharedEndpointReachabilities

/-- Cut-avoiding shared-endpoint route inputs supply cyclic
five-edge-connectivity for the peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierCutAvoidingSharedEndpointPeeledCollarRouteInputs
        G edges) :
    CyclicallyFiveEdgeConnected
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toAttachmentCarrierConnectedRouteInputs.cyclicallyFiveEdgeConnected

/-- Cut-avoiding shared-endpoint route inputs supply the no-cyclic-two-cut
fact consumed by the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierCutAvoidingSharedEndpointPeeledCollarRouteInputs
        G edges) :
    ClosedCollarForbidsCyclicTwoCut
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toAttachmentCarrierConnectedRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Cut-avoiding shared-endpoint S4 winding salvage: cyclic five-edge-connectivity
is obtained from the minimal-counterexample normal form plus cut-avoiding
shared-endpoint boundary routes for off-carrier attachments.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierCutAvoidingSharedEndpointPeeledCollarRouteInputs
        G edges) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toAttachmentCarrierConnectedRouteInputs
    |>.closedCollarWindingFreedomEscape_not_simplyRealizable

end MinimalCounterexampleOffCarrierCutAvoidingSharedEndpointPeeledCollarRouteInputs

/--
Mapped-cut-deleted shared-endpoint boundary-connectivity index of the regime
route inputs: the remaining planar-normal-form obligation is that attachments
of one off-carrier component are connected in the selected-boundary
shared-endpoint graph after deleting the mapped carrier cut.
-/
structure MinimalCounterexampleOffCarrierMappedCutAvoidingSharedEndpointConnectedPeeledCollarRouteInputs
    (G : SimpleGraph V) (edges : Finset G.edgeSet) where
  regime :
    MinimalCounterexamplePeeledCollarRegime G
      (BoundaryEdgeSetEndpointVertex (G := G) edges)
      (BoundaryEdgeSetInducedGraph (G := G) edges)
  offCarrierMappedCutAvoidingSharedEndpointConnectivities :
    BoundaryEdgeSetInducedCutOffCarrierComponentAttachmentMappedCutAvoidingSharedEndpointConnectivitiesToAmbient
      (G := G) edges

namespace MinimalCounterexampleOffCarrierMappedCutAvoidingSharedEndpointConnectedPeeledCollarRouteInputs

/-- Mapped-cut-deleted shared-endpoint connectivity supplies the
cut-avoiding shared-endpoint route input record. -/
def toCutAvoidingSharedEndpointRouteInputs
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierMappedCutAvoidingSharedEndpointConnectedPeeledCollarRouteInputs
        G edges) :
    MinimalCounterexampleOffCarrierCutAvoidingSharedEndpointPeeledCollarRouteInputs
      G edges where
  regime := inputs.regime
  offCarrierCutAvoidingSharedEndpointReachabilities :=
    boundaryEdgeSetInducedCutOffCarrierComponentAttachmentCutAvoidingSharedEndpointReachabilitiesToAmbient_of_mappedCutAvoidingSharedEndpointConnectivities
      inputs.offCarrierMappedCutAvoidingSharedEndpointConnectivities

/-- Mapped-cut-deleted shared-endpoint connectivity inputs supply cyclic
five-edge-connectivity for the peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierMappedCutAvoidingSharedEndpointConnectedPeeledCollarRouteInputs
        G edges) :
    CyclicallyFiveEdgeConnected
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toCutAvoidingSharedEndpointRouteInputs.cyclicallyFiveEdgeConnected

/-- Mapped-cut-deleted shared-endpoint connectivity inputs supply the
no-cyclic-two-cut fact consumed by the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierMappedCutAvoidingSharedEndpointConnectedPeeledCollarRouteInputs
        G edges) :
    ClosedCollarForbidsCyclicTwoCut
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toCutAvoidingSharedEndpointRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Mapped-cut-deleted shared-endpoint S4 winding salvage: cyclic
five-edge-connectivity is obtained from the minimal-counterexample normal form
plus connectedness in the selected-boundary graph after deleting the mapped
carrier cut.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {edges : Finset G.edgeSet}
    (inputs :
      MinimalCounterexampleOffCarrierMappedCutAvoidingSharedEndpointConnectedPeeledCollarRouteInputs
        G edges) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      (BoundaryEdgeSetInducedGraph (G := G) edges) :=
  inputs.toCutAvoidingSharedEndpointRouteInputs
    |>.closedCollarWindingFreedomEscape_not_simplyRealizable

end MinimalCounterexampleOffCarrierMappedCutAvoidingSharedEndpointConnectedPeeledCollarRouteInputs

/--
Off-boundary index of the regime route inputs: the remaining planar
normal-form obligation is stated locally, as no ambient side-crossing edge
being incident to a vertex outside the mapped collar-cut endpoint support.
-/
structure MinimalCounterexampleOffBoundaryPeeledCollarRouteInputs
    (G : SimpleGraph V) (H : SimpleGraph W) where
  regime : MinimalCounterexamplePeeledCollarRegime G W H
  embedding : H ↪g G
  ambientSideOffBoundaryNoCrossings :
    PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient embedding

namespace MinimalCounterexampleOffBoundaryPeeledCollarRouteInputs

/-- Off-boundary route inputs supply the boundary-support route input record. -/
def toBoundarySupportRouteInputs
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleOffBoundaryPeeledCollarRouteInputs G H) :
    MinimalCounterexampleBoundarySupportPeeledCollarRouteInputs G H where
  regime := inputs.regime
  embedding := inputs.embedding
  ambientSideBoundarySupports :=
    peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSideOffBoundaryNoCrossings
      inputs.ambientSideOffBoundaryNoCrossings

/-- The off-boundary route inputs supply cyclic five-edge-connectivity for the
peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleOffBoundaryPeeledCollarRouteInputs G H) :
    CyclicallyFiveEdgeConnected H :=
  inputs.toBoundarySupportRouteInputs.cyclicallyFiveEdgeConnected

/-- The off-boundary route inputs supply the no-cyclic-two-cut fact consumed
by the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleOffBoundaryPeeledCollarRouteInputs G H) :
    ClosedCollarForbidsCyclicTwoCut H :=
  inputs.toBoundarySupportRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Off-boundary S4 winding salvage: cyclic five-edge-connectivity is obtained
from the minimal-counterexample normal form plus the local planar-facing fact
that ambient side-crossing edges cannot touch off-boundary vertices.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleOffBoundaryPeeledCollarRouteInputs G H) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H :=
  inputs.toBoundarySupportRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable

end MinimalCounterexampleOffBoundaryPeeledCollarRouteInputs

/--
Local-constancy index of the regime route inputs: the remaining planar
normal-form obligation is stated edge-locally, as filled-side constancy across
any ambient edge incident to a vertex outside the mapped collar-cut endpoint
support.
-/
structure MinimalCounterexampleLocalConstancyPeeledCollarRouteInputs
    (G : SimpleGraph V) (H : SimpleGraph W) where
  regime : MinimalCounterexamplePeeledCollarRegime G W H
  embedding : H ↪g G
  ambientSideLocalConstancies :
    PeeledCollarCutAmbientSideLocalConstanciesToAmbient embedding

namespace MinimalCounterexampleLocalConstancyPeeledCollarRouteInputs

/-- Local-constancy route inputs supply the off-boundary route input record. -/
def toOffBoundaryRouteInputs
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleLocalConstancyPeeledCollarRouteInputs G H) :
    MinimalCounterexampleOffBoundaryPeeledCollarRouteInputs G H where
  regime := inputs.regime
  embedding := inputs.embedding
  ambientSideOffBoundaryNoCrossings :=
    peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_localConstancies
      inputs.ambientSideLocalConstancies

/-- The local-constancy route inputs supply cyclic five-edge-connectivity for
the peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleLocalConstancyPeeledCollarRouteInputs G H) :
    CyclicallyFiveEdgeConnected H :=
  inputs.toOffBoundaryRouteInputs.cyclicallyFiveEdgeConnected

/-- The local-constancy route inputs supply the no-cyclic-two-cut fact consumed
by the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleLocalConstancyPeeledCollarRouteInputs G H) :
    ClosedCollarForbidsCyclicTwoCut H :=
  inputs.toOffBoundaryRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Local-constancy S4 winding salvage: cyclic five-edge-connectivity is obtained
from the minimal-counterexample normal form plus the planar-facing fact that
the filled side is locally constant off the mapped collar-cut boundary.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleLocalConstancyPeeledCollarRouteInputs G H) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H :=
  inputs.toOffBoundaryRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable

end MinimalCounterexampleLocalConstancyPeeledCollarRouteInputs

/--
Annulus-extraction index of the regime route inputs: the remaining foundation
target is tied to an existing annulus collar geometry package and an embedded
collar graph, and asks for the equivalent local/off-boundary side condition.
-/
structure MinimalCounterexampleAnnulusExtractionPeeledCollarRouteInputs
    (G : SimpleGraph V) (H : SimpleGraph W) where
  regime : MinimalCounterexamplePeeledCollarRegime G W H
  ambientBoundaryEmbedding : PlaneEmbeddingWithBoundary G
  annulusGeometry :
    PlanarBoundaryAnnulusCollarGeometry ambientBoundaryEmbedding
  embedding : H ↪g G
  annulusExtractionLocalConstancy :
    PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget
      annulusGeometry embedding

namespace MinimalCounterexampleAnnulusExtractionPeeledCollarRouteInputs

/-- Build annulus-extraction route inputs from the equivalent separation-form
annulus target. -/
def of_separationTarget
    {G : SimpleGraph V} {H : SimpleGraph W}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H)
    (ambientBoundaryEmbedding : PlaneEmbeddingWithBoundary G)
    (annulusGeometry :
      PlanarBoundaryAnnulusCollarGeometry ambientBoundaryEmbedding)
    (embedding : H ↪g G)
    (hseparate :
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget
        annulusGeometry embedding) :
    MinimalCounterexampleAnnulusExtractionPeeledCollarRouteInputs G H where
  regime := regime
  ambientBoundaryEmbedding := ambientBoundaryEmbedding
  annulusGeometry := annulusGeometry
  embedding := embedding
  annulusExtractionLocalConstancy :=
    planarBoundaryAnnulusPeeledCollarLocalConstancyTarget_of_separationTarget
      hseparate

/-- Annulus-extraction route inputs supply the local-constancy route input
record. -/
def toLocalConstancyRouteInputs
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleAnnulusExtractionPeeledCollarRouteInputs G H) :
    MinimalCounterexampleLocalConstancyPeeledCollarRouteInputs G H where
  regime := inputs.regime
  embedding := inputs.embedding
  ambientSideLocalConstancies :=
    peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_annulusExtractionTarget
      inputs.annulusExtractionLocalConstancy

/-- The annulus-extraction route inputs supply cyclic five-edge-connectivity
for the peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleAnnulusExtractionPeeledCollarRouteInputs G H) :
    CyclicallyFiveEdgeConnected H :=
  inputs.toLocalConstancyRouteInputs.cyclicallyFiveEdgeConnected

/-- The annulus-extraction route inputs supply the no-cyclic-two-cut fact
consumed by the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleAnnulusExtractionPeeledCollarRouteInputs G H) :
    ClosedCollarForbidsCyclicTwoCut H :=
  inputs.toLocalConstancyRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Annulus-extraction S4 winding salvage: cyclic five-edge-connectivity is
obtained from the minimal-counterexample normal form plus the named annulus
extraction target for the embedded peeled collar.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {H : SimpleGraph W}
    (inputs : MinimalCounterexampleAnnulusExtractionPeeledCollarRouteInputs G H) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H :=
  inputs.toLocalConstancyRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable

end MinimalCounterexampleAnnulusExtractionPeeledCollarRouteInputs

/--
Canonical annulus index of the regime route inputs: the peeled collar is the
canonical endpoint-support induced graph selected by an annulus collar
geometry.  The remaining planar-normal-form inputs are selected-boundary
inducedness and the annulus local-constancy extraction target.
-/
structure MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) where
  regime :
    MinimalCounterexamplePeeledCollarRegime G
      (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
      data.inducedBoundaryGraph
  selectedBoundaryInduced : SelectedBoundaryInducedSubgraph emb
  annulusExtractionLocalConstancy :
    PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget
      data data.inducedBoundaryEmbedding

namespace MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs

/--
Build canonical annulus route inputs from induced outer/inner boundary
components plus cross-component chord-freeness.
-/
def of_inducedBoundaryComponents_of_crossComponentChordFree
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (hOuter : BoundaryEdgeSetInducedSubgraph data.outerAmbientBoundary)
    (hInner : BoundaryEdgeSetInducedSubgraph data.innerAmbientBoundary)
    (hCross :
      BoundaryEdgeSetCrossComponentChordFree
        data.outerAmbientBoundary data.innerAmbientBoundary)
    (hlocal :
      PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget
        data data.inducedBoundaryEmbedding) :
    MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs data where
  regime := regime
  selectedBoundaryInduced :=
    data.boundaryData
      |>.selectedBoundaryInducedSubgraph_of_inducedBoundaryComponents_of_crossComponentChordFree
        hOuter hInner hCross
  annulusExtractionLocalConstancy := hlocal

/--
Build canonical annulus route inputs from component inducedness and the
equivalent separation-form annulus target.
-/
def of_inducedBoundaryComponents_of_crossComponentChordFree_of_separation
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (hOuter : BoundaryEdgeSetInducedSubgraph data.outerAmbientBoundary)
    (hInner : BoundaryEdgeSetInducedSubgraph data.innerAmbientBoundary)
    (hCross :
      BoundaryEdgeSetCrossComponentChordFree
        data.outerAmbientBoundary data.innerAmbientBoundary)
    (hseparate :
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding) :
    MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs data :=
  of_inducedBoundaryComponents_of_crossComponentChordFree
    regime hOuter hInner hCross
    (planarBoundaryAnnulusPeeledCollarLocalConstancyTarget_of_separationTarget
      hseparate)

/-- Canonical annulus route inputs supply the off-carrier walk-consistency
route input record. -/
def toOffCarrierWalkConsistentRouteInputs
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs :
      MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs data) :
    MinimalCounterexampleOffCarrierWalkConsistentPeeledCollarRouteInputs G
      data.ambientBoundaryEdgeSet where
  regime := inputs.regime
  offCarrierWalkConsistencies :=
    data.boundaryData
      |>.offCarrierWalkConsistencyTarget_of_selectedBoundaryInducedSubgraph_of_localConstancies
        inputs.selectedBoundaryInduced
        inputs.annulusExtractionLocalConstancy

/-- The canonical annulus route inputs supply cyclic five-edge-connectivity for
the peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs :
      MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs data) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  inputs.toOffCarrierWalkConsistentRouteInputs.cyclicallyFiveEdgeConnected

/-- The canonical annulus route inputs supply the no-cyclic-two-cut fact
consumed by the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs :
      MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs data) :
    ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph :=
  inputs.toOffCarrierWalkConsistentRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Canonical-annulus S4 winding salvage: cyclic five-edge-connectivity is
obtained from the minimal-counterexample normal form, selected-boundary
inducedness, and the annulus local-constancy extraction target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs :
      MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs data) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  inputs.toOffCarrierWalkConsistentRouteInputs
    |>.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
Component-induced canonical-annulus S4 winding salvage: selected-boundary
inducedness is supplied by induced outer/inner boundary components and
cross-component chord-freeness.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_inducedBoundaryComponents
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (hOuter : BoundaryEdgeSetInducedSubgraph data.outerAmbientBoundary)
    (hInner : BoundaryEdgeSetInducedSubgraph data.innerAmbientBoundary)
    (hCross :
      BoundaryEdgeSetCrossComponentChordFree
        data.outerAmbientBoundary data.innerAmbientBoundary)
    (hlocal :
      PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget
        data data.inducedBoundaryEmbedding) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  (of_inducedBoundaryComponents_of_crossComponentChordFree
    regime hOuter hInner hCross hlocal)
      |>.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
Component-induced canonical-annulus S4 winding salvage from the separation-form
annulus target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_inducedBoundaryComponents_of_separation
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (hOuter : BoundaryEdgeSetInducedSubgraph data.outerAmbientBoundary)
    (hInner : BoundaryEdgeSetInducedSubgraph data.innerAmbientBoundary)
    (hCross :
      BoundaryEdgeSetCrossComponentChordFree
        data.outerAmbientBoundary data.innerAmbientBoundary)
    (hseparate :
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  (of_inducedBoundaryComponents_of_crossComponentChordFree_of_separation
    regime hOuter hInner hCross hseparate)
      |>.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
Canonical-annulus S4 winding salvage from the off-carrier walk-consistency
target.  This is the direct entry point when the planar normal-form layer
proves that off-carrier walks cannot connect opposite sides of a small cyclic
carrier cut.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  (MinimalCounterexampleOffCarrierWalkConsistentPeeledCollarRouteInputs.mk
    regime h)
      |>.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
Canonical-annulus S4 winding salvage from the separation-form annulus target.
The separation target is converted to off-carrier walk consistency by the
canonical endpoint-support carrier bridge, so no selected-boundary inducedness
is needed for this route.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_separationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (hseparate :
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomEscape_not_simplyRealizable_of_offCarrierWalkConsistencyTarget
    regime
    (planarBoundaryAnnulusPeeledCollarOffCarrierWalkConsistencyTarget_of_separationTarget
      hseparate)

/--
Canonical-annulus S4 winding salvage from the direct no-opposite-side
off-carrier target.  This is the graph-facing form expected from a planar
annulus separation proof.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_oppositeSideTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget data) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomEscape_not_simplyRealizable_of_offCarrierWalkConsistencyTarget
    regime
    (planarBoundaryAnnulusPeeledCollarOffCarrierWalkConsistencyTarget_of_oppositeSideTarget
      h)

/--
Canonical-annulus S4 winding salvage from the component-facing off-carrier
attachment target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_componentAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierComponentAttachmentTarget
        data) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomEscape_not_simplyRealizable_of_oppositeSideTarget
    regime
    (planarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget_of_componentAttachmentTarget
      h)

/--
Canonical-annulus S4 winding salvage from the attachment-carrier-connectivity
target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_attachmentCarrierConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentCarrierConnectivityTarget
        data) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomEscape_not_simplyRealizable_of_componentAttachmentTarget
    regime
    (planarBoundaryAnnulusPeeledCollarOffCarrierComponentAttachmentTarget_of_attachmentCarrierConnectivityTarget
      h)

/--
Canonical-annulus S4 winding salvage from the cut-avoiding shared-endpoint
boundary-route target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_cutAvoidingSharedEndpointReachabilityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget
        data) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomEscape_not_simplyRealizable_of_attachmentCarrierConnectivityTarget
    regime
    (planarBoundaryAnnulusPeeledCollarOffCarrierAttachmentCarrierConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
      h)

/--
Canonical-annulus S4 winding salvage from the mapped-cut-deleted
shared-endpoint connectivity target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_mappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h : data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomEscape_not_simplyRealizable_of_cutAvoidingSharedEndpointReachabilityTarget
    regime
    (data.cutAvoidingSharedEndpointReachabilityTarget_of_mappedCutAvoidingSharedEndpointConnectivityTarget
      h)

end MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs

/--
Separation-only canonical annulus index of the regime route inputs.  This is
the interface expected from the remaining planar annulus foundation theorem:
the minimal-counterexample regime plus no-avoiding-walk separation for the
canonical induced boundary carrier.  It deliberately does not carry selected
boundary inducedness.
-/
structure MinimalCounterexampleCanonicalAnnulusSeparationPeeledCollarRouteInputs
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) where
  regime :
    MinimalCounterexamplePeeledCollarRegime G
      (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
      data.inducedBoundaryGraph
  annulusSeparation :
    PlanarBoundaryAnnulusPeeledCollarSeparationTarget
      data data.inducedBoundaryEmbedding

namespace MinimalCounterexampleCanonicalAnnulusSeparationPeeledCollarRouteInputs

/-- Separation-only canonical annulus inputs supply the off-carrier
walk-consistency route input record. -/
def toOffCarrierWalkConsistentRouteInputs
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs :
      MinimalCounterexampleCanonicalAnnulusSeparationPeeledCollarRouteInputs
        data) :
    MinimalCounterexampleOffCarrierWalkConsistentPeeledCollarRouteInputs G
      data.ambientBoundaryEdgeSet where
  regime := inputs.regime
  offCarrierWalkConsistencies :=
    planarBoundaryAnnulusPeeledCollarOffCarrierWalkConsistencyTarget_of_separationTarget
      inputs.annulusSeparation

/-- Separation-only canonical annulus inputs supply cyclic
five-edge-connectivity for the peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs :
      MinimalCounterexampleCanonicalAnnulusSeparationPeeledCollarRouteInputs
        data) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  inputs.toOffCarrierWalkConsistentRouteInputs.cyclicallyFiveEdgeConnected

/-- Separation-only canonical annulus inputs supply the no-cyclic-two-cut fact
consumed by the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs :
      MinimalCounterexampleCanonicalAnnulusSeparationPeeledCollarRouteInputs
        data) :
    ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph :=
  inputs.toOffCarrierWalkConsistentRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Separation-only canonical-annulus S4 winding salvage: cyclic
five-edge-connectivity is obtained from the minimal-counterexample normal form
and the named annulus separation target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs :
      MinimalCounterexampleCanonicalAnnulusSeparationPeeledCollarRouteInputs
        data) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  inputs.toOffCarrierWalkConsistentRouteInputs
    |>.closedCollarWindingFreedomEscape_not_simplyRealizable

end MinimalCounterexampleCanonicalAnnulusSeparationPeeledCollarRouteInputs

/--
Repaired annulus index of the regime route inputs: the peeled collar is the
canonical endpoint-support induced graph selected by a repaired annulus
geometry.  This version keeps the stronger previous-boundary witness geometry
in the public route interface.
-/
structure MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) where
  regime :
    MinimalCounterexamplePeeledCollarRegime G
      (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
      data.inducedBoundaryGraph
  selectedBoundaryInduced : SelectedBoundaryInducedSubgraph emb
  previousBoundaryAnnulusExtractionLocalConstancy :
    PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget
      data data.inducedBoundaryEmbedding

namespace MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs

/--
Build repaired annulus route inputs from induced outer/inner boundary
components plus cross-component chord-freeness.
-/
def of_inducedBoundaryComponents_of_crossComponentChordFree
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (hOuter : BoundaryEdgeSetInducedSubgraph data.outerAmbientBoundary)
    (hInner : BoundaryEdgeSetInducedSubgraph data.innerAmbientBoundary)
    (hCross :
      BoundaryEdgeSetCrossComponentChordFree
        data.outerAmbientBoundary data.innerAmbientBoundary)
    (hlocal :
      PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget
        data data.inducedBoundaryEmbedding) :
    MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs data where
  regime := regime
  selectedBoundaryInduced :=
    data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData
      |>.selectedBoundaryInducedSubgraph_of_inducedBoundaryComponents_of_crossComponentChordFree
        hOuter hInner hCross
  previousBoundaryAnnulusExtractionLocalConstancy := hlocal

/--
Build repaired annulus route inputs from component inducedness and the
equivalent separation-form previous-boundary annulus target.
-/
def of_inducedBoundaryComponents_of_crossComponentChordFree_of_separation
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (hOuter : BoundaryEdgeSetInducedSubgraph data.outerAmbientBoundary)
    (hInner : BoundaryEdgeSetInducedSubgraph data.innerAmbientBoundary)
    (hCross :
      BoundaryEdgeSetCrossComponentChordFree
        data.outerAmbientBoundary data.innerAmbientBoundary)
    (hseparate :
      PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding) :
    MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs data :=
  of_inducedBoundaryComponents_of_crossComponentChordFree
    regime hOuter hInner hCross
    (planarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget_of_separationTarget
      hseparate)

/-- Repaired annulus route inputs supply the off-carrier walk-consistency route
input record. -/
def toOffCarrierWalkConsistentRouteInputs
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs :
      MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs data) :
    MinimalCounterexampleOffCarrierWalkConsistentPeeledCollarRouteInputs G
      data.ambientBoundaryEdgeSet where
  regime := inputs.regime
  offCarrierWalkConsistencies :=
    data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData
      |>.offCarrierWalkConsistencyTarget_of_selectedBoundaryInducedSubgraph_of_localConstancies
        inputs.selectedBoundaryInduced
        inputs.previousBoundaryAnnulusExtractionLocalConstancy

/-- The repaired annulus route inputs supply cyclic five-edge-connectivity for
the peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs :
      MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs data) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  inputs.toOffCarrierWalkConsistentRouteInputs.cyclicallyFiveEdgeConnected

/-- The repaired annulus route inputs supply the no-cyclic-two-cut fact
consumed by the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs :
      MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs data) :
    ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph :=
  inputs.toOffCarrierWalkConsistentRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Repaired-annulus S4 winding salvage: cyclic five-edge-connectivity is obtained
from the minimal-counterexample normal form, selected-boundary inducedness, and
the repaired annulus local-constancy extraction target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs :
      MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs data) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  inputs.toOffCarrierWalkConsistentRouteInputs
    |>.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
Component-induced repaired-annulus S4 winding salvage: selected-boundary
inducedness is supplied by induced outer/inner boundary components and
cross-component chord-freeness.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_inducedBoundaryComponents
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (hOuter : BoundaryEdgeSetInducedSubgraph data.outerAmbientBoundary)
    (hInner : BoundaryEdgeSetInducedSubgraph data.innerAmbientBoundary)
    (hCross :
      BoundaryEdgeSetCrossComponentChordFree
        data.outerAmbientBoundary data.innerAmbientBoundary)
    (hlocal :
      PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget
        data data.inducedBoundaryEmbedding) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  (of_inducedBoundaryComponents_of_crossComponentChordFree
    regime hOuter hInner hCross hlocal)
      |>.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
Component-induced repaired-annulus S4 winding salvage from the separation-form
previous-boundary annulus target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_inducedBoundaryComponents_of_separation
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (hOuter : BoundaryEdgeSetInducedSubgraph data.outerAmbientBoundary)
    (hInner : BoundaryEdgeSetInducedSubgraph data.innerAmbientBoundary)
    (hCross :
      BoundaryEdgeSetCrossComponentChordFree
        data.outerAmbientBoundary data.innerAmbientBoundary)
    (hseparate :
      PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  (of_inducedBoundaryComponents_of_crossComponentChordFree_of_separation
    regime hOuter hInner hCross hseparate)
      |>.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
Repaired-annulus S4 winding salvage from the off-carrier walk-consistency
target.  This is the direct entry point when the planar normal-form layer
proves that off-carrier walks cannot connect opposite sides of a small cyclic
carrier cut.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h : data.PeeledCollarOffCarrierWalkConsistencyTarget) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  (MinimalCounterexampleOffCarrierWalkConsistentPeeledCollarRouteInputs.mk
    regime h)
      |>.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
Repaired-annulus S4 winding salvage from the separation-form previous-boundary
annulus target.  The separation target is converted to off-carrier walk
consistency by the canonical endpoint-support carrier bridge, so no
selected-boundary inducedness is needed for this route.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_separationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (hseparate :
      PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomEscape_not_simplyRealizable_of_offCarrierWalkConsistencyTarget
    regime
    (planarBoundaryPreviousBoundaryPeeledCollarOffCarrierWalkConsistencyTarget_of_separationTarget
      hseparate)

/--
Repaired-annulus S4 winding salvage from the direct no-opposite-side
off-carrier target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_oppositeSideTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget
        data) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomEscape_not_simplyRealizable_of_offCarrierWalkConsistencyTarget
    regime
    (planarBoundaryPreviousBoundaryPeeledCollarOffCarrierWalkConsistencyTarget_of_oppositeSideTarget
      h)

/--
Repaired-annulus S4 winding salvage from the component-facing off-carrier
attachment target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_componentAttachmentTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierComponentAttachmentTarget
        data) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomEscape_not_simplyRealizable_of_oppositeSideTarget
    regime
    (planarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget_of_componentAttachmentTarget
      h)

/--
Repaired-annulus S4 winding salvage from the attachment-carrier-connectivity
target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_attachmentCarrierConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentCarrierConnectivityTarget
        data) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomEscape_not_simplyRealizable_of_componentAttachmentTarget
    regime
    (planarBoundaryPreviousBoundaryPeeledCollarOffCarrierComponentAttachmentTarget_of_attachmentCarrierConnectivityTarget
      h)

/--
Repaired-annulus S4 winding salvage from the cut-avoiding shared-endpoint
boundary-route target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_cutAvoidingSharedEndpointReachabilityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget
        data) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomEscape_not_simplyRealizable_of_attachmentCarrierConnectivityTarget
    regime
    (planarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentCarrierConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
      h)

/--
Repaired-annulus S4 winding salvage from the mapped-cut-deleted
shared-endpoint connectivity target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_mappedCutAvoidingSharedEndpointConnectivityTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (h : data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomEscape_not_simplyRealizable_of_cutAvoidingSharedEndpointReachabilityTarget
    regime
    (data.cutAvoidingSharedEndpointReachabilityTarget_of_mappedCutAvoidingSharedEndpointConnectivityTarget
      h)

end MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs

/--
Separation-only repaired annulus index of the regime route inputs.  This is
the repaired-geometry variant of the exact planar foundation interface: the
minimal-counterexample regime plus no-avoiding-walk separation for the
canonical induced boundary carrier.
-/
structure MinimalCounterexampleRepairedAnnulusSeparationPeeledCollarRouteInputs
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) where
  regime :
    MinimalCounterexamplePeeledCollarRegime G
      (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
      data.inducedBoundaryGraph
  annulusSeparation :
    PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
      data data.inducedBoundaryEmbedding

namespace MinimalCounterexampleRepairedAnnulusSeparationPeeledCollarRouteInputs

/-- Separation-only repaired annulus inputs supply the off-carrier
walk-consistency route input record. -/
def toOffCarrierWalkConsistentRouteInputs
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs :
      MinimalCounterexampleRepairedAnnulusSeparationPeeledCollarRouteInputs
        data) :
    MinimalCounterexampleOffCarrierWalkConsistentPeeledCollarRouteInputs G
      data.ambientBoundaryEdgeSet where
  regime := inputs.regime
  offCarrierWalkConsistencies :=
    planarBoundaryPreviousBoundaryPeeledCollarOffCarrierWalkConsistencyTarget_of_separationTarget
      inputs.annulusSeparation

/-- Separation-only repaired annulus inputs supply cyclic
five-edge-connectivity for the peeled collar. -/
theorem cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs :
      MinimalCounterexampleRepairedAnnulusSeparationPeeledCollarRouteInputs
        data) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  inputs.toOffCarrierWalkConsistentRouteInputs.cyclicallyFiveEdgeConnected

/-- Separation-only repaired annulus inputs supply the no-cyclic-two-cut fact
consumed by the closed-collar winding theorem. -/
theorem closedCollarForbidsCyclicTwoCut
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs :
      MinimalCounterexampleRepairedAnnulusSeparationPeeledCollarRouteInputs
        data) :
    ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph :=
  inputs.toOffCarrierWalkConsistentRouteInputs.closedCollarForbidsCyclicTwoCut

/--
Separation-only repaired-annulus S4 winding salvage: cyclic
five-edge-connectivity is obtained from the minimal-counterexample normal form
and the named previous-boundary annulus separation target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs :
      MinimalCounterexampleRepairedAnnulusSeparationPeeledCollarRouteInputs
        data) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  inputs.toOffCarrierWalkConsistentRouteInputs
    |>.closedCollarWindingFreedomEscape_not_simplyRealizable

end MinimalCounterexampleRepairedAnnulusSeparationPeeledCollarRouteInputs

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

/--
End-to-end S4 salvage target using the no-avoiding-walk side-separation route
interface.
-/
def Section92Step4SeparatedRegimeDischargedS4SalvageTarget : Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W},
      MinimalCounterexampleSeparatedPeeledCollarRouteInputs G H →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H

/-- Verbatim end-to-end separation-regime S4 salvage statement. -/
theorem section92Step4SeparatedRegimeDischargedS4SalvageTarget :
    Section92Step4SeparatedRegimeDischargedS4SalvageTarget := by
  intro V W _ _ G H inputs
  exact inputs.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the edge-barrier route interface.
-/
def Section92Step4BarrierRegimeDischargedS4SalvageTarget : Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W},
      MinimalCounterexampleBarrierPeeledCollarRouteInputs G H →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H

/-- Verbatim end-to-end barrier-regime S4 salvage statement. -/
theorem section92Step4BarrierRegimeDischargedS4SalvageTarget :
    Section92Step4BarrierRegimeDischargedS4SalvageTarget := by
  intro V W _ _ G H inputs
  exact inputs.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the preimage-facing route interface.
-/
def Section92Step4PreimageRegimeDischargedS4SalvageTarget : Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W},
      MinimalCounterexamplePreimagePeeledCollarRouteInputs G H →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H

/-- Verbatim end-to-end preimage-regime S4 salvage statement. -/
theorem section92Step4PreimageRegimeDischargedS4SalvageTarget :
    Section92Step4PreimageRegimeDischargedS4SalvageTarget := by
  intro V W _ _ G H inputs
  exact inputs.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the endpoint-range route interface.
-/
def Section92Step4EndpointRangeRegimeDischargedS4SalvageTarget : Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W},
      MinimalCounterexampleEndpointRangePeeledCollarRouteInputs G H →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H

/-- Verbatim end-to-end endpoint-range S4 salvage statement. -/
theorem section92Step4EndpointRangeRegimeDischargedS4SalvageTarget :
    Section92Step4EndpointRangeRegimeDischargedS4SalvageTarget := by
  intro V W _ _ G H inputs
  exact inputs.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the boundary-support route interface.
-/
def Section92Step4BoundarySupportRegimeDischargedS4SalvageTarget : Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W},
      MinimalCounterexampleBoundarySupportPeeledCollarRouteInputs G H →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H

/-- Verbatim end-to-end boundary-support S4 salvage statement. -/
theorem section92Step4BoundarySupportRegimeDischargedS4SalvageTarget :
    Section92Step4BoundarySupportRegimeDischargedS4SalvageTarget := by
  intro V W _ _ G H inputs
  exact inputs.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the boundary-edge-set induced route
interface.
-/
def Section92Step4BoundaryEdgeSetInducedRegimeDischargedS4SalvageTarget : Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {edges : Finset G.edgeSet},
      MinimalCounterexampleBoundaryEdgeSetInducedPeeledCollarRouteInputs G edges →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          (BoundaryEdgeSetInducedGraph (G := G) edges)

/-- Verbatim end-to-end boundary-edge-set induced S4 salvage statement. -/
theorem section92Step4BoundaryEdgeSetInducedRegimeDischargedS4SalvageTarget :
    Section92Step4BoundaryEdgeSetInducedRegimeDischargedS4SalvageTarget := by
  intro V _ G edges inputs
  exact inputs.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the boundary-carrier endpoint-support route
interface.
-/
def Section92Step4BoundaryCarrierEndpointSupportRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {edges : Finset G.edgeSet},
      MinimalCounterexampleBoundaryCarrierEndpointSupportPeeledCollarRouteInputs
        G edges →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          (BoundaryEdgeSetInducedGraph (G := G) edges)

/-- Verbatim end-to-end boundary-carrier endpoint-support S4 salvage statement. -/
theorem section92Step4BoundaryCarrierEndpointSupportRegimeDischargedS4SalvageTarget :
    Section92Step4BoundaryCarrierEndpointSupportRegimeDischargedS4SalvageTarget := by
  intro V _ G edges inputs
  exact inputs.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the off-carrier walk-consistency route
interface.
-/
def Section92Step4OffCarrierWalkConsistentRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {edges : Finset G.edgeSet},
      MinimalCounterexampleOffCarrierWalkConsistentPeeledCollarRouteInputs
        G edges →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          (BoundaryEdgeSetInducedGraph (G := G) edges)

/-- Verbatim end-to-end off-carrier walk-consistency S4 salvage statement. -/
theorem section92Step4OffCarrierWalkConsistentRegimeDischargedS4SalvageTarget :
    Section92Step4OffCarrierWalkConsistentRegimeDischargedS4SalvageTarget := by
  intro V _ G edges inputs
  exact inputs.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the off-carrier component-attachment route
interface.
-/
def Section92Step4OffCarrierComponentAttachmentRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {edges : Finset G.edgeSet},
      MinimalCounterexampleOffCarrierComponentAttachmentPeeledCollarRouteInputs
        G edges →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          (BoundaryEdgeSetInducedGraph (G := G) edges)

/-- Verbatim end-to-end off-carrier component-attachment S4 salvage statement. -/
theorem section92Step4OffCarrierComponentAttachmentRegimeDischargedS4SalvageTarget :
    Section92Step4OffCarrierComponentAttachmentRegimeDischargedS4SalvageTarget := by
  intro V _ G edges inputs
  exact inputs.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the off-carrier
attachment-carrier-connectivity route interface.
-/
def
    Section92Step4OffCarrierAttachmentCarrierConnectedRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {edges : Finset G.edgeSet},
      MinimalCounterexampleOffCarrierAttachmentCarrierConnectedPeeledCollarRouteInputs
        G edges →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          (BoundaryEdgeSetInducedGraph (G := G) edges)

/-- Verbatim end-to-end off-carrier attachment-carrier-connectivity S4 salvage statement. -/
theorem
    section92Step4OffCarrierAttachmentCarrierConnectedRegimeDischargedS4SalvageTarget :
    Section92Step4OffCarrierAttachmentCarrierConnectedRegimeDischargedS4SalvageTarget := by
  intro V _ G edges inputs
  exact inputs.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the off-carrier cut-avoiding
shared-endpoint boundary-route interface.
-/
def
    Section92Step4OffCarrierCutAvoidingSharedEndpointRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {edges : Finset G.edgeSet},
      MinimalCounterexampleOffCarrierCutAvoidingSharedEndpointPeeledCollarRouteInputs
        G edges →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          (BoundaryEdgeSetInducedGraph (G := G) edges)

/-- Verbatim end-to-end cut-avoiding shared-endpoint S4 salvage statement. -/
theorem
    section92Step4OffCarrierCutAvoidingSharedEndpointRegimeDischargedS4SalvageTarget :
    Section92Step4OffCarrierCutAvoidingSharedEndpointRegimeDischargedS4SalvageTarget := by
  intro V _ G edges inputs
  exact inputs.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the off-carrier mapped-cut-deleted
shared-endpoint connectivity interface.
-/
def
    Section92Step4OffCarrierMappedCutAvoidingSharedEndpointConnectedRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {edges : Finset G.edgeSet},
      MinimalCounterexampleOffCarrierMappedCutAvoidingSharedEndpointConnectedPeeledCollarRouteInputs
        G edges →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          (BoundaryEdgeSetInducedGraph (G := G) edges)

/-- Verbatim end-to-end mapped-cut-deleted shared-endpoint S4 salvage statement. -/
theorem
    section92Step4OffCarrierMappedCutAvoidingSharedEndpointConnectedRegimeDischargedS4SalvageTarget :
    Section92Step4OffCarrierMappedCutAvoidingSharedEndpointConnectedRegimeDischargedS4SalvageTarget := by
  intro V _ G edges inputs
  exact inputs.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the off-boundary route interface.
-/
def Section92Step4OffBoundaryRegimeDischargedS4SalvageTarget : Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W},
      MinimalCounterexampleOffBoundaryPeeledCollarRouteInputs G H →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H

/-- Verbatim end-to-end off-boundary S4 salvage statement. -/
theorem section92Step4OffBoundaryRegimeDischargedS4SalvageTarget :
    Section92Step4OffBoundaryRegimeDischargedS4SalvageTarget := by
  intro V W _ _ G H inputs
  exact inputs.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the local-constancy route interface.
-/
def Section92Step4LocalConstancyRegimeDischargedS4SalvageTarget : Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W},
      MinimalCounterexampleLocalConstancyPeeledCollarRouteInputs G H →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H

/-- Verbatim end-to-end local-constancy S4 salvage statement. -/
theorem section92Step4LocalConstancyRegimeDischargedS4SalvageTarget :
    Section92Step4LocalConstancyRegimeDischargedS4SalvageTarget := by
  intro V W _ _ G H inputs
  exact inputs.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the annulus-extraction route interface.
-/
def Section92Step4AnnulusExtractionRegimeDischargedS4SalvageTarget : Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W},
      MinimalCounterexampleAnnulusExtractionPeeledCollarRouteInputs G H →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization H

/-- Verbatim end-to-end annulus-extraction S4 salvage statement. -/
theorem section92Step4AnnulusExtractionRegimeDischargedS4SalvageTarget :
    Section92Step4AnnulusExtractionRegimeDischargedS4SalvageTarget := by
  intro V W _ _ G H inputs
  exact inputs.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the canonical annulus route interface.
-/
def Section92Step4CanonicalAnnulusRegimeDischargedS4SalvageTarget : Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb},
      MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs data →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim end-to-end canonical-annulus S4 salvage statement. -/
theorem section92Step4CanonicalAnnulusRegimeDischargedS4SalvageTarget :
    Section92Step4CanonicalAnnulusRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data inputs
  exact inputs.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the canonical annulus route with the
annulus obligation stated as no-avoiding-walk side separation.
-/
def Section92Step4CanonicalAnnulusSeparationRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      PlanarBoundaryAnnulusPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim end-to-end canonical-annulus separation S4 salvage statement. -/
theorem section92Step4CanonicalAnnulusSeparationRegimeDischargedS4SalvageTarget :
    Section92Step4CanonicalAnnulusSeparationRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime hseparate
  exact
    (MinimalCounterexampleCanonicalAnnulusSeparationPeeledCollarRouteInputs.mk
      regime hseparate)
        |>.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the canonical annulus route with the
annulus obligation stated as off-carrier walk consistency.
-/
def Section92Step4CanonicalAnnulusOffCarrierRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      data.PeeledCollarOffCarrierWalkConsistencyTarget →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim end-to-end canonical-annulus off-carrier S4 salvage statement. -/
theorem section92Step4CanonicalAnnulusOffCarrierRegimeDischargedS4SalvageTarget :
    Section92Step4CanonicalAnnulusOffCarrierRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime h
  exact
    MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_offCarrierWalkConsistencyTarget
      regime h

/--
End-to-end S4 salvage target using the canonical annulus route with the
annulus obligation stated as no off-carrier reachability between opposite
carrier sides.
-/
def
    Section92Step4CanonicalAnnulusOffCarrierOppositeSideRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      PlanarBoundaryAnnulusPeeledCollarOffCarrierOppositeSideTarget data →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim end-to-end canonical-annulus off-carrier-disconnection S4 salvage statement. -/
theorem
    section92Step4CanonicalAnnulusOffCarrierOppositeSideRegimeDischargedS4SalvageTarget :
    Section92Step4CanonicalAnnulusOffCarrierOppositeSideRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime h
  exact
    MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_oppositeSideTarget
      regime h

/--
End-to-end S4 salvage target using the canonical annulus route with the
annulus obligation stated as one-sided off-carrier component attachments.
-/
def
    Section92Step4CanonicalAnnulusOffCarrierComponentAttachmentRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      PlanarBoundaryAnnulusPeeledCollarOffCarrierComponentAttachmentTarget
        data →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim end-to-end canonical-annulus component-attachment S4 salvage statement. -/
theorem
    section92Step4CanonicalAnnulusOffCarrierComponentAttachmentRegimeDischargedS4SalvageTarget :
    Section92Step4CanonicalAnnulusOffCarrierComponentAttachmentRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime h
  exact
    MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_componentAttachmentTarget
      regime h

/--
End-to-end S4 salvage target using the canonical annulus route with the
annulus obligation stated as attachment-carrier connectivity.
-/
def
    Section92Step4CanonicalAnnulusOffCarrierAttachmentCarrierConnectedRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentCarrierConnectivityTarget
        data →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim end-to-end canonical-annulus attachment-carrier-connectivity S4 salvage statement. -/
theorem
    section92Step4CanonicalAnnulusOffCarrierAttachmentCarrierConnectedRegimeDischargedS4SalvageTarget :
    Section92Step4CanonicalAnnulusOffCarrierAttachmentCarrierConnectedRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime h
  exact
    MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_attachmentCarrierConnectivityTarget
      regime h

/--
End-to-end S4 salvage target using the canonical annulus route with the
annulus obligation stated as cut-avoiding shared-endpoint boundary reachability.
-/
def
    Section92Step4CanonicalAnnulusOffCarrierCutAvoidingSharedEndpointRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      PlanarBoundaryAnnulusPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget
        data →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim end-to-end canonical-annulus cut-avoiding shared-endpoint S4 salvage statement. -/
theorem
    section92Step4CanonicalAnnulusOffCarrierCutAvoidingSharedEndpointRegimeDischargedS4SalvageTarget :
    Section92Step4CanonicalAnnulusOffCarrierCutAvoidingSharedEndpointRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime h
  exact
    MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_cutAvoidingSharedEndpointReachabilityTarget
      regime h

/--
End-to-end S4 salvage target using the canonical annulus route with the
annulus obligation stated as mapped-cut-deleted shared-endpoint connectivity.
-/
def
    Section92Step4CanonicalAnnulusOffCarrierMappedCutAvoidingSharedEndpointConnectivityRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim end-to-end canonical-annulus mapped-cut-deleted shared-endpoint S4 salvage statement. -/
theorem
    section92Step4CanonicalAnnulusOffCarrierMappedCutAvoidingSharedEndpointConnectivityRegimeDischargedS4SalvageTarget :
    Section92Step4CanonicalAnnulusOffCarrierMappedCutAvoidingSharedEndpointConnectivityRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime h
  exact
    MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_mappedCutAvoidingSharedEndpointConnectivityTarget
      regime h

/--
End-to-end S4 salvage target using the repaired annulus route interface.
-/
def Section92Step4RepairedAnnulusRegimeDischargedS4SalvageTarget : Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb},
      MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs data →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim end-to-end repaired-annulus S4 salvage statement. -/
theorem section92Step4RepairedAnnulusRegimeDischargedS4SalvageTarget :
    Section92Step4RepairedAnnulusRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data inputs
  exact inputs.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the repaired annulus route with the
annulus obligation stated as no-avoiding-walk side separation.
-/
def Section92Step4RepairedAnnulusSeparationRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      PlanarBoundaryPreviousBoundaryPeeledCollarSeparationTarget
        data data.inducedBoundaryEmbedding →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim end-to-end repaired-annulus separation S4 salvage statement. -/
theorem section92Step4RepairedAnnulusSeparationRegimeDischargedS4SalvageTarget :
    Section92Step4RepairedAnnulusSeparationRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime hseparate
  exact
    (MinimalCounterexampleRepairedAnnulusSeparationPeeledCollarRouteInputs.mk
      regime hseparate)
        |>.closedCollarWindingFreedomEscape_not_simplyRealizable

/--
End-to-end S4 salvage target using the repaired annulus route with the
annulus obligation stated as off-carrier walk consistency.
-/
def Section92Step4RepairedAnnulusOffCarrierRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      data.PeeledCollarOffCarrierWalkConsistencyTarget →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim end-to-end repaired-annulus off-carrier S4 salvage statement. -/
theorem section92Step4RepairedAnnulusOffCarrierRegimeDischargedS4SalvageTarget :
    Section92Step4RepairedAnnulusOffCarrierRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime h
  exact
    MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_offCarrierWalkConsistencyTarget
      regime h

/--
End-to-end S4 salvage target using the repaired annulus route with the
annulus obligation stated as no off-carrier reachability between opposite
carrier sides.
-/
def
    Section92Step4RepairedAnnulusOffCarrierOppositeSideRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierOppositeSideTarget
        data →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim end-to-end repaired-annulus off-carrier-disconnection S4 salvage statement. -/
theorem
    section92Step4RepairedAnnulusOffCarrierOppositeSideRegimeDischargedS4SalvageTarget :
    Section92Step4RepairedAnnulusOffCarrierOppositeSideRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime h
  exact
    MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_oppositeSideTarget
      regime h

/--
End-to-end S4 salvage target using the repaired annulus route with the
annulus obligation stated as one-sided off-carrier component attachments.
-/
def
    Section92Step4RepairedAnnulusOffCarrierComponentAttachmentRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierComponentAttachmentTarget
        data →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim end-to-end repaired-annulus component-attachment S4 salvage statement. -/
theorem
    section92Step4RepairedAnnulusOffCarrierComponentAttachmentRegimeDischargedS4SalvageTarget :
    Section92Step4RepairedAnnulusOffCarrierComponentAttachmentRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime h
  exact
    MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_componentAttachmentTarget
      regime h

/--
End-to-end S4 salvage target using the repaired annulus route with the
annulus obligation stated as attachment-carrier connectivity.
-/
def
    Section92Step4RepairedAnnulusOffCarrierAttachmentCarrierConnectedRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentCarrierConnectivityTarget
        data →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim end-to-end repaired-annulus attachment-carrier-connectivity S4 salvage statement. -/
theorem
    section92Step4RepairedAnnulusOffCarrierAttachmentCarrierConnectedRegimeDischargedS4SalvageTarget :
    Section92Step4RepairedAnnulusOffCarrierAttachmentCarrierConnectedRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime h
  exact
    MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_attachmentCarrierConnectivityTarget
      regime h

/--
End-to-end S4 salvage target using the repaired annulus route with the
annulus obligation stated as cut-avoiding shared-endpoint boundary reachability.
-/
def
    Section92Step4RepairedAnnulusOffCarrierCutAvoidingSharedEndpointRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget
        data →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim end-to-end repaired-annulus cut-avoiding shared-endpoint S4 salvage statement. -/
theorem
    section92Step4RepairedAnnulusOffCarrierCutAvoidingSharedEndpointRegimeDischargedS4SalvageTarget :
    Section92Step4RepairedAnnulusOffCarrierCutAvoidingSharedEndpointRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime h
  exact
    MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_cutAvoidingSharedEndpointReachabilityTarget
      regime h

/--
End-to-end S4 salvage target using the repaired annulus route with the
annulus obligation stated as mapped-cut-deleted shared-endpoint connectivity.
-/
def
    Section92Step4RepairedAnnulusOffCarrierMappedCutAvoidingSharedEndpointConnectivityRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim end-to-end repaired-annulus mapped-cut-deleted shared-endpoint S4 salvage statement. -/
theorem
    section92Step4RepairedAnnulusOffCarrierMappedCutAvoidingSharedEndpointConnectivityRegimeDischargedS4SalvageTarget :
    Section92Step4RepairedAnnulusOffCarrierMappedCutAvoidingSharedEndpointConnectivityRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime h
  exact
    MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_mappedCutAvoidingSharedEndpointConnectivityTarget
      regime h

end Mettapedia.GraphTheory.FourColor
