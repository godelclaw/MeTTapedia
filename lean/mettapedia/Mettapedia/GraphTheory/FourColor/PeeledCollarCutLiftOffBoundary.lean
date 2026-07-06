import Mettapedia.GraphTheory.FourColor.PeeledCollarCutLiftBoundarySupport

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V W : Type*} [DecidableEq V]

/--
Off-boundary no-crossing datum for lifting one peeled-collar cut.  The ambient
side agrees with the collar side on embedded vertices, and no ambient
side-crossing edge is incident to a vertex outside the endpoint support of the
mapped collar cut.

This is the local planar-normal-form target behind the boundary-support
interface: away from the mapped cut boundary, the filled side is locally
constant across incident ambient edges.
-/
structure PeeledCollarCutAmbientSideOffBoundaryNoCrossing
    {H : SimpleGraph W} {G : SimpleGraph V}
    (φ : H ↪g G) (cut : SmallCyclicEdgeCut H) where
  side : V → Prop
  side_comp_embedding : ∀ w, side (φ w) ↔ cut.side w
  nonBoundaryEndpoint_not_crossing :
    ∀ e : G.edgeSet,
      (∃ v : V,
        v ∈ (e : Sym2 V) ∧
          v ∉ boundaryEdgeSetEndpointSupport (cut.edgeCut.map φ.mapEdgeSet)) →
        ¬ EdgeCrossesVertexSide G side e

namespace PeeledCollarCutAmbientSideOffBoundaryNoCrossing

/-- Off-boundary no-crossing data give mapped-cut endpoint-support data. -/
def toAmbientSideBoundarySupport
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (offBoundary : PeeledCollarCutAmbientSideOffBoundaryNoCrossing φ cut) :
    PeeledCollarCutAmbientSideBoundarySupport φ cut where
  side := offBoundary.side
  side_comp_embedding := offBoundary.side_comp_embedding
  crossingEdge_endpointSupport := by
    intro e hcross v hv
    by_contra hvNot
    exact offBoundary.nonBoundaryEndpoint_not_crossing e
      ⟨v, hv, hvNot⟩ hcross

/-- Off-boundary no-crossing data give endpoint-range data. -/
def toAmbientSideEndpointRange
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (offBoundary : PeeledCollarCutAmbientSideOffBoundaryNoCrossing φ cut) :
    PeeledCollarCutAmbientSideEndpointRange φ cut :=
  offBoundary.toAmbientSideBoundarySupport.toAmbientSideEndpointRange

/-- Off-boundary no-crossing data give preimage data. -/
def toAmbientSidePreimage
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (offBoundary : PeeledCollarCutAmbientSideOffBoundaryNoCrossing φ cut) :
    PeeledCollarCutAmbientSidePreimage φ cut :=
  offBoundary.toAmbientSideBoundarySupport.toAmbientSidePreimage

/-- Off-boundary no-crossing data give edge-barrier data. -/
def toAmbientSideBarrier
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (offBoundary : PeeledCollarCutAmbientSideOffBoundaryNoCrossing φ cut) :
    PeeledCollarCutAmbientSideBarrier φ cut :=
  offBoundary.toAmbientSideBoundarySupport.toAmbientSideBarrier

/-- Off-boundary no-crossing data give no-avoiding-walk separation data. -/
def toAmbientSideSeparation
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (offBoundary : PeeledCollarCutAmbientSideOffBoundaryNoCrossing φ cut) :
    PeeledCollarCutAmbientSideSeparation φ cut :=
  offBoundary.toAmbientSideBoundarySupport.toAmbientSideSeparation

/-- Off-boundary no-crossing data give concrete side-extension data. -/
def toCutSideExtension
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (offBoundary : PeeledCollarCutAmbientSideOffBoundaryNoCrossing φ cut) :
    PeeledCollarCutSideExtension φ cut :=
  offBoundary.toAmbientSideBoundarySupport.toCutSideExtension

end PeeledCollarCutAmbientSideOffBoundaryNoCrossing

namespace PeeledCollarCutAmbientSideBoundarySupport

/-- Boundary-support data give the equivalent off-boundary no-crossing datum. -/
def toOffBoundaryNoCrossing
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (support : PeeledCollarCutAmbientSideBoundarySupport φ cut) :
    PeeledCollarCutAmbientSideOffBoundaryNoCrossing φ cut where
  side := support.side
  side_comp_embedding := support.side_comp_embedding
  nonBoundaryEndpoint_not_crossing := by
    intro e hoffSupport hcross
    rcases hoffSupport with ⟨v, hv, hvNotSupport⟩
    exact hvNotSupport (support.crossingEdge_endpointSupport e hcross v hv)

end PeeledCollarCutAmbientSideBoundarySupport

/--
Off-boundary foundation target: every small cyclic cut in the peeled collar has
an ambient side such that no ambient side-crossing edge is incident to any
vertex outside the endpoint support of the mapped collar cut.
-/
def PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
    {H : SimpleGraph W} {G : SimpleGraph V} (φ : H ↪g G) : Prop :=
  ∀ cut : SmallCyclicEdgeCut H,
    Nonempty (PeeledCollarCutAmbientSideOffBoundaryNoCrossing φ cut)

/-- Boundary-support data imply off-boundary no-crossing data. -/
theorem peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_ambientSideBoundarySupports
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hsupport : PeeledCollarCutAmbientSideBoundarySupportsToAmbient φ) :
    PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient φ := by
  intro cut
  rcases hsupport cut with ⟨support⟩
  exact ⟨support.toOffBoundaryNoCrossing⟩

/-- Off-boundary no-crossing data imply boundary-support data. -/
theorem peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSideOffBoundaryNoCrossings
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hoffBoundary : PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient φ) :
    PeeledCollarCutAmbientSideBoundarySupportsToAmbient φ := by
  intro cut
  rcases hoffBoundary cut with ⟨offBoundary⟩
  exact ⟨offBoundary.toAmbientSideBoundarySupport⟩

/--
Boundary-support and off-boundary no-crossing are equivalent foundation targets
for the peeled-collar lift.
-/
theorem peeledCollarCutAmbientSideBoundarySupportsToAmbient_iff_offBoundaryNoCrossings
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G} :
    PeeledCollarCutAmbientSideBoundarySupportsToAmbient φ ↔
      PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient φ :=
  ⟨peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_ambientSideBoundarySupports,
    peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSideOffBoundaryNoCrossings⟩

/-- Off-boundary no-crossing data imply endpoint-range data. -/
theorem peeledCollarCutAmbientSideEndpointRangesToAmbient_of_ambientSideOffBoundaryNoCrossings
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hoffBoundary : PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient φ) :
    PeeledCollarCutAmbientSideEndpointRangesToAmbient φ :=
  peeledCollarCutAmbientSideEndpointRangesToAmbient_of_ambientSideBoundarySupports
    (peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSideOffBoundaryNoCrossings
      hoffBoundary)

/-- Off-boundary no-crossing data imply preimage data. -/
theorem peeledCollarCutAmbientSidePreimagesToAmbient_of_ambientSideOffBoundaryNoCrossings
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hoffBoundary : PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient φ) :
    PeeledCollarCutAmbientSidePreimagesToAmbient φ :=
  peeledCollarCutAmbientSidePreimagesToAmbient_of_ambientSideBoundarySupports
    (peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSideOffBoundaryNoCrossings
      hoffBoundary)

/-- Off-boundary no-crossing data imply edge barriers. -/
theorem peeledCollarCutAmbientSideBarriersToAmbient_of_ambientSideOffBoundaryNoCrossings
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hoffBoundary : PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient φ) :
    PeeledCollarCutAmbientSideBarriersToAmbient φ :=
  peeledCollarCutAmbientSideBarriersToAmbient_of_ambientSideBoundarySupports
    (peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSideOffBoundaryNoCrossings
      hoffBoundary)

/-- Off-boundary no-crossing data imply no-avoiding-walk side separations. -/
theorem peeledCollarCutAmbientSideSeparationsToAmbient_of_ambientSideOffBoundaryNoCrossings
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hoffBoundary : PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient φ) :
    PeeledCollarCutAmbientSideSeparationsToAmbient φ :=
  peeledCollarCutAmbientSideSeparationsToAmbient_of_ambientSideBoundarySupports
    (peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSideOffBoundaryNoCrossings
      hoffBoundary)

/-- Off-boundary no-crossing data imply concrete side extensions. -/
theorem peeledCollarCutSideExtensionsToAmbient_of_ambientSideOffBoundaryNoCrossings
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hoffBoundary : PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient φ) :
    PeeledCollarCutSideExtensionsToAmbient φ :=
  peeledCollarCutSideExtensionsToAmbient_of_ambientSideBoundarySupports
    (peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSideOffBoundaryNoCrossings
      hoffBoundary)

/-- Off-boundary no-crossing data imply the graph-facing small-cut lift. -/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideOffBoundaryNoCrossings
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hoffBoundary : PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient φ) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G H :=
  peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideBoundarySupports
    (peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSideOffBoundaryNoCrossings
      hoffBoundary)

/-- Regime-facing inheritance theorem from off-boundary no-crossing data. -/
theorem peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_ambientSideOffBoundaryNoCrossings
    [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H)
    (hoffBoundary : PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient φ) :
    CyclicallyFiveEdgeConnected H :=
  peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_ambientSideBoundarySupports
    regime
    (peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSideOffBoundaryNoCrossings
      hoffBoundary)

end Mettapedia.GraphTheory.FourColor
