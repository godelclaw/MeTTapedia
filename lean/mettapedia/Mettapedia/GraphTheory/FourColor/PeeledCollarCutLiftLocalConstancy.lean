import Mettapedia.GraphTheory.FourColor.PeeledCollarCutLiftOffBoundary

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V W : Type*} [DecidableEq V]

/--
Edge-local side constancy away from a finite vertex support.  This is the
finite graph-facing statement expected from the planar peel: if an ambient edge
has an endpoint outside the boundary support, then the filled side is constant
on that edge.
-/
def EdgeSideLocallyConstantOffSupport
    {G : SimpleGraph V} (side : V → Prop) (support : Finset V) : Prop :=
  ∀ e : G.edgeSet,
    (∃ v : V, v ∈ (e : Sym2 V) ∧ v ∉ support) →
      ∀ u v : V, u ∈ (e : Sym2 V) → v ∈ (e : Sym2 V) →
        (side u ↔ side v)

omit [DecidableEq V] in
/-- Edge-local side constancy away from the support rules out side crossing at
every edge incident to an off-support endpoint. -/
theorem not_edgeCrossesVertexSide_of_edgeSideLocallyConstantOffSupport
    {G : SimpleGraph V} {side : V → Prop} {support : Finset V}
    (hlocal : EdgeSideLocallyConstantOffSupport (G := G) side support)
    {e : G.edgeSet}
    (hoffSupport : ∃ v : V, v ∈ (e : Sym2 V) ∧ v ∉ support) :
    ¬ EdgeCrossesVertexSide G side e := by
  rw [not_edgeCrossesVertexSide_iff_forall_side_iff]
  exact hlocal e hoffSupport

/--
Local-constancy datum for lifting one peeled-collar cut.  The ambient side
agrees with the collar side on embedded vertices, and the side is constant on
every ambient edge incident to a vertex outside the endpoint support of the
mapped collar cut.

This is the next planar-normal-form target below the off-boundary interface:
the annulus/Jordan layer should prove this local constancy from the actual
filled-side geometry.
-/
structure PeeledCollarCutAmbientSideLocalConstancy
    {H : SimpleGraph W} {G : SimpleGraph V}
    (φ : H ↪g G) (cut : SmallCyclicEdgeCut H) where
  side : V → Prop
  side_comp_embedding : ∀ w, side (φ w) ↔ cut.side w
  offBoundaryEndpoint_side_iff :
    EdgeSideLocallyConstantOffSupport
      (G := G) side
      (boundaryEdgeSetEndpointSupport (cut.edgeCut.map φ.mapEdgeSet))

namespace PeeledCollarCutAmbientSideOffBoundaryNoCrossing

/-- Off-boundary no-crossing data are exactly local side constancy across
ambient edges incident to off-support endpoints. -/
def toLocalConstancy
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (offBoundary : PeeledCollarCutAmbientSideOffBoundaryNoCrossing φ cut) :
    PeeledCollarCutAmbientSideLocalConstancy φ cut where
  side := offBoundary.side
  side_comp_embedding := offBoundary.side_comp_embedding
  offBoundaryEndpoint_side_iff := by
    intro e hoffSupport u v hu hv
    exact
      (not_edgeCrossesVertexSide_iff_forall_side_iff G offBoundary.side e).1
        (offBoundary.nonBoundaryEndpoint_not_crossing e hoffSupport)
        u v hu hv

end PeeledCollarCutAmbientSideOffBoundaryNoCrossing

namespace PeeledCollarCutAmbientSideLocalConstancy

/-- Local side constancy gives the off-boundary no-crossing datum. -/
def toOffBoundaryNoCrossing
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (localData : PeeledCollarCutAmbientSideLocalConstancy φ cut) :
    PeeledCollarCutAmbientSideOffBoundaryNoCrossing φ cut where
  side := localData.side
  side_comp_embedding := localData.side_comp_embedding
  nonBoundaryEndpoint_not_crossing := by
    intro e hoffSupport
    exact not_edgeCrossesVertexSide_of_edgeSideLocallyConstantOffSupport
      localData.offBoundaryEndpoint_side_iff hoffSupport

/-- Local side constancy gives mapped-cut endpoint-support data. -/
def toAmbientSideBoundarySupport
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (localData : PeeledCollarCutAmbientSideLocalConstancy φ cut) :
    PeeledCollarCutAmbientSideBoundarySupport φ cut :=
  localData.toOffBoundaryNoCrossing.toAmbientSideBoundarySupport

/-- Local side constancy gives endpoint-range data. -/
def toAmbientSideEndpointRange
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (localData : PeeledCollarCutAmbientSideLocalConstancy φ cut) :
    PeeledCollarCutAmbientSideEndpointRange φ cut :=
  localData.toOffBoundaryNoCrossing.toAmbientSideEndpointRange

/-- Local side constancy gives preimage data. -/
def toAmbientSidePreimage
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (localData : PeeledCollarCutAmbientSideLocalConstancy φ cut) :
    PeeledCollarCutAmbientSidePreimage φ cut :=
  localData.toOffBoundaryNoCrossing.toAmbientSidePreimage

/-- Local side constancy gives edge-barrier data. -/
def toAmbientSideBarrier
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (localData : PeeledCollarCutAmbientSideLocalConstancy φ cut) :
    PeeledCollarCutAmbientSideBarrier φ cut :=
  localData.toOffBoundaryNoCrossing.toAmbientSideBarrier

/-- Local side constancy gives no-avoiding-walk separation data. -/
def toAmbientSideSeparation
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (localData : PeeledCollarCutAmbientSideLocalConstancy φ cut) :
    PeeledCollarCutAmbientSideSeparation φ cut :=
  localData.toOffBoundaryNoCrossing.toAmbientSideSeparation

/-- Local side constancy gives concrete side-extension data. -/
def toCutSideExtension
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (localData : PeeledCollarCutAmbientSideLocalConstancy φ cut) :
    PeeledCollarCutSideExtension φ cut :=
  localData.toOffBoundaryNoCrossing.toCutSideExtension

end PeeledCollarCutAmbientSideLocalConstancy

/--
Local-constancy foundation target: every small cyclic cut in the peeled collar
has an ambient side whose filled-side predicate is locally constant across any
ambient edge touching an off-boundary vertex.
-/
def PeeledCollarCutAmbientSideLocalConstanciesToAmbient
    {H : SimpleGraph W} {G : SimpleGraph V} (φ : H ↪g G) : Prop :=
  ∀ cut : SmallCyclicEdgeCut H,
    Nonempty (PeeledCollarCutAmbientSideLocalConstancy φ cut)

/-- Local side constancy implies off-boundary no-crossing data. -/
theorem peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_localConstancies
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hlocal : PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ) :
    PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient φ := by
  intro cut
  rcases hlocal cut with ⟨localData⟩
  exact ⟨localData.toOffBoundaryNoCrossing⟩

/-- Off-boundary no-crossing data imply local side constancy. -/
theorem peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_ambientSideOffBoundaryNoCrossings
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hoffBoundary : PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient φ) :
    PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ := by
  intro cut
  rcases hoffBoundary cut with ⟨offBoundary⟩
  exact ⟨offBoundary.toLocalConstancy⟩

/-- Local side constancy and off-boundary no-crossing are equivalent foundation
targets for the peeled-collar lift. -/
theorem peeledCollarCutAmbientSideLocalConstanciesToAmbient_iff_offBoundaryNoCrossings
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G} :
    PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ ↔
      PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient φ :=
  ⟨peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_localConstancies,
    peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_ambientSideOffBoundaryNoCrossings⟩

/-- Local side constancy implies boundary-support data. -/
theorem peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_localConstancies
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hlocal : PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ) :
    PeeledCollarCutAmbientSideBoundarySupportsToAmbient φ :=
  peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSideOffBoundaryNoCrossings
    (peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_localConstancies
      hlocal)

/-- Local side constancy implies endpoint-range data. -/
theorem peeledCollarCutAmbientSideEndpointRangesToAmbient_of_localConstancies
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hlocal : PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ) :
    PeeledCollarCutAmbientSideEndpointRangesToAmbient φ :=
  peeledCollarCutAmbientSideEndpointRangesToAmbient_of_ambientSideOffBoundaryNoCrossings
    (peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_localConstancies
      hlocal)

/-- Local side constancy implies preimage data. -/
theorem peeledCollarCutAmbientSidePreimagesToAmbient_of_localConstancies
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hlocal : PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ) :
    PeeledCollarCutAmbientSidePreimagesToAmbient φ :=
  peeledCollarCutAmbientSidePreimagesToAmbient_of_ambientSideOffBoundaryNoCrossings
    (peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_localConstancies
      hlocal)

/-- Local side constancy implies edge barriers. -/
theorem peeledCollarCutAmbientSideBarriersToAmbient_of_localConstancies
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hlocal : PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ) :
    PeeledCollarCutAmbientSideBarriersToAmbient φ :=
  peeledCollarCutAmbientSideBarriersToAmbient_of_ambientSideOffBoundaryNoCrossings
    (peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_localConstancies
      hlocal)

/-- Local side constancy implies no-avoiding-walk side separations. -/
theorem peeledCollarCutAmbientSideSeparationsToAmbient_of_localConstancies
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hlocal : PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ) :
    PeeledCollarCutAmbientSideSeparationsToAmbient φ :=
  peeledCollarCutAmbientSideSeparationsToAmbient_of_ambientSideOffBoundaryNoCrossings
    (peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_localConstancies
      hlocal)

/-- Local side constancy implies concrete side extensions. -/
theorem peeledCollarCutSideExtensionsToAmbient_of_localConstancies
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hlocal : PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ) :
    PeeledCollarCutSideExtensionsToAmbient φ :=
  peeledCollarCutSideExtensionsToAmbient_of_ambientSideOffBoundaryNoCrossings
    (peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_localConstancies
      hlocal)

/-- Local side constancy implies the graph-facing small-cut lift. -/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_localConstancies
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hlocal : PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G H :=
  peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideOffBoundaryNoCrossings
    (peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_localConstancies
      hlocal)

/-- Regime-facing inheritance theorem from local side constancy. -/
theorem peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_localConstancies
    [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H)
    (hlocal : PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ) :
    CyclicallyFiveEdgeConnected H :=
  peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_ambientSideOffBoundaryNoCrossings
    regime
    (peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_localConstancies
      hlocal)

end Mettapedia.GraphTheory.FourColor
