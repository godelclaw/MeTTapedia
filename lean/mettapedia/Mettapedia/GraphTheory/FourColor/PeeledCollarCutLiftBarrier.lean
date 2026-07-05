import Mettapedia.GraphTheory.FourColor.PeeledCollarCutLiftSeparation

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V W : Type*}

/--
Edge-barrier datum for lifting one peeled-collar cut.  The ambient side agrees
with the collar side on embedded vertices, and every ambient side-crossing edge
is one of the mapped collar-cut edges.

This is the edge-level target expected from a planar separation argument: once
the collar cut is known to be the whole ambient boundary of the filled side,
the no-avoiding-walk separation theorem follows by pure graph theory.
-/
structure PeeledCollarCutAmbientSideBarrier
    {H : SimpleGraph W} {G : SimpleGraph V}
    (φ : H ↪g G) (cut : SmallCyclicEdgeCut H) where
  side : V → Prop
  side_comp_embedding : ∀ w, side (φ w) ↔ cut.side w
  crossingEdge_mem_mappedCut :
    ∀ e : G.edgeSet,
      EdgeCrossesVertexSide G side e → e ∈ cut.edgeCut.map φ.mapEdgeSet

namespace PeeledCollarCutAmbientSideBarrier

/-- An edge-barrier datum gives the no-avoiding-walk separation datum. -/
def toAmbientSideSeparation
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (barrier : PeeledCollarCutAmbientSideBarrier φ cut) :
    PeeledCollarCutAmbientSideSeparation φ cut where
  side := barrier.side
  side_comp_embedding := barrier.side_comp_embedding
  noWalkAvoiding_mappedCut := by
    rintro ⟨u, v, p, hu, hv, havoid⟩
    rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides
        barrier.side p hu hv with
      ⟨e, heEdges, hcross⟩
    exact havoid e (barrier.crossingEdge_mem_mappedCut e hcross) heEdges

/-- An edge-barrier datum gives the concrete side-extension datum. -/
def toCutSideExtension
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (barrier : PeeledCollarCutAmbientSideBarrier φ cut) :
    PeeledCollarCutSideExtension φ cut :=
  barrier.toAmbientSideSeparation.toCutSideExtension

end PeeledCollarCutAmbientSideBarrier

/--
Edge-barrier foundation target: every small cyclic cut in the peeled collar has
an ambient side whose crossing edges are exactly bounded by the mapped collar
cut support.
-/
def PeeledCollarCutAmbientSideBarriersToAmbient
    {H : SimpleGraph W} {G : SimpleGraph V} (φ : H ↪g G) : Prop :=
  ∀ cut : SmallCyclicEdgeCut H,
    Nonempty (PeeledCollarCutAmbientSideBarrier φ cut)

/-- Edge barriers imply no-avoiding-walk side separations. -/
theorem peeledCollarCutAmbientSideSeparationsToAmbient_of_ambientSideBarriers
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hbarrier : PeeledCollarCutAmbientSideBarriersToAmbient φ) :
    PeeledCollarCutAmbientSideSeparationsToAmbient φ := by
  intro cut
  rcases hbarrier cut with ⟨barrier⟩
  exact ⟨barrier.toAmbientSideSeparation⟩

/-- Edge barriers imply concrete side extensions. -/
theorem peeledCollarCutSideExtensionsToAmbient_of_ambientSideBarriers
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hbarrier : PeeledCollarCutAmbientSideBarriersToAmbient φ) :
    PeeledCollarCutSideExtensionsToAmbient φ :=
  peeledCollarCutSideExtensionsToAmbient_of_ambientSideSeparations
    (peeledCollarCutAmbientSideSeparationsToAmbient_of_ambientSideBarriers
      hbarrier)

/-- Edge barriers imply the graph-facing small-cut lift. -/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideBarriers
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hbarrier : PeeledCollarCutAmbientSideBarriersToAmbient φ) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G H :=
  peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideSeparations
    (peeledCollarCutAmbientSideSeparationsToAmbient_of_ambientSideBarriers
      hbarrier)

/-- Regime-facing inheritance theorem from edge-barrier data. -/
theorem peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_ambientSideBarriers
    [DecidableEq V] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H)
    (hbarrier : PeeledCollarCutAmbientSideBarriersToAmbient φ) :
    CyclicallyFiveEdgeConnected H :=
  peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_ambientSideSeparations
    regime
    (peeledCollarCutAmbientSideSeparationsToAmbient_of_ambientSideBarriers
      hbarrier)

end Mettapedia.GraphTheory.FourColor
