import Mettapedia.GraphTheory.FourColor.PeeledCollarCutLiftEndpointRange
import Mettapedia.GraphTheory.FourColor.PlanarBoundarySupportGraph

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V W : Type*} [DecidableEq V]

/--
Every vertex in the endpoint support of a mapped collar cut edge has a source
preimage under the collar embedding.
-/
theorem exists_preimage_of_mem_mappedCut_endpointSupport
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H} {v : V}
    (hv :
      v ∈ boundaryEdgeSetEndpointSupport (cut.edgeCut.map φ.mapEdgeSet)) :
    ∃ w : W, φ w = v := by
  rcases (mem_boundaryEdgeSetEndpointSupport_iff
      (cut.edgeCut.map φ.mapEdgeSet)).1 hv with
    ⟨eG, heG, hveG⟩
  rcases Finset.mem_map.1 heG with ⟨eH, _heH, heq⟩
  rw [← heq] at hveG
  have hpreimage :
      ∃ w : W, w ∈ (eH : Sym2 W) ∧ φ w = v := by
    simpa [SimpleGraph.Embedding.mapEdgeSet, SimpleGraph.Hom.mapEdgeSet,
      Sym2.mem_map] using hveG
  rcases hpreimage with ⟨w, _hwmem, hw⟩
  exact ⟨w, hw⟩

/--
Mapped-cut endpoint-support datum for lifting one peeled-collar cut.  The
ambient side agrees with the collar side on embedded vertices, and every
endpoint of every ambient side-crossing edge lies in the endpoint support of
the mapped collar cut.

This is the boundary-support target expected from a planar annulus theorem:
the side boundary has no endpoint outside the mapped collar cut boundary.
-/
structure PeeledCollarCutAmbientSideBoundarySupport
    {H : SimpleGraph W} {G : SimpleGraph V}
    (φ : H ↪g G) (cut : SmallCyclicEdgeCut H) where
  side : V → Prop
  side_comp_embedding : ∀ w, side (φ w) ↔ cut.side w
  crossingEdge_endpointSupport :
    ∀ e : G.edgeSet,
      EdgeCrossesVertexSide G side e →
        ∀ v : V,
          v ∈ (e : Sym2 V) →
            v ∈ boundaryEdgeSetEndpointSupport (cut.edgeCut.map φ.mapEdgeSet)

namespace PeeledCollarCutAmbientSideBoundarySupport

/-- Mapped-cut endpoint-support data give endpoint-range data. -/
def toAmbientSideEndpointRange
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (support : PeeledCollarCutAmbientSideBoundarySupport φ cut) :
    PeeledCollarCutAmbientSideEndpointRange φ cut where
  side := support.side
  side_comp_embedding := support.side_comp_embedding
  crossingEdge_endpointRange := by
    intro e hcross v hv
    exact exists_preimage_of_mem_mappedCut_endpointSupport
      (support.crossingEdge_endpointSupport e hcross v hv)

/-- Mapped-cut endpoint-support data give preimage data. -/
def toAmbientSidePreimage
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (support : PeeledCollarCutAmbientSideBoundarySupport φ cut) :
    PeeledCollarCutAmbientSidePreimage φ cut :=
  support.toAmbientSideEndpointRange.toAmbientSidePreimage

/-- Mapped-cut endpoint-support data give edge-barrier data. -/
def toAmbientSideBarrier
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (support : PeeledCollarCutAmbientSideBoundarySupport φ cut) :
    PeeledCollarCutAmbientSideBarrier φ cut :=
  support.toAmbientSideEndpointRange.toAmbientSideBarrier

/-- Mapped-cut endpoint-support data give no-avoiding-walk separation data. -/
def toAmbientSideSeparation
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (support : PeeledCollarCutAmbientSideBoundarySupport φ cut) :
    PeeledCollarCutAmbientSideSeparation φ cut :=
  support.toAmbientSideEndpointRange.toAmbientSideSeparation

/-- Mapped-cut endpoint-support data give concrete side-extension data. -/
def toCutSideExtension
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (support : PeeledCollarCutAmbientSideBoundarySupport φ cut) :
    PeeledCollarCutSideExtension φ cut :=
  support.toAmbientSideEndpointRange.toCutSideExtension

end PeeledCollarCutAmbientSideBoundarySupport

namespace PeeledCollarCutAmbientSideBarrier

/-- Edge-barrier data give mapped-cut endpoint-support data. -/
def toAmbientSideBoundarySupport
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (barrier : PeeledCollarCutAmbientSideBarrier φ cut) :
    PeeledCollarCutAmbientSideBoundarySupport φ cut where
  side := barrier.side
  side_comp_embedding := barrier.side_comp_embedding
  crossingEdge_endpointSupport := by
    intro e hcross v hv
    exact
      (mem_boundaryEdgeSetEndpointSupport_iff
        (cut.edgeCut.map φ.mapEdgeSet)).2
        ⟨e, barrier.crossingEdge_mem_mappedCut e hcross, hv⟩

end PeeledCollarCutAmbientSideBarrier

/--
Boundary-support foundation target: every small cyclic cut in the peeled collar
has an ambient side such that every endpoint of every ambient side-crossing edge
lies in the endpoint support of the mapped collar cut.
-/
def PeeledCollarCutAmbientSideBoundarySupportsToAmbient
    {H : SimpleGraph W} {G : SimpleGraph V} (φ : H ↪g G) : Prop :=
  ∀ cut : SmallCyclicEdgeCut H,
    Nonempty (PeeledCollarCutAmbientSideBoundarySupport φ cut)

/-- Boundary-support data imply endpoint-range data. -/
theorem peeledCollarCutAmbientSideEndpointRangesToAmbient_of_ambientSideBoundarySupports
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hsupport : PeeledCollarCutAmbientSideBoundarySupportsToAmbient φ) :
    PeeledCollarCutAmbientSideEndpointRangesToAmbient φ := by
  intro cut
  rcases hsupport cut with ⟨support⟩
  exact ⟨support.toAmbientSideEndpointRange⟩

/-- Boundary-support data imply preimage data. -/
theorem peeledCollarCutAmbientSidePreimagesToAmbient_of_ambientSideBoundarySupports
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hsupport : PeeledCollarCutAmbientSideBoundarySupportsToAmbient φ) :
    PeeledCollarCutAmbientSidePreimagesToAmbient φ :=
  peeledCollarCutAmbientSidePreimagesToAmbient_of_ambientSideEndpointRanges
    (peeledCollarCutAmbientSideEndpointRangesToAmbient_of_ambientSideBoundarySupports
      hsupport)

/-- Boundary-support data imply edge barriers. -/
theorem peeledCollarCutAmbientSideBarriersToAmbient_of_ambientSideBoundarySupports
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hsupport : PeeledCollarCutAmbientSideBoundarySupportsToAmbient φ) :
    PeeledCollarCutAmbientSideBarriersToAmbient φ :=
  peeledCollarCutAmbientSideBarriersToAmbient_of_ambientSideEndpointRanges
    (peeledCollarCutAmbientSideEndpointRangesToAmbient_of_ambientSideBoundarySupports
      hsupport)

/-- Edge barriers imply boundary-support data. -/
theorem peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSideBarriers
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hbarrier : PeeledCollarCutAmbientSideBarriersToAmbient φ) :
    PeeledCollarCutAmbientSideBoundarySupportsToAmbient φ := by
  intro cut
  rcases hbarrier cut with ⟨barrier⟩
  exact ⟨barrier.toAmbientSideBoundarySupport⟩

/--
Boundary-support and edge-barrier data are equivalent foundation targets for
the peeled-collar lift.
-/
theorem peeledCollarCutAmbientSideBoundarySupportsToAmbient_iff_ambientSideBarriers
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G} :
    PeeledCollarCutAmbientSideBoundarySupportsToAmbient φ ↔
      PeeledCollarCutAmbientSideBarriersToAmbient φ :=
  ⟨peeledCollarCutAmbientSideBarriersToAmbient_of_ambientSideBoundarySupports,
    peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSideBarriers⟩

/-- Endpoint-range data imply boundary-support data. -/
theorem peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSideEndpointRanges
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hrange : PeeledCollarCutAmbientSideEndpointRangesToAmbient φ) :
    PeeledCollarCutAmbientSideBoundarySupportsToAmbient φ :=
  peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSideBarriers
    (peeledCollarCutAmbientSideBarriersToAmbient_of_ambientSideEndpointRanges
      hrange)

/--
Boundary-support and endpoint-range data are equivalent foundation targets for
the peeled-collar lift.
-/
theorem peeledCollarCutAmbientSideBoundarySupportsToAmbient_iff_ambientSideEndpointRanges
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G} :
    PeeledCollarCutAmbientSideBoundarySupportsToAmbient φ ↔
      PeeledCollarCutAmbientSideEndpointRangesToAmbient φ :=
  ⟨peeledCollarCutAmbientSideEndpointRangesToAmbient_of_ambientSideBoundarySupports,
    peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSideEndpointRanges⟩

/-- Preimage data imply boundary-support data. -/
theorem peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSidePreimages
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hpreimage : PeeledCollarCutAmbientSidePreimagesToAmbient φ) :
    PeeledCollarCutAmbientSideBoundarySupportsToAmbient φ :=
  peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSideBarriers
    (peeledCollarCutAmbientSideBarriersToAmbient_of_ambientSidePreimages
      hpreimage)

/--
Boundary-support and preimage data are equivalent foundation targets for the
peeled-collar lift.
-/
theorem peeledCollarCutAmbientSideBoundarySupportsToAmbient_iff_ambientSidePreimages
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G} :
    PeeledCollarCutAmbientSideBoundarySupportsToAmbient φ ↔
      PeeledCollarCutAmbientSidePreimagesToAmbient φ :=
  ⟨peeledCollarCutAmbientSidePreimagesToAmbient_of_ambientSideBoundarySupports,
    peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_ambientSidePreimages⟩

/-- Boundary-support data imply no-avoiding-walk side separations. -/
theorem peeledCollarCutAmbientSideSeparationsToAmbient_of_ambientSideBoundarySupports
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hsupport : PeeledCollarCutAmbientSideBoundarySupportsToAmbient φ) :
    PeeledCollarCutAmbientSideSeparationsToAmbient φ :=
  peeledCollarCutAmbientSideSeparationsToAmbient_of_ambientSideEndpointRanges
    (peeledCollarCutAmbientSideEndpointRangesToAmbient_of_ambientSideBoundarySupports
      hsupport)

/-- Boundary-support data imply concrete side extensions. -/
theorem peeledCollarCutSideExtensionsToAmbient_of_ambientSideBoundarySupports
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hsupport : PeeledCollarCutAmbientSideBoundarySupportsToAmbient φ) :
    PeeledCollarCutSideExtensionsToAmbient φ :=
  peeledCollarCutSideExtensionsToAmbient_of_ambientSideEndpointRanges
    (peeledCollarCutAmbientSideEndpointRangesToAmbient_of_ambientSideBoundarySupports
      hsupport)

/-- Boundary-support data imply the graph-facing small-cut lift. -/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideBoundarySupports
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hsupport : PeeledCollarCutAmbientSideBoundarySupportsToAmbient φ) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G H :=
  peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideEndpointRanges
    (peeledCollarCutAmbientSideEndpointRangesToAmbient_of_ambientSideBoundarySupports
      hsupport)

/-- Regime-facing inheritance theorem from boundary-support data. -/
theorem peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_ambientSideBoundarySupports
    [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H)
    (hsupport : PeeledCollarCutAmbientSideBoundarySupportsToAmbient φ) :
    CyclicallyFiveEdgeConnected H :=
  peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_ambientSideEndpointRanges
    regime
    (peeledCollarCutAmbientSideEndpointRangesToAmbient_of_ambientSideBoundarySupports
      hsupport)

end Mettapedia.GraphTheory.FourColor
