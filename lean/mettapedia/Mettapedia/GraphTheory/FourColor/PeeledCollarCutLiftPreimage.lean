import Mettapedia.GraphTheory.FourColor.PeeledCollarCutLiftBarrier

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V W : Type*}

namespace EdgeCrossesVertexSide

/--
A graph embedding reflects side-crossing for an edge already known to be a
mapped source edge, provided the target and source sides agree on embedded
vertices.
-/
theorem comap_embedding
    {H : SimpleGraph W} {G : SimpleGraph V} (φ : H ↪g G)
    {sideH : W → Prop} {sideG : V → Prop}
    (hside : ∀ w, sideG (φ w) ↔ sideH w)
    {e : H.edgeSet} :
    EdgeCrossesVertexSide G sideG (φ.mapEdgeSet e) →
      EdgeCrossesVertexSide H sideH e := by
  rintro ⟨u, v, hu, hv, hsu, hsv⟩
  have hu' :
      ∃ a, a ∈ (e : Sym2 W) ∧ φ a = u := by
    simpa [SimpleGraph.Embedding.mapEdgeSet, SimpleGraph.Hom.mapEdgeSet,
      Sym2.mem_map] using hu
  have hv' :
      ∃ b, b ∈ (e : Sym2 W) ∧ φ b = v := by
    simpa [SimpleGraph.Embedding.mapEdgeSet, SimpleGraph.Hom.mapEdgeSet,
      Sym2.mem_map] using hv
  rcases hu' with ⟨uH, huH, hφu⟩
  rcases hv' with ⟨vH, hvH, hφv⟩
  refine ⟨uH, vH, huH, hvH, ?_, ?_⟩
  · exact (hside uH).1 (by simpa [hφu] using hsu)
  · intro hvH
    exact hsv (by simpa [hφv] using (hside vH).2 hvH)

end EdgeCrossesVertexSide

/--
Preimage datum for lifting one peeled-collar cut.  The ambient side agrees with
the collar side on embedded vertices, and every ambient side-crossing edge is
known to be the image of some collar edge.

Together with side agreement, the reflected side-crossing theorem proves that
the preimage edge is one of the collar cut edges.  Thus this is a sharper
planar-normal-form target than the edge-barrier interface.
-/
structure PeeledCollarCutAmbientSidePreimage
    {H : SimpleGraph W} {G : SimpleGraph V}
    (φ : H ↪g G) (cut : SmallCyclicEdgeCut H) where
  side : V → Prop
  side_comp_embedding : ∀ w, side (φ w) ↔ cut.side w
  crossingEdge_preimage :
    ∀ e : G.edgeSet,
      EdgeCrossesVertexSide G side e →
        ∃ eH : H.edgeSet, φ.mapEdgeSet eH = e

namespace PeeledCollarCutAmbientSidePreimage

/-- A preimage datum gives the edge-barrier datum. -/
def toAmbientSideBarrier
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (preimage : PeeledCollarCutAmbientSidePreimage φ cut) :
    PeeledCollarCutAmbientSideBarrier φ cut where
  side := preimage.side
  side_comp_embedding := preimage.side_comp_embedding
  crossingEdge_mem_mappedCut := by
    intro e hcross
    rcases preimage.crossingEdge_preimage e hcross with ⟨eH, heq⟩
    have hcrossMapped :
        EdgeCrossesVertexSide G preimage.side (φ.mapEdgeSet eH) := by
      simpa [heq] using hcross
    have hcrossSource :
        EdgeCrossesVertexSide H cut.side eH :=
      EdgeCrossesVertexSide.comap_embedding φ
        preimage.side_comp_embedding hcrossMapped
    rw [← heq]
    exact Finset.mem_map.2 ⟨eH, (cut.hcut_eq eH).2 hcrossSource, rfl⟩

/-- A preimage datum gives the no-avoiding-walk separation datum. -/
def toAmbientSideSeparation
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (preimage : PeeledCollarCutAmbientSidePreimage φ cut) :
    PeeledCollarCutAmbientSideSeparation φ cut :=
  preimage.toAmbientSideBarrier.toAmbientSideSeparation

/-- A preimage datum gives the concrete side-extension datum. -/
def toCutSideExtension
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (preimage : PeeledCollarCutAmbientSidePreimage φ cut) :
    PeeledCollarCutSideExtension φ cut :=
  preimage.toAmbientSideBarrier.toCutSideExtension

end PeeledCollarCutAmbientSidePreimage

/--
Preimage-facing foundation target: every small cyclic cut in the peeled collar
has an ambient side such that every ambient side-crossing edge has a collar-edge
preimage.
-/
def PeeledCollarCutAmbientSidePreimagesToAmbient
    {H : SimpleGraph W} {G : SimpleGraph V} (φ : H ↪g G) : Prop :=
  ∀ cut : SmallCyclicEdgeCut H,
    Nonempty (PeeledCollarCutAmbientSidePreimage φ cut)

/-- Preimage data imply edge barriers. -/
theorem peeledCollarCutAmbientSideBarriersToAmbient_of_ambientSidePreimages
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hpreimage : PeeledCollarCutAmbientSidePreimagesToAmbient φ) :
    PeeledCollarCutAmbientSideBarriersToAmbient φ := by
  intro cut
  rcases hpreimage cut with ⟨preimage⟩
  exact ⟨preimage.toAmbientSideBarrier⟩

/-- Preimage data imply no-avoiding-walk side separations. -/
theorem peeledCollarCutAmbientSideSeparationsToAmbient_of_ambientSidePreimages
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hpreimage : PeeledCollarCutAmbientSidePreimagesToAmbient φ) :
    PeeledCollarCutAmbientSideSeparationsToAmbient φ :=
  peeledCollarCutAmbientSideSeparationsToAmbient_of_ambientSideBarriers
    (peeledCollarCutAmbientSideBarriersToAmbient_of_ambientSidePreimages
      hpreimage)

/-- Preimage data imply concrete side extensions. -/
theorem peeledCollarCutSideExtensionsToAmbient_of_ambientSidePreimages
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hpreimage : PeeledCollarCutAmbientSidePreimagesToAmbient φ) :
    PeeledCollarCutSideExtensionsToAmbient φ :=
  peeledCollarCutSideExtensionsToAmbient_of_ambientSideBarriers
    (peeledCollarCutAmbientSideBarriersToAmbient_of_ambientSidePreimages
      hpreimage)

/-- Preimage data imply the graph-facing small-cut lift. -/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSidePreimages
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hpreimage : PeeledCollarCutAmbientSidePreimagesToAmbient φ) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G H :=
  peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideBarriers
    (peeledCollarCutAmbientSideBarriersToAmbient_of_ambientSidePreimages
      hpreimage)

/-- Regime-facing inheritance theorem from preimage data. -/
theorem peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_ambientSidePreimages
    [DecidableEq V] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H)
    (hpreimage : PeeledCollarCutAmbientSidePreimagesToAmbient φ) :
    CyclicallyFiveEdgeConnected H :=
  peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_ambientSideBarriers
    regime
    (peeledCollarCutAmbientSideBarriersToAmbient_of_ambientSidePreimages
      hpreimage)

end Mettapedia.GraphTheory.FourColor
