import Mettapedia.GraphTheory.FourColor.PeeledCollarCutLiftEmbedding

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V W : Type*}

namespace EdgeCrossesVertexSide

/-- A graph embedding transports a side-crossing edge when the target side
agrees with the source side on embedded vertices. -/
theorem map_embedding
    {H : SimpleGraph W} {G : SimpleGraph V} (φ : H ↪g G)
    {sideH : W → Prop} {sideG : V → Prop}
    (hside : ∀ w, sideG (φ w) ↔ sideH w)
    {e : H.edgeSet} :
    EdgeCrossesVertexSide H sideH e →
      EdgeCrossesVertexSide G sideG (φ.mapEdgeSet e) := by
  rintro ⟨u, v, hu, hv, hsu, hsv⟩
  refine ⟨φ u, φ v, ?_, ?_, (hside u).2 hsu, ?_⟩
  · simpa [SimpleGraph.Embedding.mapEdgeSet, SimpleGraph.Hom.mapEdgeSet,
      Sym2.mem_map] using
      (show ∃ a, a ∈ (e : Sym2 W) ∧ φ a = φ u from ⟨u, hu, rfl⟩)
  · simpa [SimpleGraph.Embedding.mapEdgeSet, SimpleGraph.Hom.mapEdgeSet,
      Sym2.mem_map] using
      (show ∃ a, a ∈ (e : Sym2 W) ∧ φ a = φ v from ⟨v, hv, rfl⟩)
  · intro hsg
    exact hsv ((hside v).1 hsg)

end EdgeCrossesVertexSide

namespace SmallCyclicEdgeCut

/-- Every listed collar cut edge maps to an ambient side-crossing edge when the
ambient side agrees with the collar side on embedded vertices. -/
theorem mappedCut_crosses_of_side_comp_embedding
    {H : SimpleGraph W} {G : SimpleGraph V} (φ : H ↪g G)
    {cut : SmallCyclicEdgeCut H} {sideG : V → Prop}
    (hside : ∀ w, sideG (φ w) ↔ cut.side w) :
    ∀ e : G.edgeSet, e ∈ cut.edgeCut.map φ.mapEdgeSet →
      EdgeCrossesVertexSide G sideG e := by
  intro e he
  rcases Finset.mem_map.1 he with ⟨eH, heH, heq⟩
  rw [← heq]
  exact EdgeCrossesVertexSide.map_embedding φ hside ((cut.hcut_eq eH).1 heH)

end SmallCyclicEdgeCut

/--
Separation-facing datum for lifting one peeled-collar cut.  The ambient side
agrees with the collar cut side on embedded vertices, and every ambient walk
from one ambient side to the other must use a mapped collar-cut edge.

This is the graph-theoretic endpoint of the remaining planar foundation
target: a Jordan/duality argument should supply the no-avoiding-walk field for
the actual peel.
-/
structure PeeledCollarCutAmbientSideSeparation
    {H : SimpleGraph W} {G : SimpleGraph V}
    (φ : H ↪g G) (cut : SmallCyclicEdgeCut H) where
  side : V → Prop
  side_comp_embedding : ∀ w, side (φ w) ↔ cut.side w
  noWalkAvoiding_mappedCut :
    ¬ ∃ u v : V, ∃ p : G.Walk u v,
      side u ∧ ¬ side v ∧
        ∀ e : G.edgeSet, e ∈ cut.edgeCut.map φ.mapEdgeSet →
          (e : Sym2 V) ∉ p.edges

namespace PeeledCollarCutAmbientSideSeparation

/-- The no-avoiding-walk separation datum gives the exact side-extension
datum used by the embedding-side cut-lift bridge. -/
def toCutSideExtension
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (separation : PeeledCollarCutAmbientSideSeparation φ cut) :
    PeeledCollarCutSideExtension φ cut where
  side := separation.side
  side_comp_embedding := separation.side_comp_embedding
  crossingSupport_eq_mappedCut := by
    intro e
    constructor
    · exact cut.mappedCut_crosses_of_side_comp_embedding φ
        separation.side_comp_embedding e
    · intro hcross
      by_contra hnot
      have hnoncross :
          ∀ e : G.edgeSet, e ∉ cut.edgeCut.map φ.mapEdgeSet →
            ¬ EdgeCrossesVertexSide G separation.side e :=
        (no_walk_avoiding_edgeCut_iff_noncrossing_outside_edgeCut
          (G := G) (edgeCut := cut.edgeCut.map φ.mapEdgeSet)
          separation.side).1
          separation.noWalkAvoiding_mappedCut
      exact hnoncross e hnot hcross

end PeeledCollarCutAmbientSideSeparation

/--
Separation-facing foundation target: every small cyclic cut in the peeled
collar has an ambient side satisfying the no-avoiding-walk separation property.
-/
def PeeledCollarCutAmbientSideSeparationsToAmbient
    {H : SimpleGraph W} {G : SimpleGraph V} (φ : H ↪g G) : Prop :=
  ∀ cut : SmallCyclicEdgeCut H,
    Nonempty (PeeledCollarCutAmbientSideSeparation φ cut)

/-- No-avoiding-walk side separations imply concrete side extensions. -/
theorem peeledCollarCutSideExtensionsToAmbient_of_ambientSideSeparations
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hseparate : PeeledCollarCutAmbientSideSeparationsToAmbient φ) :
    PeeledCollarCutSideExtensionsToAmbient φ := by
  intro cut
  rcases hseparate cut with ⟨separation⟩
  exact ⟨separation.toCutSideExtension⟩

/-- No-avoiding-walk side separations imply the graph-facing small-cut lift. -/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideSeparations
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hseparate : PeeledCollarCutAmbientSideSeparationsToAmbient φ) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G H :=
  peeledCollarSmallCyclicCutLiftsToAmbient_of_cutSideExtensions
    (peeledCollarCutSideExtensionsToAmbient_of_ambientSideSeparations
      hseparate)

/-- Regime-facing inheritance theorem from no-avoiding-walk side separations. -/
theorem peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_ambientSideSeparations
    [DecidableEq V] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H)
    (hseparate : PeeledCollarCutAmbientSideSeparationsToAmbient φ) :
    CyclicallyFiveEdgeConnected H :=
  peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_cutSideExtensions
    regime
    (peeledCollarCutSideExtensionsToAmbient_of_ambientSideSeparations
      hseparate)

end Mettapedia.GraphTheory.FourColor
