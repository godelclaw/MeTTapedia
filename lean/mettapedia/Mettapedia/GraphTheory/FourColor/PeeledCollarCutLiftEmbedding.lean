import Mettapedia.GraphTheory.FourColor.PeeledCollarConnectivityBridge

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V W : Type*}

namespace HasCycleOnSide

/-- A graph embedding transports a side-contained cycle when the target side
contains the image of the source side. -/
theorem map_embedding
    {H : SimpleGraph W} {G : SimpleGraph V} (φ : H ↪g G)
    {sideH : W → Prop} {sideG : V → Prop}
    (hside : ∀ w, sideH w → sideG (φ w)) :
    HasCycleOnSide H sideH → HasCycleOnSide G sideG := by
  rintro ⟨w, hw, p, hpCycle, hpSide⟩
  refine ⟨φ w, hside w hw, p.map φ.toHom, hpCycle.map φ.injective, ?_⟩
  intro v hv
  rw [Walk.support_map] at hv
  rcases List.mem_map.1 hv with ⟨w', hw', rfl⟩
  exact hside w' (hpSide w' hw')

end HasCycleOnSide

variable [DecidableEq V] [DecidableEq W]

/--
Concrete side-extension datum for lifting one peeled-collar cut to the ambient
graph along an embedding.  The ambient side agrees with the collar side on the
embedded collar vertices, and its exact crossing support is the image of the
collar cut edge support.
-/
structure PeeledCollarCutSideExtension
    {H : SimpleGraph W} {G : SimpleGraph V}
    (φ : H ↪g G) (cut : SmallCyclicEdgeCut H) where
  side : V → Prop
  side_comp_embedding : ∀ w, side (φ w) ↔ cut.side w
  crossingSupport_eq_mappedCut :
    ∀ e : G.edgeSet,
      e ∈ cut.edgeCut.map φ.mapEdgeSet ↔ EdgeCrossesVertexSide G side e

namespace PeeledCollarCutSideExtension

/-- A concrete side-extension datum gives cyclic-edge-cut realization data for
the mapped collar cut support. -/
def toCyclicEdgeCutRealization
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (extension : PeeledCollarCutSideExtension φ cut) :
    CyclicEdgeCutRealization G (cut.edgeCut.map φ.mapEdgeSet) where
  side := extension.side
  hcut_eq := extension.crossingSupport_eq_mappedCut
  hinside_cycle :=
    cut.hinside_cycle.map_embedding φ
      (fun w hw => (extension.side_comp_embedding w).2 hw)
  houtside_cycle :=
    cut.houtside_cycle.map_embedding φ
      (fun w hw hside => hw ((extension.side_comp_embedding w).1 hside))

/-- A concrete side-extension datum gives a bundled ambient small cyclic cut. -/
def toAmbientSmallCyclicEdgeCut
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (extension : PeeledCollarCutSideExtension φ cut) :
    SmallCyclicEdgeCut G :=
  (extension.toCyclicEdgeCutRealization).toSmallCyclicEdgeCut (by
    rw [Finset.card_map]
    exact cut.hcard_le_four)

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem toAmbientSmallCyclicEdgeCut_edgeCut
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (extension : PeeledCollarCutSideExtension φ cut) :
    extension.toAmbientSmallCyclicEdgeCut.edgeCut =
      cut.edgeCut.map φ.mapEdgeSet :=
  rfl

/- The lifted ambient cut has the same edge-support cardinality as the collar
cut. -/
omit [DecidableEq V] [DecidableEq W] in
theorem toAmbientSmallCyclicEdgeCut_card
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (extension : PeeledCollarCutSideExtension φ cut) :
    extension.toAmbientSmallCyclicEdgeCut.edgeCut.card = cut.edgeCut.card := by
  rw [toAmbientSmallCyclicEdgeCut_edgeCut, Finset.card_map]

end PeeledCollarCutSideExtension

/--
Embedding-side foundation target: every small cyclic cut in the peeled collar
has an ambient side extension along the selected collar embedding.
-/
def PeeledCollarCutSideExtensionsToAmbient
    {H : SimpleGraph W} {G : SimpleGraph V} (φ : H ↪g G) : Prop :=
  ∀ cut : SmallCyclicEdgeCut H,
    Nonempty (PeeledCollarCutSideExtension φ cut)

/- Concrete embedding-side extensions imply the previous graph-facing
small-cut lift target. -/
omit [DecidableEq V] [DecidableEq W] in
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_cutSideExtensions
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hlift : PeeledCollarCutSideExtensionsToAmbient φ) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G H := by
  intro cut
  rcases hlift cut with ⟨extension⟩
  refine ⟨extension.toAmbientSmallCyclicEdgeCut, ?_⟩
  rw [extension.toAmbientSmallCyclicEdgeCut_card]

/-- Regime-facing inheritance theorem from concrete embedding-side cut
extensions. -/
theorem peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_cutSideExtensions
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H)
    (hlift : PeeledCollarCutSideExtensionsToAmbient φ) :
    CyclicallyFiveEdgeConnected H :=
  peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_smallCutLift
    regime
    (peeledCollarSmallCyclicCutLiftsToAmbient_of_cutSideExtensions hlift)

end Mettapedia.GraphTheory.FourColor
