import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicSmallBoundaryCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutAttachment

/-! Exact graph isomorphisms transport cyclic-cut witnesses and their
crossing-edge cardinalities. The inverse-recognition consumer uses this
transport to retain a genuine source obstruction after changing vertices
to rotation-orbit classes. -/

namespace Mettapedia.GraphTheory.FourColor.CyclicEdgeCutIso

open _root_.SimpleGraph GoertzelV24CubicSmallBoundaryCycle

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]

def crossingDartEquiv (f : G ≃g H) (side : V → Prop) :
    CrossingSideDart G side ≃ CrossingSideDart H (fun w => side (f.symm w)) where
  toFun d := ⟨⟨(f d.1.fst, f d.1.snd), f.toHom.map_adj d.1.adj⟩, by simpa using d.2⟩
  invFun d := ⟨⟨(f.symm d.1.fst, f.symm d.1.snd), f.symm.toHom.map_adj d.1.adj⟩, d.2⟩
  left_inv d := by
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    apply Prod.ext <;> simp
  right_inv d := by
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    apply Prod.ext <;> simp

theorem crossing_count (f : G ≃g H) (side : V → Prop) :
    (crossingEdgeFinset H (fun w => side (f.symm w))).card =
      (crossingEdgeFinset G side).card := by
  rw [card_crossingEdgeFinset_eq_card_crossingSideDart,
    card_crossingEdgeFinset_eq_card_crossingSideDart]
  exact (Fintype.card_congr (crossingDartEquiv f side)).symm

theorem cycle_map (f : G ≃g H) {side : V → Prop}
    (h : HasCycleOnSide G side) : HasCycleOnSide H (fun w => side (f.symm w)) := by
  obtain ⟨u, hu, p, hp, hs⟩ := h
  refine ⟨f u, by simpa using hu, p.map f.toHom, hp.map f.injective, ?_⟩
  intro w hw
  rw [Walk.support_map] at hw
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
  simpa using hs v hv

private theorem cut_eq (cut : SmallCyclicEdgeCut G) :
    crossingEdgeFinset G cut.side = cut.edgeCut := by
  ext e
  exact (mem_crossingEdgeFinset_iff cut.side e).trans (cut.hcut_eq e).symm

/-- Both shore cycles and the exact edge count survive the representation
change. -/
def cutMap (f : G ≃g H) (cut : SmallCyclicEdgeCut G) : SmallCyclicEdgeCut H where
  side := fun w => cut.side (f.symm w)
  edgeCut := crossingEdgeFinset H (fun w => cut.side (f.symm w))
  hcut_eq := mem_crossingEdgeFinset_iff _
  hcard_le_four := by rw [crossing_count f, cut_eq cut]; exact cut.hcard_le_four
  hinside_cycle := cycle_map f cut.hinside_cycle
  houtside_cycle := cycle_map f cut.houtside_cycle

theorem cutMap_card (f : G ≃g H) (cut : SmallCyclicEdgeCut G) :
    (cutMap f cut).edgeCut.card = cut.edgeCut.card := by
  change (crossingEdgeFinset H (fun w => cut.side (f.symm w))).card = _
  rw [crossing_count f, cut_eq cut]

theorem cyclic_connectivity (f : G ≃g H) (k : ℕ) :
    CyclicEdgeConnectivityAtLeast G k ↔ CyclicEdgeConnectivityAtLeast H k := by
  constructor
  · intro h cut
    have bound := h (cutMap f.symm cut)
    rwa [cutMap_card] at bound
  · intro h cut
    have bound := h (cutMap f cut)
    rwa [cutMap_card] at bound

end
end Mettapedia.GraphTheory.FourColor.CyclicEdgeCutIso
