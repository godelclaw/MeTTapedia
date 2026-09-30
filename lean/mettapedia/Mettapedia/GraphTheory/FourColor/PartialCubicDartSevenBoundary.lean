import Mettapedia.GraphTheory.FourColor.PartialCubicDartBoundary
import Mettapedia.GraphTheory.FourColor.CubicDualInternalSixConnectivity

/-!
# Seven unpaired slots and internal-six connectivity

For an odd-sized partial cubic diagram, seven possible ports allow a cut
of size five or seven. If both shores have at least six vertices, internal-six
connectivity excludes the five-cut. Thus every unpaired slot is a genuine
boundary dart. This is the additional geometric obligation at odd width.
-/

namespace Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation.Realization

open _root_.SimpleGraph GoertzelV24CubicSmallBoundaryCycle GoertzelV24MinimalTriangleFree
open GoertzelV24CubicFourEdgeConnectedSides

noncomputable section
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {P : Diagram W} (F : Realization P G)

local instance sevenBoundaryEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Odd cut parity leaves only five or seven; the nontrivial five-cut
exclusion supplies the distinction that cyclic-five connectivity alone lacks. -/
theorem unpaired_leaves_of_internalSix
    (hv : Function.Injective F.vertex)
    (hports : Fintype.card (Unpaired (P := P)) = 7)
    (hodd : Odd (Fintype.card W)) (hlarge : 6 ≤ Fintype.card W)
    (hspace : Fintype.card W + 6 ≤ Fintype.card V)
    (hcubic : G.IsRegularOfDegree 3) (hinternal : CubicDualInternallySixConnected G)
    (p : Unpaired (P := P)) : ¬ F.imageSide (F.dart p.1).snd := by
  classical
  have hcard := F.card_imageSide hv
  have hle := F.crossing_card_le
  rw [hports] at hle
  have hcycle := CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two
    hcubic F.imageSide (Fintype.card_pos_iff.mp (by omega)) (by omega)
  have hpartition := Fintype.card_subtype_compl F.imageSide
  have hfive := CyclicFiveBoundary.five_le_crossing_card hcubic hinternal.1 F.imageSide
    hcycle (by omega)
  have hdegree := card_crossingEdgeFinset_add_twice_internal_eq_three_mul (G := G)
    (fun v => (degree_instance_independent v _ _).trans (hcubic v)) F.imageSide
  rw [card_crossingEdgeFinset_eq_card_crossingSideDart] at hdegree
  simp only [Nat.card_eq_fintype_card] at hdegree
  obtain ⟨k, hk⟩ := hodd
  have hnotfive : Fintype.card (CrossingSideDart G F.imageSide) ≠ 5 := by
    intro he
    have hcompl : Fintype.card (CrossingSideDart G (fun v => ¬ F.imageSide v)) = 5 := by
      rw [← card_crossingEdgeFinset_eq_card_crossingSideDart,
        crossingEdgeFinset_compl, card_crossingEdgeFinset_eq_card_crossingSideDart, he]
    have hout := CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two
      hcubic (fun v => ¬ F.imageSide v) (Fintype.card_pos_iff.mp (by omega)) (by omega)
    let cut : ExactSizedCyclicEdgeCut G 5 :=
      { edgeCut := crossingEdgeFinset G F.imageSide
        side := F.imageSide
        hcut_eq := mem_crossingEdgeFinset_iff F.imageSide
        hcard_eq := by rw [card_crossingEdgeFinset_eq_card_crossingSideDart]; exact he
        hinside_cycle := hcycle
        houtside_cycle := hout }
    have hs := hinternal.2 cut
    have ha : (exactCutVertexSide cut).card = Fintype.card W := by
      simpa [exactCutVertexSide, cut, Fintype.card_subtype] using hcard
    have hb : (exactCutVertexSide cut.compl).card = Fintype.card {v // ¬ F.imageSide v} := by
      rw [← Fintype.card_coe]
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight (fun v => by
        simpa only [ExactSizedCyclicEdgeCut.compl, cut] using
          (mem_exactCutVertexSide_iff cut.compl v))
    omega
  have hseven : Fintype.card (CrossingSideDart G F.imageSide) = 7 := by omega
  have hsurj : Function.Surjective F.crossingIndex := by
    by_contra hn
    have hlt := Fintype.card_lt_of_injective_not_surjective
      F.crossingIndex F.crossingIndex_injective hn
    omega
  obtain ⟨d, hd⟩ := hsurj p
  have he := F.crossingIndex_dart d
  rw [hd] at he
  exact he.symm ▸ d.2.2

end
end Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation.Realization
