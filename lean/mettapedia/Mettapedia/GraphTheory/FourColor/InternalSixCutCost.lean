import Mettapedia.GraphTheory.FourColor.RotationCutDartSum
import Mettapedia.GraphTheory.FourColor.EightPortBoundaryConnectivity

/-! # Internal-six normal form as a constraint on exact cut observations

These bounds concern actual vertex subsets of a cubic graph. They can be
transported through an exact representation change without losing shore
sizes, as required when a local reduction changes its connectivity.
-/

namespace Mettapedia.GraphTheory.FourColor.InternalSixCutCost
open SimpleGraphDartRotation GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24CubicFourEdgeConnectedSides GoertzelV24MinimalTriangleFree
open RotationCutDartSum

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (rotation : Data G)
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

theorem cost_crossing (s : V → Bool) : cost rotation.toRotationSystem s =
    2 * Fintype.card (CrossingSideDart G (fun v => s v = true)) := by
  rw [cost_eq_twice_outgoing]
  congr 1
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro d
  change (s d.fst = true ∧ s d.snd = false) ↔ (s d.fst = true ∧ ¬ s d.snd = true)
  simp

variable (hcubic : G.IsRegularOfDegree 3) (hi : CubicDualInternallySixConnected G)

include hcubic hi
theorem ten_le (s : V → Bool)
    (hyes : 3 ≤ Fintype.card {v // s v = true})
    (hno : 3 ≤ Fintype.card {v // ¬ s v = true}) :
    10 ≤ cost rotation.toRotationSystem s := by
  rw [cost_crossing]
  by_contra hn
  have hh : Fintype.card (CrossingSideDart G (fun v => s v = true)) ≤ 4 := by omega
  have cyc := CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two hcubic
    (fun v => s v = true) (Fintype.card_pos_iff.mp (by omega)) (by omega)
  have five := CyclicFiveBoundary.five_le_crossing_card hcubic hi.1 _ cyc hno
  omega

theorem small_shore (s : V → Bool) (hs : cost rotation.toRotationSystem s ≤ 10) :
    Fintype.card {v // s v = true} ≤ 5 ∨ Fintype.card {v // ¬ s v = true} ≤ 5 := by
  classical
  by_contra! hn
  have hb : Fintype.card (CrossingSideDart G (fun v => s v = true)) ≤ 5 := by
    rw [cost_crossing] at hs
    omega
  have hcompl : Fintype.card (CrossingSideDart G (fun v => ¬ s v = true)) =
      Fintype.card (CrossingSideDart G (fun v => s v = true)) := by
    rw [← card_crossingEdgeFinset_eq_card_crossingSideDart,
      ← card_crossingEdgeFinset_eq_card_crossingSideDart, crossingEdgeFinset_compl]
  let cut : CyclicEdgeCutRealization G (crossingEdgeFinset G (fun v => s v = true)) :=
    { side := fun v => s v = true
      hcut_eq := mem_crossingEdgeFinset_iff _
      hinside_cycle := CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two
        hcubic _ (Fintype.card_pos_iff.mp (by omega)) (by omega)
      houtside_cycle := CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two
        hcubic _ (Fintype.card_pos_iff.mp (by omega)) (by rw [hcompl]; omega) }
  have hh := cut.hasShoreOfSizeAtMost_five hi
    (by rw [card_crossingEdgeFinset_eq_card_crossingSideDart]; exact hb)
  have hs' : Fintype.card {v // s v = true} ≤ 5 ∨
      Fintype.card {v // ¬ s v = true} ≤ 5 := by
    simpa [CyclicEdgeCutRealization.HasShoreOfSizeAtMost,
      CyclicEdgeCutRealization.vertexSide, CyclicEdgeCutRealization.compl,
      cut, Fintype.card_subtype] using hh
  omega

theorem ten_le_selected (s : V → Bool)
    (hyes : 3 ≤ selected s) (hno : 3 ≤ selected (fun v => !(s v))) :
    10 ≤ cost rotation.toRotationSystem s := by
  apply ten_le rotation hcubic hi s
  · simpa only [selected_card] using hyes
  · simpa [selected_card] using hno

theorem small_selected (s : V → Bool) (hs : cost rotation.toRotationSystem s ≤ 10) :
    selected s ≤ 5 ∨ selected (fun v => !(s v)) ≤ 5 := by
  simpa [selected_card] using small_shore rotation hcubic hi s hs

end
end Mettapedia.GraphTheory.FourColor.InternalSixCutCost
