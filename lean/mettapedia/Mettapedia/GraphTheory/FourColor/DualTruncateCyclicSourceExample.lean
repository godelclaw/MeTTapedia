import Mettapedia.GraphTheory.FourColor.DualTruncateCyclicSource
import Mettapedia.GraphTheory.FourColor.DualTruncateCoupledExample

/-!
# A source cut constraint consumed on the actual cube

A small finite check concerns the cube's cuts, not its colourings. Its exact
boundary-count interpretation establishes cyclic edge-connectivity. The
general cut theorem derives every connected two-vertex deletion and supplies
the actual target colouring and faithful construction witnesses.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateCyclicSourceExample

open _root_.SimpleGraph GoertzelV24CubicSmallBoundaryCycle
open DualTruncateColoring GoertzelV24FaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace
open VertexConstructionGSLT

noncomputable section
abbrev source := DualTruncateCoupledExample.source
abbrev graph := DualTruncateCoupledExample.graph

/-- The finite observation counts actual oriented crossing edges. -/
def boundaryPairs (inside : Finset (Fin 8)) : Finset (Fin 8 × Fin 8) :=
  Finset.univ.filter (fun p => graph.Adj p.1 p.2 ∧ p.1 ∈ inside ∧ p.2 ∉ inside)

/-- Every nontrivial shore of the cube has at least four crossing edges.
This checks all 256 vertex sides, with no colour-word input. -/
theorem finite_boundary_bound :
    ∀ inside : Finset (Fin 8), 2 ≤ inside.card →
      2 ≤ (Finset.univ \ inside).card → 4 ≤ (boundaryPairs inside).card := by
  decide +kernel

/-- The executable boundary observation equals the graph dart count exactly. -/
theorem boundaryPairs_card (inside : Finset (Fin 8)) :
    (boundaryPairs inside).card =
      Fintype.card (CrossingSideDart graph (fun v => v ∈ inside)) := by
  let equiv : CrossingSideDart graph (fun v => v ∈ inside) ≃
      {p : Fin 8 × Fin 8 // p ∈ boundaryPairs inside} :=
    { toFun := fun d => ⟨d.1.toProd, by simp [boundaryPairs, d.1.adj, d.2]⟩
      invFun := fun p =>
        let hp := (Finset.mem_filter.mp p.2).2
        ⟨⟨p.1, hp.1⟩, hp.2⟩
      left_inv := fun d => by apply Subtype.ext; rfl
      right_inv := fun p => rfl }
  have h := Fintype.card_congr equiv
  rw [Fintype.card_coe] at h
  exact h.symm

private theorem two_le_filter_of_cycle (side : Fin 8 → Prop)
    [DecidablePred side]
    (hcycle : HasCycleOnSide graph side) :
    2 ≤ (Finset.univ.filter side).card := by
  classical
  obtain ⟨v, hv, walk, hc, hs⟩ := hcycle
  cases walk with
  | nil => exact (hc.ne_nil rfl).elim
  | @cons v w _ hadj tail =>
    have hw : side w := hs w (by simp)
    have hsubset : ({v, w} : Finset (Fin 8)) ⊆ Finset.univ.filter side := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> simp [hv, hw]
    simpa [hadj.ne] using Finset.card_le_card hsubset

/-- The finite cut check is interpreted as the actual cyclic connectivity
predicate used by the structural source theorem. -/
theorem cyclic_four : CyclicEdgeConnectivityAtLeast graph 4 := by
  classical
  intro cut
  let inside := Finset.univ.filter cut.side
  have hside : (fun v => v ∈ inside) = cut.side := by
    funext v
    exact propext (by simp [inside])
  have hcompl : Finset.univ \ inside = Finset.univ.filter (fun v => ¬cut.side v) := by
    ext v
    simp [inside]
  have hbound := finite_boundary_bound inside
    (two_le_filter_of_cycle cut.side cut.hinside_cycle)
    (by rw [hcompl]; exact two_le_filter_of_cycle _ cut.houtside_cycle)
  rw [boundaryPairs_card, hside, ← card_crossingEdgeFinset_eq_card_crossingSideDart] at hbound
  have hcut : crossingEdgeFinset graph cut.side = cut.edgeCut := by
    ext edge
    exact (mem_crossingEdgeFinset_iff cut.side edge).trans (cut.hcut_eq edge).symm
  rwa [hcut] at hbound

theorem regular : graph.IsRegularOfDegree 3 := by
  intro v
  rw [← card_neighborFinset_eq_degree]
  have h : graph.neighborFinset v = Finset.univ.filter (graph.Adj v) := by
    ext w
    simp
  rw [h]
  fin_cases v <;> decide +kernel

/-- All pair deletions follow from one source cut law. -/
theorem every_pair_deletion_connected (a b : Fin 8) (hab : a ≠ b) :
    (graph.induce {v | v ≠ a ∧ v ≠ b}).Connected :=
  CubicPairDeletionConnectivity.pairDeletion_connected graph regular cyclic_four a b hab

theorem connected : graph.Connected := by
  have reach (v : Fin 8) : graph.Reachable 0 v := by
    by_cases h1 : v = 1
    · subst v
      exact DualTruncateCoupledExample.root_adj_one.reachable
    by_cases h3 : v = 3
    · subst v
      exact DualTruncateCoupledExample.root_adj_three.reachable
    let w : CoupledThreeColouring.Retained (1 : Fin 8) 3 := ⟨v, h1, h3⟩
    exact (DualTruncateCoupledExample.retained_reachable w).map
      (SimpleGraph.Embedding.induce (G := graph) {v | v ≠ 1 ∧ v ≠ 3}).toHom
  exact { preconnected := fun u v => (reach u).symm.trans (reach v) }

theorem noncomplete : ¬∀ x y : Fin 8, x ≠ y → graph.Adj x y := by
  intro h
  exact DualTruncateCoupledExample.pair_nonadjacent (h 1 3 (by decide))

/-- The specified coupled choice is supplied by source cut structure. -/
theorem shared_source_colouring :
    ∃ c : ThreeVertexColoring source, c.colour 1 = c.colour 3 :=
  DualTruncateCyclicSource.source_of_cyclic_pair source regular cyclic_four (by decide)
    DualTruncateCoupledExample.pair_nonadjacent
    DualTruncateCoupledExample.root_adj_one DualTruncateCoupledExample.root_adj_three

theorem target_tait : RotationSystemTaitColorable (rotation source) :=
  DualTruncateCyclicSource.tait source regular cyclic_four connected noncomplete

theorem every_complete_sweep (order : List source.D) (hn : order.Nodup)
    (he : order ≠ []) (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (route (encodeClosed (cubic source) (DualTruncateConstructionGSLT.rotationCyclic source)
        order hn he hcover).trace) Fin.elim0 Fin.elim0 :=
  DualTruncateCyclicSource.every_complete_sweep source regular cyclic_four connected
    noncomplete order hn he hcover

end
end Mettapedia.GraphTheory.FourColor.DualTruncateCyclicSourceExample
