import MettapediaFourColor.ThreeBlockDiskBoundary

/-! # Complete core rows exclude extra ambient edges

The source row is closed under the actual vertex rotation. Vertexwise
cyclicity therefore forces every ambient neighbour of a core vertex to
occur in that row. No degree equality or complete-star assumption is used.
-/

namespace FourColor.ThreeBlockDiskBoundary

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open FiveTriangleCollapseObstruction

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem core_nonempty : ∀ i : Fin 18, 11 ≤ i.val → ∃ j, upper.graph.Adj i j := by
  decide +kernel

theorem core_predecessor : ∀ i j : Fin 18, 11 ≤ i.val → upper.graph.Adj i j →
    ∃ k, upper.graph.Adj i k ∧ Turn i k j := by decide +kernel

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {data : Data G}
  (r : Reading data)

omit [DecidableEq V] in
/-- An exact cyclic core reading already determines its complete ambient star. -/
theorem core_stars (cyclic : data.IsVertexwiseCyclic)
    (i : Fin 18) (hi : 11 ≤ i.val) (v : V) (hv : G.Adj (r.hom i) v) :
    ∃ j, r.hom j = v ∧ upper.graph.Adj i j := by
  obtain ⟨j, hj⟩ := core_nonempty i hi
  let start : G.Dart := ⟨(r.hom i, r.hom j), r.hom.map_rel hj⟩
  have powers : ∀ n : ℕ, ∃ k, ∃ hk : upper.graph.Adj i k,
      (data.vertexRotation ^ n) start = ⟨(r.hom i, r.hom k), r.hom.map_rel hk⟩ := by
    intro n
    induction n with
    | zero => exact ⟨j, hj, rfl⟩
    | succ n ih =>
      obtain ⟨k, hk, hpow⟩ := ih
      obtain ⟨l, hl, turn⟩ := core_predecessor i k hi hk
      obtain ⟨_, _, step⟩ := r.turn i l k turn
      refine ⟨l, hl, ?_⟩
      rw [pow_succ', Equiv.Perm.mul_apply, hpow]
      exact step
  have same := (cyclic (r.hom i)).2
    (show start.fst = r.hom i from rfl)
    (show (⟨(r.hom i, v), hv⟩ : G.Dart).fst = r.hom i from rfl)
  obtain ⟨n, hn⟩ := same.exists_nat_pow_eq
  obtain ⟨k, hk, hpow⟩ := powers n
  rw [hn] at hpow
  exact ⟨k, (congrArg (fun d => d.snd) hpow).symm, hk⟩

end FourColor.ThreeBlockDiskBoundary
