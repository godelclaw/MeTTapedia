import MettapediaFourColor.PlanarGraphBoundaryClosure
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Cyclic neighbour rows give an exact graph rotation

A duplicate-free row listing exactly a vertex's neighbours specifies one
cycle of outgoing darts. The permutation and its cyclicity follow from the
list laws, without a table of paths between every pair of darts.
-/

namespace FourColor.GraphRotationRows

open Mettapedia.GraphTheory.FourColor.SimpleGraphDartRotation

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

structure Rows (G : SimpleGraph V) where
  star : V → List V
  nodup : ∀ v, (star v).Nodup
  adjacent : ∀ u v, v ∈ star u ↔ G.Adj u v

namespace Rows

variable (rows : Rows G)

def next (u v : V) : V := (rows.star u).formPerm v
def prev (u v : V) : V := (rows.star u).formPerm.symm v

theorem next_adj {u v : V} (h : G.Adj u v) : G.Adj u (rows.next u v) :=
  (rows.adjacent _ _).mp (List.formPerm_apply_mem_of_mem ((rows.adjacent _ _).mpr h))

theorem prev_adj {u v : V} (h : G.Adj u v) : G.Adj u (rows.prev u v) := by
  apply (rows.adjacent _ _).mp
  apply List.mem_of_formPerm_apply_mem
  simpa [prev] using (rows.adjacent _ _).mpr h

def rotation (outer : G.Dart) : Data G where
  vertexRotation := {
    toFun := fun d => ⟨(d.fst, rows.next d.fst d.snd), rows.next_adj d.adj⟩
    invFun := fun d => ⟨(d.fst, rows.prev d.fst d.snd), rows.prev_adj d.adj⟩
    left_inv := fun d => SimpleGraph.Dart.ext _ _
      (Prod.ext rfl ((rows.star d.fst).formPerm.symm_apply_apply d.snd))
    right_inv := fun d => SimpleGraph.Dart.ext _ _
      (Prod.ext rfl ((rows.star d.fst).formPerm.apply_symm_apply d.snd)) }
  vertexRotation_fst := fun _ => rfl
  outer := outer

theorem pow_reading (outer : G.Dart) (n : ℕ) (d : G.Dart) :
    (((rows.rotation outer).vertexRotation ^ n) d).fst = d.fst ∧
    (((rows.rotation outer).vertexRotation ^ n) d).snd =
      ((rows.star d.fst).formPerm ^ n) d.snd := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply]
    exact ⟨ih.1, by change rows.next _ _ = _; rw [ih.1, ih.2]; rfl⟩

theorem cyclic [Finite V] (outer : G.Dart) : (rows.rotation outer).IsVertexwiseCyclic := by
  intro u
  refine ⟨⟨?_, (rows.rotation outer).vertexRotation.injective.injOn, ?_⟩, ?_⟩
  · intro d hd
    exact hd
  · intro d hd
    exact ⟨(rows.rotation outer).vertexRotation.symm d, hd,
      Equiv.apply_symm_apply _ d⟩
  · intro x hx y hy
    have xm : x.snd ∈ rows.star u := (rows.adjacent _ _).mpr (hx ▸ x.adj)
    have ym : y.snd ∈ rows.star u := (rows.adjacent _ _).mpr (hy ▸ y.adj)
    obtain ⟨n, hn⟩ := ((rows.nodup u).isCycleOn_formPerm.2 xm ym).exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast]
    apply SimpleGraph.Dart.ext
    exact Prod.ext ((rows.pow_reading outer n x).1.trans (hx.trans hy.symm))
      ((rows.pow_reading outer n x).2.trans (by rwa [hx]))

end Rows

namespace Rows

variable [Fintype V] [DecidableRel G.Adj] (rows : Rows G)

theorem degree (v : V) : G.degree v = (rows.star v).length := by
  have eq : G.neighborFinset v = (rows.star v).toFinset := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, List.mem_toFinset, rows.adjacent]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, eq,
    List.toFinset_card_of_nodup (rows.nodup v)]

theorem dart_count : Nat.card G.Dart = ∑ v, (rows.star v).length := by
  rw [Nat.card_eq_fintype_card, G.dart_card_eq_sum_degrees]
  simp_rw [rows.degree]

end Rows
end FourColor.GraphRotationRows
