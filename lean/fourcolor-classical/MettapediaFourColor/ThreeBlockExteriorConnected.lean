import MettapediaFourColor.ThreeBlockDiskDeletion
import MettapediaFourColor.ThreeBlockDiskStars

/-! # Core deletion preserves connectedness

Every exterior neighbour of the deleted core is a boundary port. The
retained boundary cycle connects all such ports. Collapsing the core to
one boundary port maps each ambient edge to exterior reachability.
-/

namespace FourColor.ThreeBlockDiskBoundary

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open FiveTriangleCollapseObstruction

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {data : Data G}
  (r : Reading data)

theorem ports_reachable (j : Fin 11) :
    (G.induce (keep r)).Reachable (port r 0) (port r j) := by
  have reach : ∀ n (hn : n < 11),
      (G.induce (keep r)).Reachable (port r 0) (port r ⟨n, hn⟩) := by
    intro n
    induction n with
    | zero => intro _; exact .refl _
    | succ n ih =>
      intro hn
      have add : (⟨n, by omega⟩ : Fin 11) + 1 = ⟨n + 1, hn⟩ := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt hn]
      have edge := (boundaryDart r ⟨n, by omega⟩).adj.reachable
      rw [show (boundaryDart r ⟨n, by omega⟩).snd =
        port r (⟨n, by omega⟩ + 1) from rfl, add] at edge
      exact (ih (by omega)).trans edge
  exact reach j.val j.isLt

theorem boundary_neighbor (cyclic : data.IsVertexwiseCyclic)
    {u v : V} (hu : u ∈ keep r) (hv : v ∉ keep r) (edge : G.Adj u v) :
    ∃ j : Fin 11, (port r j).val = u := by
  classical
  change ¬ ¬ v ∈ r.hom '' {i : Fin 18 | 11 ≤ i.val} at hv
  obtain ⟨i, hi, rfl⟩ := not_not.mp hv
  obtain ⟨j, hj, _⟩ := core_stars r cyclic i hi u edge.symm
  have low : j.val < 11 := (keep_point r j).mp (hj ▸ hu)
  exact ⟨⟨j.val, low⟩, hj⟩

theorem outside_connected (cyclic : data.IsVertexwiseCyclic) (conn : G.Connected) :
    (G.induce (keep r)).Connected := by
  classical
  let f (v : V) : keep r := if h : v ∈ keep r then ⟨v, h⟩ else port r 0
  have fixed (v : keep r) : f v.val = v := by simp [f, v.property]
  have edge : ∀ u v, G.Adj u v → (G.induce (keep r)).Reachable (f u) (f v) := by
    intro u v huv
    by_cases hu : u ∈ keep r <;> by_cases hv : v ∈ keep r
    · simpa only [f, dite_eq_left hu, dite_eq_left hv] using
        (show (G.induce (keep r)).Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv).reachable
    · obtain ⟨j, hj⟩ := boundary_neighbor r cyclic hu hv huv
      have eq : (⟨u, hu⟩ : keep r) = port r j := Subtype.ext hj.symm
      simpa only [f, dite_eq_left hu, dite_eq_right hv, eq] using (ports_reachable r j).symm
    · obtain ⟨j, hj⟩ := boundary_neighbor r cyclic hv hu huv.symm
      have eq : (⟨v, hv⟩ : keep r) = port r j := Subtype.ext hj.symm
      simpa only [f, dite_eq_right hu, dite_eq_left hv, eq] using ports_reachable r j
    · simp only [f, dite_eq_right hu, dite_eq_right hv]
      exact .refl _
  have walk : ∀ {u v}, G.Walk u v → (G.induce (keep r)).Reachable (f u) (f v) := by
    intro u v p
    induction p with
    | nil => exact .refl _
    | cons h p ih => exact (edge _ _ h).trans ih
  letI : Nonempty (keep r) := ⟨port r 0⟩
  refine ⟨?_⟩
  intro u v
  obtain ⟨p⟩ := conn u.val v.val
  simpa only [fixed] using walk p

end
end FourColor.ThreeBlockDiskBoundary
