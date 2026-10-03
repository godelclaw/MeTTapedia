import MettapediaFourColor.ResidualExteriorDiskChecked
import MettapediaFourColor.GraphRotationRows

/-! # Exact cyclic rows for the retained 155-vertex exterior -/

namespace FourColor.ResidualExteriorDisk

open SimpleGraph KempeDetachExample

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem row_adjacent (u v : Fin 155) : v ∈ star u ↔ graph.Adj u v := by
  constructor
  · intro h
    exact of_decide_eq_true (List.all_eq_true.mp (forward_check u) v h)
  · intro h
    exact on_edges (fun u v => v ∈ star u)
      (fun e he => of_decide_eq_true (List.all_eq_true.mp reverse_check e he)) u v h

def rows : GraphRotationRows.Rows graph := ⟨star, row_nodup, row_adjacent⟩

def rotation := rows.rotation (⟨(0, (star 0).head!), by decide +kernel⟩ : graph.Dart)

theorem cyclic : rotation.IsVertexwiseCyclic := rows.cyclic _

theorem connected : graph.Connected := by
  let p := Walk.ofSupport tour (by decide +kernel) tour_chain
  have reach (v : Fin 155) : graph.Reachable (tour.head (by decide +kernel)) v := by
    refine ⟨p.takeUntil v ?_⟩
    simpa only [p, Walk.support_ofSupport] using tour_covers v
  exact ⟨fun u v => (reach u).symm.trans (reach v)⟩

theorem covered : Function.Surjective (fun d : graph.Dart => d.fst) := by
  intro v
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil (star v) (row_nonempty v)
  exact ⟨⟨(v,w), (row_adjacent v w).mp hw⟩, rfl⟩

theorem dart_count : Nat.card graph.Dart = 902 := by
  rw [rows.dart_count]
  decide +kernel

end FourColor.ResidualExteriorDisk
