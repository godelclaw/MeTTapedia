import Mettapedia.GraphTheory.Representation.MaterializedSparseFrontier

/-!
# Sparse traversal controls

The examples distinguish entry visits from finalization, lawful neighbor
enumeration from duplicate occurrences, and natural walk counts from a
coefficient readout that loses information.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.Representation.SparseFrontier.Controls

open NeighborEnumeration
open Mettapedia.GSLT.Dynamics

/-- Three neighbors need three entry visits and one finalization. -/
theorem star_row_account :
    ((ofRows AdjacencyRows.Canary.starAndIsolated).update (fun _ => (1 : Nat)) 0).work = 3 ∧
      (traversalPath (ofRows AdjacencyRows.Canary.starAndIsolated)
        (fun _ => (1 : Nat)) 0).length = 4 := by
  constructor
  · decide
  · exact (traversal_complete _ _ _ _ (traversalPath _ _ _)).2

/-- An isolated vertex requires no neighbor visit but still finalizes. -/
theorem isolated_row_account :
    (ofRows AdjacencyRows.Canary.starAndIsolated).update (fun _ => (1 : Nat)) 4 = ⟨0, 0⟩ ∧
      (traversalPath (ofRows AdjacencyRows.Canary.starAndIsolated)
        (fun _ => (1 : Nat)) 4).length = 1 := by
  constructor
  · decide
  · exact (traversal_complete _ _ _ _ (traversalPath _ _ _)).2

/-- A round visits six stored neighbors rather than all twenty-five cells
of this graph's dense square matrix. This is an entry-account comparison. -/
theorem sparse_round_account :
    (∑ vertex : Fin 5,
      ((ofRows AdjacencyRows.Canary.starAndIsolated).update (fun _ => (1 : Nat)) vertex).work) = 6 ∧
      6 < 5 * 5 := by decide

theorem duplicates_change_the_sum :
    accumulate (fun _ : Fin 3 => (1 : Nat)) [1, 1] 0 = 2 ∧
      accumulate (fun _ : Fin 3 => (1 : Nat)) [1] 0 = 1 := by decide

/-- Duplicate entries cannot be passed off as a valid enumeration, even when
their membership relation answers the same adjacency queries. -/
theorem duplicate_row_refused (graph : SimpleGraph (Fin 3)) :
    ¬ ∃ enumeration : NeighborEnumeration graph, enumeration.row 0 = [1, 1] := by
  rintro ⟨enumeration, duplicate⟩
  have unique := enumeration.nodup 0
  rw [duplicate] at unique
  simp at unique

/-- Row permutation preserves the sum but not the ordered prefix states. -/
theorem equal_sum_different_first_prefix :
    accumulate (fun vertex : Fin 3 => vertex.val) [1, 2] 0 =
      accumulate (fun vertex : Fin 3 => vertex.val) [2, 1] 0 ∧
      accumulate (fun vertex : Fin 3 => vertex.val) [1] 0 ≠
        accumulate (fun vertex : Fin 3 => vertex.val) [2] 0 := by decide

/-- The existing occurrence-wise module feeds a genuine two-hop sparse walk. -/
theorem authored_path_two_hops :
    (ofCSR (MaterializedSparseFrontier.packed EdgeList.Canary.path3)).iterate
      (fun vertex => if (0 : Fin 3) = vertex then (1 : Nat) else 0) 2 2 = 1 := by decide

theorem authored_path_one_hop_absent :
    (ofCSR (MaterializedSparseFrontier.packed EdgeList.Canary.path3)).iterate
      (fun vertex => if (0 : Fin 3) = vertex then (1 : Nat) else 0) 1 2 = 0 := by decide

theorem sparse_counts_retain_two_returns :
    (ofMatrix MatrixSemantics.Controls.path3).iterate
      (fun vertex => if (1 : Fin 3) = vertex then (1 : Nat) else 0) 2 1 = 2 := by decide

/-- A semiring homomorphism can preserve execution while erasing a positive
walk count. Sparse storage does not repair coefficient information loss. -/
theorem modular_readout_loses_positive_count :
    (ofMatrix MatrixSemantics.Controls.path3).iterate
      (fun vertex => if (1 : Fin 3) = vertex then (1 : Nat) else 0) 2 1 = 2 ∧
      (ofMatrix MatrixSemantics.Controls.path3).iterate
        (fun vertex => if (1 : Fin 3) = vertex then (1 : ZMod 2) else 0) 2 1 = 0 := by
  constructor <;> decide

end Mettapedia.GraphTheory.Representation.SparseFrontier.Controls
