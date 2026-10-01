import MettapediaFourColor.BoundaryRepairTransport
import Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision

/-!
# Joint repair descends through an actual boundary-triangle subdivision

The split law retains both new edge colours. Their inequality forces the
retained endpoints to differ, so deleting the inserted vertex reconstructs
a genuine colouring of the old graph. The statement is uniform in the graph,
the remainder of its boundary, and the Kempe-closed exterior relation.
-/

namespace FourColor.BoundaryTriangleRepair

open Color KempeBoundarySplit
open Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision

variable {V : Type*}

def ports (a b : V) (tail : List V) : List (Option V) :=
  some a :: none :: some b :: tail.map some

theorem reconstruct (G : SimpleGraph V) (a b c : V) (tail : List V)
    (x y : Color) (t : List Color) (_hx : x ≠ 0) (_hy : y ≠ 0) (hxy : x ≠ y)
    (h : GraphTrace (subdivide G a b c) (ports a b tail) (x :: y :: t)) :
    GraphTrace G (a :: b :: tail) ((x + y) :: t) := by
  obtain ⟨k, hk⟩ := h
  have hx := congrArg (fun et => et.getD 0 0) hk
  have hy := congrArg (fun et => et.getD 1 0) hk
  have ht := congrArg (List.drop 2) hk
  change x = k (some a) + k none at hx
  change y = k none + k (some b) at hy
  have distinct : k (some a) ≠ k (some b) := by
    intro heq
    apply hxy
    rw [hx, hy, heq, add_comm]
  refine ⟨restrict G a b c k distinct, ?_⟩
  have htail : t = pairmap (· + ·) (k (some b))
      ((tail.map fun v => k (some v)) ++ [k (some a)]) := by
    simpa only [ports, List.map_cons, List.map_map, Function.comp_def, trace_cons,
      List.cons_append, pairmap_cons, List.drop_succ_cons, List.drop_zero] using ht
  rw [hx, hy, htail]
  simp only [List.map_cons, trace_cons, List.cons_append, pairmap_cons]
  change (k (some a) + k none + (k none + k (some b))) :: _ =
    (k (some a) + k (some b)) :: _
  congr 1
  rw [add_assoc, ← add_assoc (k none), add_self, zero_add]

/-- One upper repair supplies the lower repair, without independent choices. -/
theorem repair (G : SimpleGraph V) (a b c : V) (tail : List V)
    (base : Repairs (GraphTrace (subdivide G a b c) (ports a b tail)) (tail.length + 3)) :
    Repairs (GraphTrace G (a :: b :: tail)) (tail.length + 2) := by
  apply repairs_collapse (reconstruct G a b c tail) (by omega)
  simpa only [Nat.add_assoc] using base

end FourColor.BoundaryTriangleRepair
