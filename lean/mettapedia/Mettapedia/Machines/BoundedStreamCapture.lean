import Mathlib.Tactic

/-!
# Bounded diagnostic retention with complete stream consumption

The reader retains a bounded prefix but consumes every finite input chunk. Retention
and consumption are independent observations. Native read errors, scheduling,
descriptor lifetimes and compiler correspondence are outside this model.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BoundedStreamCapture

variable {α : Type*}

def consume (capacity : Nat) (stored : List α) (consumed : Nat) :
    List (List α) → List α × Nat
  | [] => (stored, consumed)
  | chunk :: rest =>
    consume capacity ((stored ++ chunk).take capacity)
      (consumed + chunk.length) rest

def capture (capacity : Nat) (chunks : List (List α)) : List α × Nat :=
  consume capacity [] 0 chunks

theorem truncate_before_append (capacity : Nat) (left right : List α) :
    (left.take capacity ++ right).take capacity = (left ++ right).take capacity := by
  induction capacity generalizing left with
  | zero => simp
  | succ capacity ih =>
    cases left with
    | nil => simp
    | cons head tail => simpa using congrArg (List.cons head) (ih tail)

theorem consume_prefix (capacity : Nat) (stored : List α) (consumed : Nat)
    (chunks : List (List α)) (bounded : stored.length ≤ capacity) :
    (consume capacity stored consumed chunks).1 =
      (stored ++ chunks.flatten).take capacity := by
  induction chunks generalizing stored consumed with
  | nil => simpa [consume] using (List.take_eq_self_iff stored).mpr bounded |>.symm
  | cons chunk rest ih =>
    simp only [consume]
    rw [ih _ _ (List.length_take_le _ _), truncate_before_append]
    simp [List.append_assoc]

theorem consume_count (capacity : Nat) (stored : List α) (consumed : Nat)
    (chunks : List (List α)) :
    (consume capacity stored consumed chunks).2 = consumed + chunks.flatten.length := by
  induction chunks generalizing stored consumed with
  | nil => simp [consume]
  | cons chunk rest ih => simp [consume, ih, Nat.add_assoc]

theorem capture_prefix (capacity : Nat) (chunks : List (List α)) :
    (capture capacity chunks).1 = chunks.flatten.take capacity := by
  simpa [capture] using consume_prefix capacity ([] : List α) 0 chunks (by simp)

theorem capture_count (capacity : Nat) (chunks : List (List α)) :
    (capture capacity chunks).2 = chunks.flatten.length := by
  simpa [capture] using consume_count capacity ([] : List α) 0 chunks

theorem retained_length_bound (capacity : Nat) (chunks : List (List α)) :
    (capture capacity chunks).1.length ≤ capacity := by
  rw [capture_prefix]
  exact List.length_take_le _ _

theorem zero_retention_still_consumes (chunks : List (List α)) :
    capture 0 chunks = ([], chunks.flatten.length) := by
  apply Prod.ext
  · simp [capture_prefix]
  · exact capture_count _ _

theorem exhausted_prefix_still_consumes (capacity : Nat) (stored : List α)
    (consumed : Nat) (chunks : List (List α)) (full : stored.length = capacity) :
    consume capacity stored consumed chunks =
      (stored, consumed + chunks.flatten.length) := by
  apply Prod.ext
  · rw [consume_prefix _ _ _ _ (by omega), List.take_append]
    simp [full]
  · exact consume_count _ _ _ _

theorem empty_chunk_is_stutter (capacity : Nat) (stored : List α)
    (consumed : Nat) (chunks : List (List α)) (bounded : stored.length ≤ capacity) :
    consume capacity stored consumed ([] :: chunks) =
      consume capacity stored consumed chunks := by
  simp [consume, (List.take_eq_self_iff stored).mpr bounded]

theorem full_stream_control : capture 2 ([[1, 2], [3, 4, 5]] : List (List Nat)) =
    ([1, 2], 5) := by decide

theorem early_close_loses_consumption :
    (2 : Nat) ≠ (capture 2 ([[1, 2], [3, 4, 5]] : List (List Nat))).2 := by decide

end Mettapedia.Machines.BoundedStreamCapture
