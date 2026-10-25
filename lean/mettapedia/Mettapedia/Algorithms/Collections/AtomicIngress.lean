import Mathlib.Data.List.Basic

/-!
Ordered map/flat-map ingestion with private staging. Each projection here is
a completed value; runtime admission must establish that the callback is
pure and has that cardinality. Unsupported callbacks belong to the authored
route. The law below connects incremental staging to materialize-then-append,
not to the native implementation's memory management.
-/

namespace Mettapedia.Algorithms.Collections.AtomicIngress

variable {Input Row : Type*}

/-- Accumulate admitted batches without mutating the destination. -/
def stage (project : Input → List Row) (admit : Row → Bool)
    (pending : List Row) : List Input → Option (List Row)
  | [] => some pending
  | item :: rest =>
      let batch := project item
      if batch.all admit then stage project admit (pending ++ batch) rest else none

/-- Validation may be interleaved with projection, but it preserves the
complete sequence, including repeated rows, when it succeeds. -/
theorem stage_eq_materialized (project : Input → List Row) (admit : Row → Bool)
    (inputs : List Input) (pending : List Row) :
    stage project admit pending inputs =
      if (inputs.flatMap project).all admit
      then some (pending ++ inputs.flatMap project) else none := by
  induction inputs generalizing pending with
  | nil => simp [stage]
  | cons item rest ih =>
      cases accepted : (project item).all admit <;>
        simp [stage, accepted, ih, List.all_append, List.append_assoc]

theorem sequential_append_eq_flatMap (project : Input → List Row)
    (inputs : List Input) (destination : List Row) :
    inputs.foldl (fun rows item => rows ++ project item) destination =
      destination ++ inputs.flatMap project := by
  induction inputs generalizing destination with
  | nil => simp
  | cons item rest ih => simp [ih, List.append_assoc]

/-- A declined attempt returns no publication; the caller retains its
original destination and executes the authored route. -/
def publication (destination : List Row) (pending : Option (List Row)) : Option (List Row) :=
  pending.map (destination ++ ·)

theorem publication_eq_sequential (project : Input → List Row) (admit : Row → Bool)
    (inputs : List Input) (destination : List Row) :
    publication destination (stage project admit [] inputs) =
      if (inputs.flatMap project).all admit then
        some (inputs.foldl (fun rows item => rows ++ project item) destination)
      else none := by
  rw [stage_eq_materialized, sequential_append_eq_flatMap]
  split <;> simp_all [publication]

example : publication [9] (stage (fun n : Nat => [n, n]) (fun _ => true) [] [2, 1]) =
    some [9, 2, 2, 1, 1] := by decide +kernel

example : publication [9] (stage (fun n : Nat => [n]) (· != 3) [] [1, 2, 3]) =
    none := by decide +kernel

#print axioms stage_eq_materialized
#print axioms publication_eq_sequential

end Mettapedia.Algorithms.Collections.AtomicIngress
