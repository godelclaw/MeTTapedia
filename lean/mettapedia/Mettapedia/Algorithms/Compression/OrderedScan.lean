import Mathlib.Data.List.TakeDrop

/-! Ordered inclusive scans with explicit missing observations and faults.
The first present value seeds each fiber. The operator need not be associative,
commutative or total; successful concatenated runs retain exact prefix state. -/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.OrderedScan

variable {α : Type*}

def advance (combine : α → α → Option α) (state input : Option α) :
    Option (Option α × Option α) :=
  match input with
  | none => some (state, none)
  | some value =>
      match state with
      | none => some (some value, some value)
      | some previous => (combine previous value).map fun next => (some next, some next)

def run (combine : α → α → Option α) (state : Option α) :
    List (Option α) → Option (Option α × List (Option α))
  | [] => some (state, [])
  | first :: rest =>
      match advance combine state first with
      | none => none
      | some (next, emitted) =>
          match run combine next rest with
          | none => none
          | some (final, outputs) => some (final, emitted :: outputs)

theorem run_append (combine : α → α → Option α) (first second : List (Option α))
    (state : Option α) :
    run combine state (first ++ second) =
      (match run combine state first with
      | none => none
      | some (middle, before) =>
          match run combine middle second with
          | none => none
          | some (final, after) => some (final, before ++ after)) := by
  induction first generalizing state with
  | nil =>
      simp only [List.nil_append, run]
      cases run combine state second <;> rfl
  | cons head tail ih =>
      simp only [List.cons_append, run]
      cases found : advance combine state head with
      | none => simp
      | some step =>
          obtain ⟨next, emitted⟩ := step
          simp only [ih]
          cases before : run combine next tail with
          | none => simp
          | some priorResult =>
              obtain ⟨middle, outputs⟩ := priorResult
              dsimp only
              cases after : run combine middle second with
              | none => rfl
              | some laterResult =>
                  obtain ⟨final, outputs'⟩ := laterResult
                  rfl

theorem advance_support (combine : α → α → Option α) (state input next emitted : Option α)
    (found : advance combine state input = some (next, emitted)) :
    emitted.isSome = input.isSome := by
  cases input with
  | none => simp only [advance, Option.some.injEq, Prod.mk.injEq] at found; rw [← found.2]
  | some value =>
      cases state with
      | none => simp only [advance, Option.some.injEq, Prod.mk.injEq] at found; rw [← found.2]
      | some previous =>
          cases chosen : combine previous value with
          | none => simp [advance, chosen] at found
          | some result =>
              simp only [advance, chosen, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
              rw [← found.2]
              rfl

theorem support_preserved (combine : α → α → Option α) (inputs outputs : List (Option α))
    (state final : Option α) (found : run combine state inputs = some (final, outputs)) :
    outputs.map Option.isSome = inputs.map Option.isSome := by
  induction inputs generalizing state outputs with
  | nil =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at found
      rw [← found.2]
  | cons head tail ih =>
      cases step : advance combine state head with
      | none => simp [run, step] at found
      | some pair =>
          obtain ⟨next, emitted⟩ := pair
          cases later : run combine next tail with
          | none => simp [run, step, later] at found
          | some pair =>
              obtain ⟨last, rest⟩ := pair
              simp only [run, step, later, Option.some.injEq, Prod.mk.injEq] at found
              rw [← found.2, List.map_cons, advance_support combine state head next emitted step,
                ih rest next (by rw [later, found.1])]
              rfl

theorem length_preserved (combine : α → α → Option α) (inputs outputs : List (Option α))
    (state final : Option α) (found : run combine state inputs = some (final, outputs)) :
    outputs.length = inputs.length := by
  simpa only [List.length_map] using congrArg List.length
    (support_preserved combine inputs outputs state final found)

theorem split_success (combine : α → α → Option α) (first second outputs : List (Option α))
    (state final : Option α) (found : run combine state (first ++ second) = some (final, outputs)) :
    ∃ middle before after,
      run combine state first = some (middle, before) ∧
      run combine middle second = some (final, after) ∧ outputs = before ++ after := by
  rw [run_append] at found
  cases before : run combine state first with
  | none => simp [before] at found
  | some priorResult =>
      obtain ⟨middle, prior⟩ := priorResult
      cases after : run combine middle second with
      | none => simp [before, after] at found
      | some laterResult =>
          obtain ⟨last, later⟩ := laterResult
          simp only [before, after, Option.some.injEq, Prod.mk.injEq] at found
          exact ⟨middle, prior, later, rfl, by rw [after, found.1], found.2.symm⟩

theorem prefix_succeeds (combine : α → α → Option α) (inputs outputs : List (Option α))
    (state final : Option α) (found : run combine state inputs = some (final, outputs)) (size : Nat)
    (within : size ≤ inputs.length) :
    ∃ middle prior, run combine state (inputs.take size) = some (middle, prior) ∧
      prior = outputs.take size := by
  have split := split_success combine (inputs.take size) (inputs.drop size) outputs state final
    (by simpa only [List.take_append_drop] using found)
  obtain ⟨middle, prior, suffix, before, after, joined⟩ := split
  refine ⟨middle, prior, before, ?_⟩
  have lengths := length_preserved combine (inputs.take size) prior state middle before
  have sameLength : prior.length = size := by simpa [List.length_take, Nat.min_eq_left within] using lengths
  rw [joined, ← sameLength, List.take_left]

theorem fault_persists (combine : α → α → Option α) (first second : List (Option α))
    (state : Option α) (failed : run combine state first = none) :
    run combine state (first ++ second) = none := by
  rw [run_append, failed]

namespace Controls

def checkedAdd (left right : Int) : Option Int :=
  let result := left + right
  if -9223372036854775808 ≤ result ∧ result ≤ 9223372036854775807 then some result else none

theorem missing_stays_missing :
    run checkedAdd none [some 7, none, some 3] = some (some 10, [some 7, none, some 10]) := by decide

theorem first_value_is_not_added_to_zero :
    run (fun x y : Int => some (x - y)) none [some 10, some 3, some 2] =
      some (some 5, [some 10, some 7, some 5]) := by decide

theorem reassociation_changes_the_result : (10 - 3 : Int) - 2 ≠ 10 - (3 - 2) := by decide

theorem overflow_is_a_fault :
    run checkedAdd none [some 9223372036854775807, some 1] = none := by decide

theorem continuation_retains_the_prefix :
    run checkedAdd (some 7) [none, some 3] = some (some 10, [none, some 10]) := by decide

end Controls

end Mettapedia.Algorithms.Compression.OrderedScan
