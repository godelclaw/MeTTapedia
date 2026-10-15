import Mettapedia.GSLT.Dynamics.RelationalCardinality
import Mettapedia.GSLT.Dynamics.CollapseObservationContract
import Mettapedia.Machines.ResumableRegion

/-!
# Retained cardinality commits and complete publication

An intersection navigator produces weighted leaves: each weight is the number
of physical occurrence combinations under one assignment. The native cursor
retains the committed total while its range-navigation state is suspended.
This model proves the leaf-commit boundary, checked addition, exact residual
resumption and complete-only publication against independent enumeration.

The model's steps are commits and closure inspection, not native seek ticks or
dialect evaluation fuel. Establishing the navigator's assignment domain and
refining its individual range phases remain separate obligations. The model
does not assert that a native cursor materializes this list of weights.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.RelationalCountResumption

open Mettapedia.Machines
open RelationalCardinality
open CollapseObservationContract

inductive State where
  | running (remaining : List Nat) (total : Nat)
  | complete (total : Nat)
  | overflow (remaining : List Nat) (total : Nat)
  deriving DecidableEq, Repr

def step (maximum : Nat) : State → Option State
  | .running [] total => some (.complete total)
  | .running (weight :: rest) total =>
      match BoundedCount.add? maximum total weight with
      | none => some (.overflow (weight :: rest) total)
      | some next => some (.running rest next)
  | .complete _ | .overflow _ _ => none

abbrev machine (maximum : Nat) : MachineCore (List Nat) where
  State := State
  load := fun weights => .running weights 0
  step := step maximum

def account : State → Nat
  | .running remaining total | .overflow remaining total => total + remaining.sum
  | .complete total => total

def publish : State → Option Nat
  | .complete total => some total
  | .running _ _ | .overflow _ _ => none

/-- The native leaf multiplies each positive range length before committing
the resulting weight. Failure never replaces its existing accumulator. -/
def checkedProduct (maximum : Nat) : Nat → List Nat → Option Nat
  | total, [] => some total
  | total, factor :: rest =>
      match BoundedCount.multiply? maximum total factor with
      | none => none
      | some next => checkedProduct maximum next rest

theorem positive_product (factors : List Nat)
    (positive : ∀ factor ∈ factors, 0 < factor) : 0 < factors.prod := by
  induction factors with
  | nil => simp
  | cons factor rest ih =>
      simp only [List.prod_cons]
      exact Nat.mul_pos (positive factor (by simp))
        (ih fun value member => positive value (by simp [member]))

/-- For surviving nonempty range blocks, checking intermediate products is
exactly checking the final product. Zero blocks are handled by the navigator
before it invokes this multiplication routine. -/
theorem checked_product_exact (maximum total : Nat) (factors : List Nat)
    (initial : total ≤ maximum) (positive : ∀ factor ∈ factors, 0 < factor) :
    checkedProduct maximum total factors =
      if total * factors.prod ≤ maximum then some (total * factors.prod) else none := by
  induction factors generalizing total with
  | nil => simp [checkedProduct, initial]
  | cons factor rest ih =>
      have tailPositive : ∀ value ∈ rest, 0 < value := by
        intro value member
        exact positive value (by simp [member])
      have prefixBound : total * factor ≤ total * factor * rest.prod := by
        have one := positive_product rest tailPositive
        simpa using Nat.mul_le_mul_left (total * factor) one
      by_cases within : total * factor ≤ maximum
      · simp only [checkedProduct, BoundedCount.multiply?, if_pos within]
        rw [ih (total * factor) within tailPositive]
        simp only [List.prod_cons, Nat.mul_assoc]
        rfl
      · have beyond : ¬total * (factor * rest.prod) ≤ maximum := by
          intro fits
          exact within (prefixBound.trans (by simpa only [Nat.mul_assoc] using fits))
        simp [checkedProduct, BoundedCount.multiply?, within, beyond]

/-- Each successful commit moves one weight from the residual to the total.
Overflow keeps that weight and publishes nothing. -/
theorem step_preserves_account (maximum : Nat) (before after : State)
    (transition : step maximum before = some after) :
    account after = account before := by
  cases before with
  | complete total => simp [step] at transition
  | overflow remaining total => simp [step] at transition
  | running remaining total =>
      cases remaining with
      | nil =>
          simp only [step, Option.some.injEq] at transition
          subst after
          simp [account]
      | cons weight rest =>
          cases decision : BoundedCount.add? maximum total weight with
          | none =>
              simp only [step, decision, Option.some.injEq] at transition
              subst after
              rfl
          | some next =>
              have addition := (BoundedCount.add?_eq_some_iff maximum total weight next).mp decision
              simp only [step, decision, Option.some.injEq] at transition
              subst after
              simp [account, addition.2, Nat.add_assoc]

theorem slice_preserves_account (maximum fuel : Nat) (state : State) :
    account (MachineCore.runSlice (machine maximum) fuel state).1 = account state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases transition : step maximum state with
      | none => simp [MachineCore.runSlice, machine, transition]
      | some next =>
          simp only [MachineCore.runSlice, machine, transition]
          exact (ih next).trans (step_preserves_account maximum state next transition)

/-- Resumption composes residual state and exact commit/closure accounting.
This reuses the common machine law; it does not restart the weighted source. -/
theorem slices_compose (maximum first second : Nat) (state : State) :
    MachineCore.runSlice (machine maximum) (first + second) state =
      let earlier := MachineCore.runSlice (machine maximum) first state
      let later := MachineCore.runSlice (machine maximum) second earlier.1
      (later.1, earlier.2 + later.2) :=
  MachineCore.runSlice_add (machine maximum) first second state

theorem publish_requires_completion (state : State) (result : Nat)
    (observed : publish state = some result) : state = .complete result := by
  cases state <;> simp_all [publish]

/-- Enough capacity gives complete publication after every weighted leaf and
one closure inspection. The bound is derived from the whole residual sum. -/
theorem complete_within_capacity (maximum total : Nat) (weights : List Nat)
    (within : total + weights.sum ≤ maximum) :
    MachineCore.runSlice (machine maximum) (weights.length + 1)
      (.running weights total) = (.complete (total + weights.sum), weights.length + 1) := by
  induction weights generalizing total with
  | nil => simp [MachineCore.runSlice, machine, step]
  | cons weight rest ih =>
      have headWithin : total + weight ≤ maximum := by
        simp only [List.sum_cons] at within
        omega
      have remainingWithin : total + weight + rest.sum ≤ maximum := by
        simpa only [List.sum_cons, Nat.add_assoc] using within
      have accepted : BoundedCount.add? maximum total weight = some (total + weight) := by
        simp [BoundedCount.add?, headWithin]
      simp only [List.length_cons]
      rw [MachineCore.runSlice.eq_def]
      simp only [machine, step, accepted]
      change (((machine maximum).runSlice (rest.length + 1) (.running rest (total + weight))).1,
        ((machine maximum).runSlice (rest.length + 1) (.running rest (total + weight))).2 + 1) = _
      rw [ih (total + weight) remainingWithin]
      simp [Nat.add_assoc]

/-- A weighted cursor's complete count equals a separate enumeration of
physical row choices. Assignment enumeration itself belongs to its navigator. -/
theorem complete_count_is_occurrence_enumeration
    {Row Assignment : Type} (assignments : List Assignment)
    (rowsAt : Assignment → List (List Row)) (maximum : Nat)
    (within : countAssignments assignments rowsAt ≤ maximum) :
    publish (MachineCore.runSlice (machine maximum)
      (assignments.length + 1)
      (.running (assignments.map fun assignment => leafMultiplicity (rowsAt assignment)) 0)).1 =
        some (enumerateAssignments assignments rowsAt).length := by
  have completed := complete_within_capacity maximum 0
    (assignments.map fun assignment => leafMultiplicity (rowsAt assignment))
    (by simpa [countAssignments] using within)
  rw [← countAssignments_eq_enumeration_length assignments rowsAt]
  simpa only [List.length_map, countAssignments, publish, Nat.zero_add] using
    congrArg (fun result => publish result.1) completed

/-- Even an overflowed finite run reaches a terminal refusal. It cannot
return a wrapped total or publish a successfully accumulated prefix. -/
theorem over_capacity_refuses (maximum total : Nat) (weights : List Nat)
    (overflowed : maximum < total + weights.sum) (nonempty : weights ≠ []) :
    publish (MachineCore.runSlice (machine maximum) (weights.length + 1)
      (.running weights total)).1 = none := by
  induction weights generalizing total with
  | nil => exact (nonempty rfl).elim
  | cons weight rest ih =>
      by_cases headWithin : total + weight ≤ maximum
      · have accepted : BoundedCount.add? maximum total weight = some (total + weight) := by
          simp [BoundedCount.add?, headWithin]
        have restNonempty : rest ≠ [] := by
          intro empty
          simp [empty] at overflowed
          omega
        have restOverflow : maximum < total + weight + rest.sum := by
          simpa only [List.sum_cons, Nat.add_assoc] using overflowed
        simp only [List.length_cons]
        rw [MachineCore.runSlice.eq_def]
        simp only [machine, step, accepted]
        exact ih (total + weight) restOverflow restNonempty
      · have refused : BoundedCount.add? maximum total weight = none := by
          simp [BoundedCount.add?, headWithin]
        simp [MachineCore.runSlice, machine, step, refused, publish]

/-- A finite publication after any split inherits the original residual
account. No complete observation is inferred merely from budget exhaustion. -/
theorem any_published_slice_is_exact (maximum fuel : Nat) (weights : List Nat)
    (result : Nat)
    (observed : publish (MachineCore.runSlice (machine maximum) fuel
      (.running weights 0)).1 = some result) : result = weights.sum := by
  have complete := publish_requires_completion _ result observed
  have preserved := slice_preserves_account maximum fuel (.running weights 0)
  simpa [complete, account] using preserved

namespace Controls

theorem zero_suffix_does_not_repair_an_overflowed_product :
    checkedProduct 7 1 [8, 0] = none ∧ (1 * ([8, 0] : List Nat).prod) = 0 := by
  constructor <;> rfl

theorem pending_total_is_not_complete :
    MachineCore.runSlice (machine 100) 2 (.running [3, 3, 5] 0) =
      (.running [5] 6, 2) ∧ publish (.running [5] 6) = none := by constructor <;> rfl

theorem replay_invents_occurrences :
    publish (MachineCore.runSlice (machine 100) 4 (.running [3, 3, 5] 6)).1 = some 17 ∧
    publish (MachineCore.runSlice (machine 100) 2 (.running [5] 6)).1 = some 11 := by constructor <;> rfl

theorem overflow_keeps_uncommitted_leaf :
    MachineCore.runSlice (machine 7) 4 (.running [3, 3, 5] 0) =
      (.overflow [5] 6, 3) ∧ publish (.overflow [5] 6) = none := by constructor <;> rfl

theorem independent_residuals_share_the_original_weights :
    MachineCore.runSlice (machine 100) 1 (.running [3, 3, 5] 0) = (.running [3, 5] 3, 1) ∧
    MachineCore.runSlice (machine 100) 3 (.running [3, 3, 5] 0) = (.running [] 11, 3) := by constructor <;> rfl

end Controls

end Mettapedia.GSLT.Dynamics.RelationalCountResumption
