import Mathlib.Data.List.Basic

/-!
# Memoize successful initialization, preserving retry after a resource stop

This sequential specification distinguishes a pending cell from a completed
failed attempt. Caching the latter as an initialized cell makes a temporary
failure permanent. A successful cell instead keeps the first successful
result and never changes it, while every failed pending attempt leaves the
cell pending. Potential attempt outcomes below are data, not an account of
when an implementation invokes its allocator.

The native seal brand cells realize this protocol using an atomic published
pointer and a mutex around construction. This module does not verify their
C memory ordering or the freshness of the factory's returned objects.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.SuccessfulInitialization

universe u
variable {Value : Type u}

/-- Outer `some` records that a one-shot initializer ran, even if it failed. -/
def sticky (cell : Option (Option Value)) (attempt : Option Value) :
    Option Value × Option (Option Value) :=
  match cell with
  | some result => (result, cell)
  | none => (attempt, some attempt)

/-- Publish successful values only. A failed pending attempt remains pending. -/
def retry (cell attempt : Option Value) : Option Value × Option Value :=
  match cell with
  | some value => (some value, cell)
  | none => (attempt, attempt)

def run (cell : Option Value) : List (Option Value) → List (Option Value) × Option Value
  | [] => ([], cell)
  | attempt :: attempts =>
      let (result, after) := retry cell attempt
      let (results, final) := run after attempts
      (result :: results, final)

def firstSuccess : List (Option Value) → Option Value
  | [] => none
  | none :: rest => firstSuccess rest
  | some value :: _ => some value

theorem successful_cell_stable (value : Value) (attempts : List (Option Value)) :
    run (some value) attempts = (List.replicate attempts.length (some value), some value) := by
  induction attempts with
  | nil => rfl
  | cons attempt attempts ih => simp [run, retry, ih, List.replicate_succ]

/-- The final cell contains exactly the first successful attempt, not the
last result or the first failed attempt. -/
theorem publishes_first_success (attempts : List (Option Value)) :
    (run none attempts).2 = firstSuccess attempts := by
  induction attempts with
  | nil => rfl
  | cons attempt attempts ih =>
      cases attempt with
      | none => simpa [run, retry, firstSuccess] using ih
      | some value => simp [run, retry, firstSuccess, successful_cell_stable]

theorem failed_pending_attempt :
    retry (none : Option Value) none = (none, none) := rfl

theorem one_shot_failure_is_sticky (value : Value) :
    (sticky (sticky none none).2 (some value)).1 = none := rfl

theorem retry_recovers_after_failure (value : Value) :
    (retry (retry none none).2 (some value)).1 = some value := rfl

theorem protocols_differ_after_resource_recovery (value : Value) :
    (sticky (sticky none none).2 (some value)).1 ≠
      (retry (retry none none).2 (some value)).1 := by
  simp [sticky, retry]

#print axioms successful_cell_stable
#print axioms publishes_first_success
#print axioms protocols_differ_after_resource_recovery

end Mettapedia.Computability.SuccessfulInitialization
