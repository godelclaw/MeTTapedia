import Mettapedia.Machines.ConstraintPropagation.Readiness

/-!
# Waiting on one completion signal

A conjunction can wait on its first unfinished signal, then reconstruct its
dependencies after waking. The selected signal is a scheduling choice, not
evidence that the other signals have completed. A resumed producer may have
introduced new signals. Names are local to a retained computation; renaming
them together with their completion map preserves the waiting decision.

This module concerns completion signals, not logical variables or groundness.
Propagation through term binding and foreign attributed-variable hooks are
separate realization obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ConstraintPropagation.FirstPending

variable {Signal : Type*}

def active (completed : Signal → Bool) (signals : List Signal) : List Signal :=
  signals.filter fun signal => !completed signal

def select (completed : Signal → Bool) (signals : List Signal) : Option Signal :=
  (active completed signals).head?

/-- A consumer requires every retained producer to have returned, even when
some signals occur more than once in its dependency list. -/
def Ready (completed : Signal → Bool) (signals : List Signal) : Prop :=
  ∀ signal ∈ signals, completed signal = true

theorem active_exact (completed : Signal → Bool) (signals : List Signal) (signal : Signal) :
    signal ∈ active completed signals ↔ signal ∈ signals ∧ completed signal = false := by
  simp [active]

theorem select_none_iff (completed : Signal → Bool) (signals : List Signal) :
    select completed signals = none ↔ Ready completed signals := by
  simp [select, active, Ready]

theorem selected_is_unfinished (completed : Signal → Bool) (signals : List Signal)
    (signal : Signal) (selected : select completed signals = some signal) :
    signal ∈ signals ∧ completed signal = false := by
  exact (active_exact completed signals signal).mp
    (List.mem_of_mem_head? (by simpa [select, selected] using selected))

theorem select_append (completed : Signal → Bool) (left right : List Signal) :
    select completed (left ++ right) =
      (select completed left).or (select completed right) := by
  simp [select, active, List.filter_append, List.head?_append]

/-- Propagating dependencies does not turn finishing one producer into
permission to run its consumer. Every newly retained producer is included. -/
theorem resumed_ready_iff (completed : Signal → Bool) (retained introduced : List Signal) :
    select completed (retained ++ introduced) = none ↔
      Ready completed retained ∧ Ready completed introduced := by
  rw [select_none_iff]
  simp only [Ready, List.mem_append]
  constructor
  · intro ready
    exact ⟨fun signal member => ready signal (Or.inl member),
      fun signal member => ready signal (Or.inr member)⟩
  · rintro ⟨left, right⟩ signal (member | member)
    · exact left signal member
    · exact right signal member

theorem readiness_perm (completed : Signal → Bool) {first second : List Signal}
    (same : first.Perm second) :
    select completed first = none ↔ select completed second = none := by
  simp only [select_none_iff, Ready, same.mem_iff]

/-- Dropping completed metadata does not change the next dependency. -/
theorem select_active (completed : Signal → Bool) (signals : List Signal) :
    select completed (active completed signals) = select completed signals := by
  simp [select, active, List.filter_filter]

theorem active_map {Other : Type*} (rename : Signal → Other)
    (completed : Signal → Bool) (copied : Other → Bool)
    (preserves : ∀ signal, copied (rename signal) = completed signal)
    (signals : List Signal) :
    active copied (signals.map rename) = (active completed signals).map rename := by
  simp only [active, List.filter_map]
  congr 1
  exact List.filter_congr fun signal _ => by simp [preserves]

/-- Copying the entire signal context preserves both waiting and readiness.
Independence from the original context is a separate freshness property. -/
theorem select_map {Other : Type*} (rename : Signal → Other)
    (completed : Signal → Bool) (copied : Other → Bool)
    (preserves : ∀ signal, copied (rename signal) = completed signal)
    (signals : List Signal) :
    select copied (signals.map rename) = (select completed signals).map rename := by
  simp [select, active_map rename completed copied preserves]

theorem agrees_with_all_watches [DecidableEq Signal] (completed : Signal → Bool)
    (signals : List Signal) :
    select completed signals = none ↔
      (Readiness.probe completed (.requires signals.toFinset)).isReady = true := by
  rw [select_none_iff, Readiness.probe_correct]
  simp [Ready, Readiness.denote]

namespace Controls

def finishedFirst : Nat → Bool := fun signal => signal == 0

example : select finishedFirst [0, 1] = some 1 := by decide
example : select finishedFirst [0, 0] = none := by decide

/-- Looking only at the original dependency list loses a newly posted wait. -/
theorem old_watch_list_is_insufficient :
    select finishedFirst [0] = none ∧ select finishedFirst [0, 1] ≠ none := by
  decide

end Controls

#print axioms selected_is_unfinished
#print axioms resumed_ready_iff
#print axioms select_map
#print axioms agrees_with_all_watches

end Mettapedia.Machines.ConstraintPropagation.FirstPending
