import Mathlib

/-!
# Provider resource lifetime

This file models the resource boundary around one external model-provider
request.  The relevant invariant is independent of whether the request
succeeds: the caller owns a connection before the first blocking operation and
releases it on every exit path.

The executable implementation and its tests establish refinement to this
model.  Lean proves the transition-level consequence: any finite sequence of
provider outcomes preserves the baseline live-descriptor count, and uses at
most one temporary descriptor beyond that baseline.
-/

namespace PettaClaw.ProviderResourceLifetime

/-- All exits from the provider boundary that matter to resource ownership. -/
inductive Outcome where
  | answered
  | httpError
  | connectTimeout
  | headerTimeout
  | readTimeout
  | malformedJSON
deriving Repr, DecidableEq

/-- `live` is the currently owned descriptor count. `peak` remembers the
largest count observed so far. -/
structure ResourceState where
  live : Nat
  peak : Nat
deriving Repr, DecidableEq

/-- Acquisition happens before any potentially blocking transport operation. -/
def acquire (state : ResourceState) : ResourceState :=
  { live := state.live + 1
    peak := max state.peak (state.live + 1) }

/-- The provider boundary releases the descriptor it just acquired. -/
def release (state : ResourceState) : ResourceState :=
  { state with live := state.live - 1 }

/-- The unconditional-finalizer transition. The outcome affects the value
returned to the agent, but not ownership of the transport resource. -/
def request (_outcome : Outcome) (state : ResourceState) : ResourceState :=
  release (acquire state)

theorem request_restores_live (outcome : Outcome) (state : ResourceState) :
    (request outcome state).live = state.live := by
  simp [request, release, acquire]

theorem request_peak (outcome : Outcome) (state : ResourceState) :
    (request outcome state).peak = max state.peak (state.live + 1) := by
  rfl

/-- Every enumerated exit path obeys the same close discipline. -/
theorem every_outcome_restores_live (state : ResourceState) :
    (request .answered state).live = state.live ∧
    (request .httpError state).live = state.live ∧
    (request .connectTimeout state).live = state.live ∧
    (request .headerTimeout state).live = state.live ∧
    (request .readTimeout state).live = state.live ∧
    (request .malformedJSON state).live = state.live := by
  simp [request_restores_live]

/-- Run a finite sequence of cognitive provider turns. -/
def run : List Outcome → ResourceState → ResourceState
  | [], state => state
  | outcome :: rest, state => run rest (request outcome state)

theorem run_restores_live (outcomes : List Outcome)
    (state : ResourceState) :
    (run outcomes state).live = state.live := by
  induction outcomes generalizing state with
  | nil => rfl
  | cons outcome rest ih =>
      simp only [run]
      rw [ih, request_restores_live]

theorem run_peak_le (outcomes : List Outcome) (state : ResourceState) :
    (run outcomes state).peak ≤ max state.peak (state.live + 1) := by
  induction outcomes generalizing state with
  | nil => exact Nat.le_max_left _ _
  | cons outcome rest ih =>
      simp only [run]
      calc
        (run rest (request outcome state)).peak
            ≤ max (request outcome state).peak
                ((request outcome state).live + 1) := ih _
        _ = max state.peak (state.live + 1) := by
          simp [request_peak, request_restores_live]

/-- If the process starts below its descriptor limit, no finite sequence of
provider outcomes can consume the remaining descriptor capacity. -/
theorem run_preserves_below_limit (outcomes : List Outcome)
    (state : ResourceState) (limit : Nat) (below : state.live < limit) :
    (run outcomes state).live < limit := by
  simpa [run_restores_live outcomes state] using below

/-! ## The unowned timeout transition -/

/-- A timeout path that acquires a descriptor but has no caller-owned
finalizer. This is the failure shape excluded by `request`. -/
def unownedTimeout (state : ResourceState) : ResourceState :=
  acquire state

def runUnownedTimeouts : Nat → ResourceState → ResourceState
  | 0, state => state
  | n + 1, state => runUnownedTimeouts n (unownedTimeout state)

theorem runUnownedTimeouts_live (n : Nat) (state : ResourceState) :
    (runUnownedTimeouts n state).live = state.live + n := by
  induction n generalizing state with
  | zero => simp [runUnownedTimeouts]
  | succ n ih =>
      simp only [runUnownedTimeouts, ih, unownedTimeout, acquire]
      omega

/-- Repeating an unowned timeout exactly fills any finite remaining capacity. -/
theorem unowned_timeouts_reach_limit (state : ResourceState) (limit : Nat)
    (fits : state.live ≤ limit) :
    (runUnownedTimeouts (limit - state.live) state).live = limit := by
  rw [runUnownedTimeouts_live]
  omega

/-- By contrast, explicitly finalized timeouts cannot accumulate. -/
theorem finalized_timeouts_do_not_accumulate (n : Nat)
    (state : ResourceState) :
    (run (List.replicate n .headerTimeout) state).live = state.live := by
  exact run_restores_live _ _

end PettaClaw.ProviderResourceLifetime

#print axioms PettaClaw.ProviderResourceLifetime.request_restores_live
#print axioms PettaClaw.ProviderResourceLifetime.every_outcome_restores_live
#print axioms PettaClaw.ProviderResourceLifetime.run_restores_live
#print axioms PettaClaw.ProviderResourceLifetime.run_peak_le
#print axioms PettaClaw.ProviderResourceLifetime.run_preserves_below_limit
#print axioms PettaClaw.ProviderResourceLifetime.unowned_timeouts_reach_limit
#print axioms PettaClaw.ProviderResourceLifetime.finalized_timeouts_do_not_accumulate
