import Mathlib

/-!
# LilaModeIntegration — conservative operational modes

This file models the small runtime boundary used by Lila's selectable modes.
Modes alter scheduling, request preparation, and reasoning effort.  They do not
own identity, durable memory, or the present working state.

The default policy is the historical one: `agent` mode, medium reasoning, no
Iter transformation, and saturating renewal.  The Iter variants add autonomous
renewal only at a completed wait boundary.  An explicit rest keeps its selected
duration.  Provider failure changes pacing, not identity, memory, or energy.
-/

namespace PettaClaw.LilaModeIntegration

inductive Mode where
  | agent
  | iter
  | coding
  | iterCoding
deriving Repr, DecidableEq

inductive Reasoning where
  | medium
  | high
deriving Repr, DecidableEq

structure ModePolicy where
  autonomous : Bool
  transforms : Bool
  reasoning : Reasoning
deriving Repr, DecidableEq

def policy : Mode → ModePolicy
  | .agent => ⟨false, false, .medium⟩
  | .iter => ⟨true, true, .medium⟩
  | .coding => ⟨false, false, .high⟩
  | .iterCoding => ⟨true, true, .high⟩

theorem agent_is_legacy_policy :
    policy .agent = ⟨false, false, .medium⟩ := rfl

theorem coding_changes_effort_not_request_shape :
    (policy .coding).transforms = false ∧
      (policy .coding).reasoning = .high := by
  decide

theorem iter_modes_transform_and_renew (mode : Mode)
    (h : mode = .iter ∨ mode = .iterCoding) :
    (policy mode).transforms = true ∧ (policy mode).autonomous = true := by
  rcases h with rfl | rfl <;> decide

inductive Fuel where
  | saturate
  | accumulate
  | carry
  | decay
deriving Repr, DecidableEq

def carryMultiple : Nat := 4

def refuel : Fuel → Nat → Nat → Nat
  | .saturate, held, grant => max held grant
  | .accumulate, held, grant => held + grant
  | .carry, held, grant => min (carryMultiple * grant) (held + grant)
  | .decay, held, grant => held * 3 / 4 + grant

theorem default_fuel_is_exactly_legacy_saturation (held grant : Nat) :
    refuel .saturate held grant = max held grant := rfl

theorem every_fuel_grants_at_least_the_offer
    (fuel : Fuel) (held grant : Nat) :
    grant ≤ refuel fuel held grant := by
  cases fuel
  · exact Nat.le_max_right _ _
  · exact Nat.le_add_left _ _
  · exact Nat.le_min.mpr ⟨by
      simp [carryMultiple]
      exact Nat.le_mul_of_pos_left grant (by decide), by omega⟩
  · exact Nat.le_add_left _ _

structure State (Identity Memory Working : Type*) where
  identity : Identity
  memory : Memory
  working : Working
  mode : Mode
  fuel : Fuel
  loops : Nat
  sleepInterval : Nat
  explicitRest : Bool
deriving Repr, DecidableEq

def selectMode (next : Mode) (state : State Identity Memory Working) :
    State Identity Memory Working :=
  { state with mode := next }

theorem mode_selection_preserves_person
    (next : Mode) (state : State Identity Memory Working) :
    let selected := selectMode next state
    selected.identity = state.identity ∧
      selected.memory = state.memory ∧
      selected.working = state.working ∧
      selected.fuel = state.fuel ∧
      selected.loops = state.loops ∧
      selected.sleepInterval = state.sleepInterval := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The actual wait law: Iter uses its cadence only after exhausting the burst;
an explicit rest, and all non-autonomous modes, keep the selected duration. -/
def waitSeconds (iterIdle : Nat) (state : State Identity Memory Working) : Nat :=
  if (policy state.mode).autonomous && state.loops == 0 && !state.explicitRest
  then iterIdle
  else state.sleepInterval

theorem agent_keeps_legacy_wait
    (iterIdle : Nat) (state : State Identity Memory Working)
    (h : state.mode = .agent) :
    waitSeconds iterIdle state = state.sleepInterval := by
  simp [waitSeconds, h, policy]

theorem coding_keeps_legacy_wait
    (iterIdle : Nat) (state : State Identity Memory Working)
    (h : state.mode = .coding) :
    waitSeconds iterIdle state = state.sleepInterval := by
  simp [waitSeconds, h, policy]

theorem iter_uses_idle_cadence_after_spending
    (iterIdle : Nat) (state : State Identity Memory Working)
    (hmode : state.mode = .iter ∨ state.mode = .iterCoding)
    (hspent : state.loops = 0) (hrest : state.explicitRest = false) :
    waitSeconds iterIdle state = iterIdle := by
  rcases hmode with hmode | hmode <;>
    simp [waitSeconds, hmode, hspent, hrest, policy]

theorem explicit_rest_duration_wins
    (iterIdle : Nat) (state : State Identity Memory Working)
    (hrest : state.explicitRest = true) :
    waitSeconds iterIdle state = state.sleepInterval := by
  simp [waitSeconds, hrest]

/-- Renewal is a wait-boundary transition.  It is total: every branch returns
a state, so selecting a non-autonomous mode cannot terminate the loop. -/
def renew (grant : Nat) (state : State Identity Memory Working) :
    State Identity Memory Working :=
  if (policy state.mode).autonomous && state.loops == 0
  then { state with loops := refuel state.fuel state.loops grant }
  else state

theorem agent_does_not_self_renew
    (grant : Nat) (state : State Identity Memory Working)
    (h : state.mode = .agent) : renew grant state = state := by
  simp [renew, h, policy]

theorem coding_does_not_self_renew
    (grant : Nat) (state : State Identity Memory Working)
    (h : state.mode = .coding) : renew grant state = state := by
  simp [renew, h, policy]

theorem iter_saturate_renews_to_grant
    (grant : Nat) (state : State Identity Memory Working)
    (hmode : state.mode = .iter ∨ state.mode = .iterCoding)
    (hfuel : state.fuel = .saturate) (hspent : state.loops = 0) :
    (renew grant state).loops = grant := by
  rcases hmode with hmode | hmode <;>
    simp [renew, hmode, hfuel, hspent, policy, refuel]

theorem renewal_preserves_person
    (grant : Nat) (state : State Identity Memory Working) :
    let next := renew grant state
    next.identity = state.identity ∧
      next.memory = state.memory ∧ next.working = state.working := by
  simp only [renew]
  split <;> exact ⟨rfl, rfl, rfl⟩

structure Activity where
  mode : Mode
  fuel : Fuel
  loops : Nat
  sleepInterval : Nat
deriving Repr, DecidableEq

/-- Observation deliberately omits identity, memory, and working content. -/
def observe (state : State Identity Memory Working) : Activity :=
  ⟨state.mode, state.fuel, state.loops, state.sleepInterval⟩

theorem observation_is_pure
    (state : State Identity Memory Working) :
    state = state ∧
      (observe state).mode = state.mode ∧
      (observe state).loops = state.loops := by
  exact ⟨rfl, rfl, rfl⟩

/-- Provider failure is pacing, never a life-authority transition. -/
def providerFailure (retryAfter : Nat)
    (state : State Identity Memory Working) : State Identity Memory Working :=
  { state with sleepInterval := max 1 retryAfter }

theorem provider_failure_preserves_person_and_energy
    (retryAfter : Nat) (state : State Identity Memory Working) :
    let failed := providerFailure retryAfter state
    failed.identity = state.identity ∧
      failed.memory = state.memory ∧
      failed.working = state.working ∧ failed.loops = state.loops := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem provider_failure_cannot_disable_iter_renewal
    (retryAfter grant : Nat) (state : State Identity Memory Working)
    (hmode : state.mode = .iter ∨ state.mode = .iterCoding)
    (hfuel : state.fuel = .saturate) (hspent : state.loops = 0) :
    (renew grant (providerFailure retryAfter state)).loops = grant := by
  rcases hmode with hmode | hmode <;>
    simp [providerFailure, renew, hmode, hfuel, hspent, policy, refuel]

end PettaClaw.LilaModeIntegration

#print axioms PettaClaw.LilaModeIntegration.mode_selection_preserves_person
#print axioms PettaClaw.LilaModeIntegration.agent_keeps_legacy_wait
#print axioms PettaClaw.LilaModeIntegration.iter_uses_idle_cadence_after_spending
#print axioms PettaClaw.LilaModeIntegration.explicit_rest_duration_wins
#print axioms PettaClaw.LilaModeIntegration.agent_does_not_self_renew
#print axioms PettaClaw.LilaModeIntegration.iter_saturate_renews_to_grant
#print axioms PettaClaw.LilaModeIntegration.renewal_preserves_person
#print axioms PettaClaw.LilaModeIntegration.observation_is_pure
#print axioms PettaClaw.LilaModeIntegration.provider_failure_preserves_person_and_energy
#print axioms PettaClaw.LilaModeIntegration.provider_failure_cannot_disable_iter_renewal
