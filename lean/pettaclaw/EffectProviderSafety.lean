import Mathlib

/-!
# Effect-provider selection and write-ahead receipts

The weak process kernel is intentionally unable to decide which external
effect provider a surrounding process should use.  This file isolates two
obligations of that replaceable surround.

First, a configured qualification state must not fall through to live effects
when its provider selector is absent or malformed.  Second, consuming an
effect capability must be durable before the physical effect: otherwise a
post-effect exception can leave the physical world changed while the persisted
trace and receipt remain unchanged.

The repaired model does not pretend that a crash after a physical effect can
always reveal whether that effect occurred.  It proves the weaker property
which is actually available: an uncertain effect cannot be replayed using the
same capability.
-/

namespace PettaClaw.EffectProviderSafety

inductive Provider where
  | live
  | shadow
deriving Repr, DecidableEq

inductive ProviderDecision where
  | use (provider : Provider)
  | reject
deriving Repr, DecidableEq

/-- The deployed selector: every spelling except one silently chooses live
effects. -/
def deployedSelect (selector : String) : Provider :=
  if selector = "tmux-shadow" then .shadow else .live

/-- A shadow-state witness changes the default: malformed configuration is
rejected rather than interpreted as permission to use the live provider. -/
def guardedSelect (selector : String) (shadowStateConfigured : Bool) :
    ProviderDecision :=
  if selector = "tmux-shadow" then
    .use .shadow
  else if shadowStateConfigured then
    .reject
  else
    .use .live

theorem deployed_malformed_selector_reaches_live
    (selector : String) (malformed : selector ≠ "tmux-shadow") :
    deployedSelect selector = .live := by
  simp [deployedSelect, malformed]

theorem guarded_configured_shadow_rejects_malformed_selector
    (selector : String) (malformed : selector ≠ "tmux-shadow") :
    guardedSelect selector true = .reject := by
  simp [guardedSelect, malformed]

theorem guarded_valid_shadow_selects_shadow :
    guardedSelect "tmux-shadow" true = .use .shadow := by
  rfl

inductive ReceiptStatus where
  | available
  | reserved
  | spent
deriving Repr, DecidableEq

structure DurableState where
  traceCount : Nat
  effectCount : Nat
  receipt : ReceiptStatus
deriving Repr, DecidableEq

structure ProviderSystem where
  physicalEffects : Nat
  durable : DurableState
deriving Repr, DecidableEq

def initial : ProviderSystem :=
  ⟨0, ⟨0, 0, .available⟩⟩

/-- The deployed post-send timeout: the external effect has occurred, but the
exception aborts persistence and exposes the old receipt again. -/
def deployedPostSendTimeout (system : ProviderSystem) : ProviderSystem :=
  { system with physicalEffects := system.physicalEffects + 1 }

/-- At-most-once safety permits an uncertain outcome, but never permits a
receipt to remain available after more physical effects occurred than were
durably finalized. -/
def AtMostOnceSafe (system : ProviderSystem) : Prop :=
  system.durable.effectCount < system.physicalEffects →
    system.durable.receipt ≠ .available

theorem deployed_timeout_is_unrecorded :
    (deployedPostSendTimeout initial).durable = initial.durable ∧
    (deployedPostSendTimeout initial).physicalEffects = 1 := by
  decide

theorem deployed_timeout_violates_at_most_once :
    ¬ AtMostOnceSafe (deployedPostSendTimeout initial) := by
  simp [AtMostOnceSafe, deployedPostSendTimeout, initial]

/-- Durably reserve and thereby consume the capability before crossing the
physical effect boundary. -/
def reserve (system : ProviderSystem) : ProviderSystem :=
  { system with durable := { system.durable with receipt := .reserved } }

def performPhysicalEffect (system : ProviderSystem) : ProviderSystem :=
  { system with physicalEffects := system.physicalEffects + 1 }

def finalizeEffect (system : ProviderSystem) : ProviderSystem :=
  { system with durable :=
      { traceCount := system.durable.traceCount + 1
        effectCount := system.durable.effectCount + 1
        receipt := .spent } }

inductive CrashPoint where
  | beforeReserve
  | afterReserve
  | afterPhysicalEffect
  | afterFinalize
deriving Repr, DecidableEq

/-- Every durable prefix of the write-ahead protocol, including the uncertain
post-effect prefix. -/
def repairedAt : CrashPoint → ProviderSystem
  | .beforeReserve => initial
  | .afterReserve => reserve initial
  | .afterPhysicalEffect => performPhysicalEffect (reserve initial)
  | .afterFinalize => finalizeEffect (performPhysicalEffect (reserve initial))

theorem write_ahead_protocol_is_at_most_once
    (point : CrashPoint) : AtMostOnceSafe (repairedAt point) := by
  cases point <;>
    simp [AtMostOnceSafe, repairedAt, initial, reserve,
      performPhysicalEffect, finalizeEffect]

theorem post_effect_crash_is_durably_uncertain :
    let system := repairedAt .afterPhysicalEffect
    system.physicalEffects = 1 ∧
      system.durable.effectCount = 0 ∧
      system.durable.receipt = .reserved := by
  decide

theorem completed_effect_is_witnessed_and_spent :
    let system := repairedAt .afterFinalize
    system.physicalEffects = system.durable.effectCount ∧
      system.durable.traceCount = 1 ∧
      system.durable.receipt = .spent := by
  decide

/-- The general information-boundary theorem behind the terminal-marker
counterexample: no deterministic policy on a projection can distinguish two
histories which the projection identifies but the required action separates. -/
theorem no_policy_on_a_conflating_projection
    {History Observation Action : Type}
    (projection : History → Observation) (required : History → Action)
    (first second : History)
    (collision : projection first = projection second)
    (different : required first ≠ required second) :
    ¬ ∃ choose : Observation → Action,
        choose (projection first) = required first ∧
          choose (projection second) = required second := by
  rintro ⟨choose, firstCorrect, secondCorrect⟩
  apply different
  calc
    required first = choose (projection first) := firstCorrect.symm
    _ = choose (projection second) := congrArg choose collision
    _ = required second := secondCorrect

#print axioms PettaClaw.EffectProviderSafety.deployed_malformed_selector_reaches_live
#print axioms PettaClaw.EffectProviderSafety.guarded_configured_shadow_rejects_malformed_selector
#print axioms PettaClaw.EffectProviderSafety.deployed_timeout_is_unrecorded
#print axioms PettaClaw.EffectProviderSafety.deployed_timeout_violates_at_most_once
#print axioms PettaClaw.EffectProviderSafety.write_ahead_protocol_is_at_most_once
#print axioms PettaClaw.EffectProviderSafety.no_policy_on_a_conflating_projection

end PettaClaw.EffectProviderSafety
