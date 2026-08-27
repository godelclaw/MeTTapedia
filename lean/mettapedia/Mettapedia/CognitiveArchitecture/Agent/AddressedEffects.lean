import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Addressed external effects

An external messaging effect has two independent identities: its destination
and the platform identifier returned after delivery.  Hiding either identity
behind mutable "current chat" state or a partial local ledger makes basic
operations non-robust even when the policy choosing the operation is ideal.

This file isolates that architectural fact from any particular messaging
provider.  A recent-message ledger remains useful as a convenience index, but
it is not a complete deletion interface unless it contains every platform
message still in scope.  Likewise, a success claim is admitted only by a
success receipt; proposing an effect is not such a receipt.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Agent.AddressedEffects

universe uChat uMessage uMessageId uPayload

/-- An explicitly addressed message.  The destination is part of the effect,
not ambient mutable state. -/
structure Addressed (Chat : Type uChat) (Payload : Type uPayload) where
  destination : Chat
  payload : Payload

/-- Legacy resolution of an unaddressed payload through mutable current-chat
state. -/
def resolveAmbient {Chat : Type uChat} {Payload : Type uPayload}
    (current : Chat) (payload : Payload) : Addressed Chat Payload :=
  ⟨current, payload⟩

/-- Explicit addressing is stable under arbitrary changes to ambient state. -/
def resolveExplicit {Chat : Type uChat} {Payload : Type uPayload}
    (destination : Chat) (payload : Payload) : Addressed Chat Payload :=
  ⟨destination, payload⟩

/-- Resolution used by a deployment with an optional primary route.  A
configured primary is an explicit constant route; only an unconfigured
deployment falls back to ambient state. -/
def resolveConfigured {Chat : Type uChat} {Payload : Type uPayload}
    (primary : Option Chat) (ambient : Chat) (payload : Payload) :
    Addressed Chat Payload :=
  match primary with
  | some destination => resolveExplicit destination payload
  | none => resolveAmbient ambient payload

@[simp] theorem configured_primary_ignores_ambient
    {Chat : Type uChat} {Payload : Type uPayload}
    (primary ambient : Chat) (payload : Payload) :
    (resolveConfigured (some primary) ambient payload).destination =
      primary := by
  rfl

/-- With a configured primary, changing the observed chat cannot change the
resolved effect at all, not merely its projected destination. -/
theorem configured_primary_stable
    {Chat : Type uChat} {Payload : Type uPayload}
    (primary firstAmbient secondAmbient : Chat) (payload : Payload) :
    resolveConfigured (some primary) firstAmbient payload =
      resolveConfigured (some primary) secondAmbient payload := by
  rfl

@[simp] theorem unconfigured_route_is_ambient
    {Chat : Type uChat} {Payload : Type uPayload}
    (ambient : Chat) (payload : Payload) :
    (resolveConfigured none ambient payload).destination = ambient := by
  rfl

/-- If the ambient chat differs from the intended recipient, an unaddressed
send is necessarily misrouted.  Model intelligence cannot repair information
that is absent from the effect. -/
theorem ambient_route_misroutes
    {Chat : Type uChat} {Payload : Type uPayload}
    (intended current : Chat) (payload : Payload)
    (different : current ≠ intended) :
    (resolveAmbient current payload).destination ≠ intended := by
  simpa [resolveAmbient] using different

/-- An explicitly addressed send reaches its named destination regardless of
the ambient chat. -/
@[simp] theorem explicit_route_stable
    {Chat : Type uChat} {Payload : Type uPayload}
    (destination _ambient : Chat) (payload : Payload) :
    (resolveExplicit destination payload).destination = destination := by
  rfl

/-- The deletion range of a ledger-only interface. -/
def LedgerAddressable {MessageId : Type uMessageId} [DecidableEq MessageId]
    (ledger : Finset MessageId) (message : MessageId) : Prop :=
  message ∈ ledger

/-- A ledger-only operation cannot address an outbound message whose platform
identifier was never captured. -/
theorem ledger_only_cannot_delete_uncaptured
    {MessageId : Type uMessageId} [DecidableEq MessageId]
    (ledger : Finset MessageId) (message : MessageId)
    (uncaptured : message ∉ ledger) :
    ¬ LedgerAddressable ledger message := by
  exact uncaptured

/-- Ledger deletion is complete for a platform scope exactly when every
in-scope platform identifier occurs in the ledger. -/
theorem ledger_deletion_complete_iff_subset
    {MessageId : Type uMessageId} [DecidableEq MessageId]
    (platformScope ledger : Finset MessageId) :
    (∀ message, message ∈ platformScope → LedgerAddressable ledger message) ↔
      platformScope ⊆ ledger := by
  rfl

/-- A complete deployment may combine the agent's receipt-backed ledger with
an independently authorized exact-address set.  This preserves the agent's
least authority while allowing an operator to name a legacy platform id. -/
def AddressableWithAuthority
    {MessageId : Type uMessageId} [DecidableEq MessageId]
    (ledger authorized : Finset MessageId) (message : MessageId) : Prop :=
  message ∈ ledger ∪ authorized

theorem receipt_or_authority_complete_iff_subset_union
    {MessageId : Type uMessageId} [DecidableEq MessageId]
    (platformScope ledger authorized : Finset MessageId) :
    (∀ message, message ∈ platformScope →
      AddressableWithAuthority ledger authorized message) ↔
      platformScope ⊆ ledger ∪ authorized := by
  rfl

/-- Concrete witness that platform deletability does not imply ledger
addressability. -/
theorem uncaptured_deletion_counterexample
    {MessageId : Type uMessageId} [DecidableEq MessageId]
    (message : MessageId) :
    ∃ platformScope ledger : Finset MessageId,
      message ∈ platformScope ∧ ¬ LedgerAddressable ledger message := by
  exact ⟨{message}, ∅, by simp, by simp [LedgerAddressable]⟩

/-- A coarse capacity model: `arrivals * turns` messages enter while at most
`capacity * turns` can be retired. -/
def CompleteCleanupPossible (arrivals capacity turns : Nat) : Prop :=
  arrivals * turns ≤ capacity * turns

/-- If arrivals per turn exceed cleanup capacity for a nonempty interval,
complete cleanup is impossible.  With an external deletion deadline, some
message can therefore age out unless another exact-addressed cleanup path is
available. -/
theorem sustained_overload_prevents_complete_cleanup
    {arrivals capacity turns : Nat}
    (overloaded : capacity < arrivals) (nonempty : 0 < turns) :
    ¬ CompleteCleanupPossible arrivals capacity turns := by
  unfold CompleteCleanupPossible
  exact not_le_of_gt (Nat.mul_lt_mul_of_pos_right overloaded nonempty)

inductive Outcome where
  | succeeded
  | failed
deriving DecidableEq, Repr

/-- Provider evidence returned after attempting an external effect. -/
structure Receipt (MessageId : Type uMessageId) where
  messageId : Option MessageId
  outcome : Outcome

/-- The evidence required for an affirmative completion claim. -/
def WitnessesSuccess {MessageId : Type uMessageId}
    (receipt : Option (Receipt MessageId)) : Prop :=
  ∃ observed, receipt = some observed ∧ observed.outcome = .succeeded

/-- No receipt cannot witness success. -/
theorem proposal_without_receipt_cannot_witness_success
    {MessageId : Type uMessageId} :
    ¬ WitnessesSuccess (none : Option (Receipt MessageId)) := by
  simp [WitnessesSuccess]

/-- A returned failure receipt cannot witness success. -/
theorem failure_receipt_cannot_witness_success
    {MessageId : Type uMessageId} (messageId : Option MessageId) :
    ¬ WitnessesSuccess (some ⟨messageId, .failed⟩) := by
  simp [WitnessesSuccess]

/-- A success receipt is sufficient evidence for a completion claim. -/
theorem success_receipt_witnesses_success
    {MessageId : Type uMessageId} (messageId : Option MessageId) :
    WitnessesSuccess (some ⟨messageId, .succeeded⟩) := by
  exact ⟨⟨messageId, .succeeded⟩, rfl, rfl⟩

end Mettapedia.CognitiveArchitecture.Agent.AddressedEffects

#print axioms Mettapedia.CognitiveArchitecture.Agent.AddressedEffects.ambient_route_misroutes
#print axioms Mettapedia.CognitiveArchitecture.Agent.AddressedEffects.configured_primary_ignores_ambient
#print axioms Mettapedia.CognitiveArchitecture.Agent.AddressedEffects.configured_primary_stable
#print axioms Mettapedia.CognitiveArchitecture.Agent.AddressedEffects.unconfigured_route_is_ambient
#print axioms Mettapedia.CognitiveArchitecture.Agent.AddressedEffects.ledger_only_cannot_delete_uncaptured
#print axioms Mettapedia.CognitiveArchitecture.Agent.AddressedEffects.ledger_deletion_complete_iff_subset
#print axioms Mettapedia.CognitiveArchitecture.Agent.AddressedEffects.receipt_or_authority_complete_iff_subset_union
#print axioms Mettapedia.CognitiveArchitecture.Agent.AddressedEffects.uncaptured_deletion_counterexample
#print axioms Mettapedia.CognitiveArchitecture.Agent.AddressedEffects.sustained_overload_prevents_complete_cleanup
#print axioms Mettapedia.CognitiveArchitecture.Agent.AddressedEffects.proposal_without_receipt_cannot_witness_success
#print axioms Mettapedia.CognitiveArchitecture.Agent.AddressedEffects.failure_receipt_cannot_witness_success
#print axioms Mettapedia.CognitiveArchitecture.Agent.AddressedEffects.success_receipt_witnesses_success
