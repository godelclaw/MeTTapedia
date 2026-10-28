import ContextProjection

/-!
# CapabilityProjection — revision-bound project facts for context policy

An agent should not reconstruct a local subsystem from general knowledge when
the running artifact can state its capabilities directly.  This module models
the narrow context view used for that purpose.  A snapshot records an artifact
revision and its witnessed inventory; projection may select implemented
entries, but it cannot mint new ones or perform an effect.
-/

namespace CapabilityProjection

inductive Status
  | implemented
  | planned
deriving Repr, DecidableEq

structure Capability where
  name : String
  status : Status
  description : String
deriving Repr, DecidableEq

structure Snapshot where
  artifact : String
  revision : String
  inventory : List Capability
deriving Repr, DecidableEq

structure View where
  artifact : String
  revision : String
  implemented : List Capability
deriving Repr, DecidableEq

/-- Selection is deliberately boring: filter the witnessed inventory. -/
def project (snapshot : Snapshot) : View :=
  { artifact := snapshot.artifact
    revision := snapshot.revision
    implemented := snapshot.inventory.filter
      (fun capability => capability.status == .implemented) }

theorem projection_is_revision_bound (snapshot : Snapshot) :
    (project snapshot).revision = snapshot.revision := by
  rfl

/-- Every displayed capability came from this exact artifact snapshot. -/
theorem projected_capability_is_witnessed (snapshot : Snapshot)
    (capability : Capability)
    (visible : capability ∈ (project snapshot).implemented) :
    capability ∈ snapshot.inventory ∧ capability.status = .implemented := by
  simpa [project] using visible

/-- A temporarily unavailable probe keeps the previous capability view. -/
theorem unavailable_preserves_capability_view (previous : Option View) :
    ContextProjection.admit previous
      (.unavailable : ContextProjection.Observation View) = previous := by
  exact ContextProjection.unavailable_preserves_last_known previous

/-- Refreshing a capability view cannot alter the event record. -/
theorem refresh_preserves_ledger
    {Event Effect : Type}
    (state : ContextProjection.AgentState Event View Effect)
    (snapshot : Snapshot) :
    (ContextProjection.refreshView state (project snapshot)).ledger =
      state.ledger := by
  exact ContextProjection.refresh_preserves_authoritative_ledger
    state (project snapshot)

/-- Capability discovery is context, never effect authority. -/
theorem refresh_cannot_emit_effect
    {Event Effect : Type}
    (state : ContextProjection.AgentState Event View Effect)
    (snapshot : Snapshot) :
    (ContextProjection.refreshView state (project snapshot)).effects =
      state.effects := by
  exact ContextProjection.refresh_cannot_emit_effect state (project snapshot)

end CapabilityProjection

#print axioms CapabilityProjection.projection_is_revision_bound
#print axioms CapabilityProjection.projected_capability_is_witnessed
#print axioms CapabilityProjection.unavailable_preserves_capability_view
#print axioms CapabilityProjection.refresh_preserves_ledger
#print axioms CapabilityProjection.refresh_cannot_emit_effect
