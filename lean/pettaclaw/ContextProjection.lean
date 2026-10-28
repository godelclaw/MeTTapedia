/-!
# ContextProjection — typed views over an append-only event record

The agent's event ledger is authoritative.  Context, memory indexes, and graph
views are replaceable materializations of a finite causal prefix.  This file
formalizes the small interface between those roles:

* a source observation is known, absent, or temporarily unavailable;
* unavailability preserves the last known projection, while absence clears it;
* multiple revisions of one semantic event project to the latest revision;
* events beyond a fixed frontier cannot affect that frontier's projection;
* replaying deltas composes; and
* refreshing a materialized view cannot change the ledger or effects.

The model deliberately does not prescribe retrieval, ranking, summarization,
an ontology, or an action policy.  Those remain replaceable processes.
-/

namespace ContextProjection

/-! ## Typed source availability -/

inductive Observation (α : Type)
  | absent
  | unavailable
  | known (value : α)
deriving Repr, DecidableEq

/-- Admit one source observation against its previous materialized value. -/
def admit {α : Type} (previous : Option α) : Observation α → Option α
  | .absent => none
  | .unavailable => previous
  | .known value => some value

theorem unavailable_preserves_last_known {α : Type} (previous : Option α) :
    admit previous (.unavailable : Observation α) = previous := by
  rfl

theorem absence_clears_projection {α : Type} (previous : Option α) :
    admit previous (.absent : Observation α) = none := by
  rfl

theorem known_replaces_projection {α : Type} (previous : Option α) (value : α) :
    admit previous (.known value) = some value := by
  rfl

def PreservesUnavailable {α : Type}
    (candidate : Option α → Observation α → Option α) : Prop :=
  ∀ previous, candidate previous .unavailable = previous

def ClearsAbsent {α : Type}
    (candidate : Option α → Observation α → Option α) : Prop :=
  ∀ previous, candidate previous .absent = none

def InstallsKnown {α : Type}
    (candidate : Option α → Observation α → Option α) : Prop :=
  ∀ previous value, candidate previous (.known value) = some value

/-- The three availability laws determine the admission operation completely;
there is no fourth status-dependent policy hidden in the projection layer. -/
theorem availability_laws_determine_admission {α : Type}
    (candidate : Option α → Observation α → Option α)
    (unavailable : PreservesUnavailable candidate)
    (absent : ClearsAbsent candidate)
    (known : InstallsKnown candidate) :
    candidate = admit := by
  funext previous observation
  cases observation with
  | absent => exact absent previous
  | unavailable => exact unavailable previous
  | known value => exact known previous value

/-! ## Semantic identity and latest-revision projection -/

structure Revision (Id Payload : Type) where
  id : Id
  payload : Payload
deriving Repr, DecidableEq

def updateLatest {Id Payload : Type} [DecidableEq Id] (selected : Id)
    (current : Option Payload) (revision : Revision Id Payload) :
    Option Payload :=
  if revision.id = selected then some revision.payload else current

/-- A functional materialization: every semantic id has at most one visible
payload, even though the ledger retains every revision. -/
def latest {Id Payload : Type} [DecidableEq Id] (selected : Id)
    (revisions : List (Revision Id Payload)) : Option Payload :=
  revisions.foldl (updateLatest selected) none

theorem newest_revision_wins {Id Payload : Type} [DecidableEq Id]
    (selected : Id) (revisions : List (Revision Id Payload))
    (payload : Payload) :
    latest selected (revisions ++ [⟨selected, payload⟩]) = some payload := by
  simp [latest, updateLatest, List.foldl_append]

theorem unrelated_revision_does_not_change_projection
    {Id Payload : Type} [DecidableEq Id]
    (selected other : Id) (different : other ≠ selected)
    (revisions : List (Revision Id Payload)) (payload : Payload) :
    latest selected (revisions ++ [⟨other, payload⟩]) =
      latest selected revisions := by
  simp [latest, updateLatest, List.foldl_append, different]

def atFrontier {Id Payload : Type} [DecidableEq Id] (selected : Id)
    (frontier : Nat) (ledger : List (Revision Id Payload)) : Option Payload :=
  latest selected (ledger.take frontier)

theorem take_append_before_boundary {α : Type} (ledgerPrefix future : List α)
    (frontier : Nat) (within : frontier ≤ ledgerPrefix.length) :
    (ledgerPrefix ++ future).take frontier = ledgerPrefix.take frontier := by
  induction ledgerPrefix generalizing frontier with
  | nil =>
      have zero : frontier = 0 := Nat.eq_zero_of_le_zero within
      subst frontier
      simp
  | cons head tail inductionHypothesis =>
      cases frontier with
      | zero => simp
      | succ remaining =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at within
          simp [inductionHypothesis remaining within]

/-- Once a controller's causal frontier is fixed, later ledger events cannot
appear in the context projected for that controller invocation. -/
theorem future_events_do_not_cross_frontier
    {Id Payload : Type} [DecidableEq Id]
    (selected : Id) (ledgerPrefix future : List (Revision Id Payload))
    (frontier : Nat) (within : frontier ≤ ledgerPrefix.length) :
    atFrontier selected frontier (ledgerPrefix ++ future) =
      atFrontier selected frontier ledgerPrefix := by
  simp [atFrontier,
    take_append_before_boundary ledgerPrefix future frontier within]

theorem one_identity_has_at_most_one_visible_payload
    {Id Payload : Type} [DecidableEq Id]
    (selected : Id) (frontier : Nat) (ledger : List (Revision Id Payload))
    (left right : Payload)
    (leftVisible : atFrontier selected frontier ledger = some left)
    (rightVisible : atFrontier selected frontier ledger = some right) :
    left = right := by
  rw [leftVisible] at rightVisible
  exact Option.some.inj rightVisible

/-! ## Delta replay for replaceable materialized views -/

inductive Delta (Id Payload : Type)
  | put (id : Id) (payload : Payload)
  | remove (id : Id)
deriving Repr, DecidableEq

abbrev View (Id Payload : Type) := Id → Option Payload

def applyDelta {Id Payload : Type} [DecidableEq Id]
    (view : View Id Payload) : Delta Id Payload → View Id Payload
  | .put id payload => fun selected =>
      if selected = id then some payload else view selected
  | .remove id => fun selected =>
      if selected = id then none else view selected

def replay {Id Payload : Type} [DecidableEq Id]
    (initial : View Id Payload) (deltas : List (Delta Id Payload)) :
    View Id Payload :=
  deltas.foldl applyDelta initial

theorem replay_append_composes {Id Payload : Type} [DecidableEq Id]
    (initial : View Id Payload) (left right : List (Delta Id Payload)) :
    replay initial (left ++ right) = replay (replay initial left) right := by
  simp [replay, List.foldl_append]

theorem replay_put_is_visible {Id Payload : Type} [DecidableEq Id]
    (initial : View Id Payload) (deltas : List (Delta Id Payload))
    (id : Id) (payload : Payload) :
    replay initial (deltas ++ [.put id payload]) id = some payload := by
  simp [replay, List.foldl_append, applyDelta]

theorem replay_remove_is_absent {Id Payload : Type} [DecidableEq Id]
    (initial : View Id Payload) (deltas : List (Delta Id Payload)) (id : Id) :
    replay initial (deltas ++ [.remove id]) id = none := by
  simp [replay, List.foldl_append, applyDelta]

/-! ## Views are non-authoritative -/

structure AgentState (Event Materialized Effect : Type) where
  ledger : List Event
  view : Materialized
  effects : List Effect
deriving Repr, DecidableEq

/-- Rebuilding Chroma, an AtomSpace, or a prompt bundle changes only the
replaceable materialized coordinate. -/
def refreshView {Event Materialized Effect : Type}
    (state : AgentState Event Materialized Effect) (next : Materialized) :
    AgentState Event Materialized Effect :=
  { state with view := next }

theorem refresh_preserves_authoritative_ledger
    {Event Materialized Effect : Type}
    (state : AgentState Event Materialized Effect) (next : Materialized) :
    (refreshView state next).ledger = state.ledger := by
  rfl

theorem refresh_cannot_emit_effect
    {Event Materialized Effect : Type}
    (state : AgentState Event Materialized Effect) (next : Materialized) :
    (refreshView state next).effects = state.effects := by
  rfl

/-! Context management remains autonomous policy, not kernel mechanism. -/

abbrev ContextPolicy (Event Context : Type) := List Event → Context

def selectContext {Event Context : Type}
    (policy : ContextPolicy Event Context) (ledger : List Event) : Context :=
  policy ledger

/-- Any context manager is hostable: recency windows, structured compaction,
graph retrieval, and learned selectors all inhabit the same open policy type. -/
theorem every_context_policy_is_expressible {Event Context : Type}
    (policy : ContextPolicy Event Context) (ledger : List Event) :
    selectContext policy ledger = policy ledger := by
  rfl

/-- Preparing context returns the state unchanged.  Selection may explain
evidence to a controller, but is not itself an effect transition. -/
def prepareContext {Event Materialized Effect Context : Type}
    (policy : ContextPolicy Event Context)
    (state : AgentState Event Materialized Effect) :
    Context × AgentState Event Materialized Effect :=
  (selectContext policy state.ledger, state)

theorem context_preparation_preserves_state
    {Event Materialized Effect Context : Type}
    (policy : ContextPolicy Event Context)
    (state : AgentState Event Materialized Effect) :
    (prepareContext policy state).2 = state := by
  rfl

def appendEvent {Event Materialized Effect : Type}
    (state : AgentState Event Materialized Effect) (event : Event) :
    AgentState Event Materialized Effect :=
  { state with ledger := state.ledger ++ [event] }

theorem event_append_is_monotone
    {Event Materialized Effect : Type}
    (state : AgentState Event Materialized Effect) (event : Event) :
    state.ledger.IsPrefix (appendEvent state event).ledger := by
  simp [appendEvent, List.IsPrefix]

end ContextProjection

/-! ## Axiom audit -/

#print axioms ContextProjection.availability_laws_determine_admission
#print axioms ContextProjection.newest_revision_wins
#print axioms ContextProjection.future_events_do_not_cross_frontier
#print axioms ContextProjection.one_identity_has_at_most_one_visible_payload
#print axioms ContextProjection.replay_append_composes
#print axioms ContextProjection.refresh_preserves_authoritative_ledger
#print axioms ContextProjection.refresh_cannot_emit_effect
#print axioms ContextProjection.every_context_policy_is_expressible
#print axioms ContextProjection.context_preparation_preserves_state
