import Mettapedia.Machines.NativeStoreScopes

/-!
# Native view resources and creation cancellation

These are executable protocol obligations. The implementation's kernel
principal and shared monotonic clock supply the identity and time inputs.
Byte usage includes pointer vectors, patterns, copied requests and row bytes;
it is a view-buffer budget, not a bound on total process RSS.

Cancellation fences cannot be evicted before their deadline. If there is no
room for one, abandonment reports a refusal, even if it released an existing
capture. Leases remain the fallback when a caller cannot reach the service.
-/

namespace Mettapedia.Machines.NativeStoreResources

structure Creation where
  boot : Nat
  principal : Nat
  source : Nat
  request : Nat
  expiresAt : Nat
deriving DecidableEq, Repr

structure Creations where
  active : List Creation := []
  cancelled : List Creation := []
deriving DecidableEq, Repr

def mayCreate (now boot : Nat) (identity : Creation) (state : Creations) : Bool :=
  identity.boot == boot && now < identity.expiresAt && !state.cancelled.contains identity

inductive CancelAnswer | closed | forbidden | capacity
deriving DecidableEq, Repr

def abandon (now principal : Nat) (identity : Creation) (room : Bool)
    (state : Creations) : CancelAnswer × Creations :=
  if principal ≠ identity.principal then (.forbidden, state)
  else
    let released := { state with active := state.active.filter (· != identity) }
    if identity.expiresAt ≤ now then (.closed, released)
    else if state.cancelled.contains identity then (.closed, released)
    else if room then (.closed, { released with cancelled := identity :: state.cancelled })
    else (.capacity, released)

theorem another_principal_cannot_abandon (now principal : Nat) (identity : Creation)
    (room : Bool) (state : Creations) (foreign : principal ≠ identity.principal) :
    abandon now principal identity room state = (.forbidden, state) := by
  simp [abandon, foreign]

/-- A wire request carries no principal field. The kernel supplies it. -/
def abandonPacket (now principal : Nat) (identity : Creation) (room : Bool)
    (state : Creations) : CancelAnswer × Creations :=
  abandon now principal { identity with principal := principal } room state

theorem packet_cannot_release_foreign_capture (now principal : Nat) (identity target : Creation)
    (room : Bool) (state : Creations) (foreign : target.principal ≠ principal)
    (present : target ∈ state.active) :
    target ∈ (abandonPacket now principal identity room state).2.active := by
  have different : target ≠ { identity with principal := principal } := by
    intro equal
    exact foreign (congrArg Creation.principal equal)
  simp only [abandonPacket, abandon]
  split_ifs <;> simp_all

theorem closed_creation_stays_refused (now later boot principal : Nat) (identity : Creation)
    (room : Bool) (before after : Creations)
    (closed : abandon now principal identity room before = (.closed, after))
    (monotone : now ≤ later) : mayCreate later boot identity after = false := by
  unfold abandon at closed
  split at closed
  · cases closed
  · split at closed
    · simp_all [mayCreate]
      omega
    · split at closed
      · cases closed
        simp_all [mayCreate]
      · split at closed
        · cases closed
          simp_all [mayCreate]
        · cases closed

theorem restart_refuses_old_creation (now boot : Nat) (identity : Creation)
    (state : Creations) (fresh : identity.boot ≠ boot) :
    mayCreate now boot identity state = false := by
  simp [mayCreate, fresh]

theorem expiring_only_old_fences_is_safe (now : Nat) (identity : Creation)
    (state : Creations) (cancelled : identity ∈ state.cancelled)
    (still_valid : now < identity.expiresAt) :
    identity ∈ state.cancelled.filter (fun entry => now < entry.expiresAt) := by
  simp [cancelled, still_valid]

inductive ViewKind | snapshot | capturing | observation | waiting
deriving DecidableEq, Repr

structure View where
  principal : Nat
  bytes : Nat
  kind : ViewKind
deriving DecidableEq, Repr

structure Usage where
  views : Nat := 0
  bytes : Nat := 0
  waits : Nat := 0
deriving DecidableEq, Repr

def Usage.add (left right : Usage) : Usage :=
  ⟨left.views + right.views, left.bytes + right.bytes, left.waits + right.waits⟩

def View.usage (principal : Nat) (view : View) : Usage :=
  if principal = view.principal then ⟨1, view.bytes, if view.kind = .waiting then 1 else 0⟩
  else {}

def usage (principal : Nat) : List View → Usage
  | [] => {}
  | view :: rest => Usage.add (view.usage principal) (usage principal rest)

abbrev fits (budget use : Usage) : Prop :=
  use.views ≤ budget.views ∧ use.bytes ≤ budget.bytes ∧ use.waits ≤ budget.waits

theorem foreign_usage_unchanged (principal : Nat) (view : View) (rest : List View)
    (foreign : principal ≠ view.principal) :
    usage principal (view :: rest) = usage principal rest := by
  simp [usage, View.usage, foreign, Usage.add]

/-- Transfer changes ownership stage, not the account or byte charge. -/
theorem waiting_preserves_view_and_byte_charge (principal : Nat) (view : View) :
    (View.usage principal { view with kind := .waiting }).views = (view.usage principal).views ∧
    (View.usage principal { view with kind := .waiting }).bytes = (view.usage principal).bytes := by
  by_cases owner : principal = view.principal <;> simp [View.usage, owner]

def room (limit used requested : Nat) : Bool :=
  requested ≤ limit && used ≤ limit - requested

theorem room_iff (limit used requested : Nat) :
    room limit used requested = true ↔ used + requested ≤ limit := by
  simp [room]
  omega

def admit (budget : Usage) (principal : Nat) (view : View) (views : List View) : Bool :=
  let current := usage principal views
  let requested := view.usage principal
  room budget.views current.views requested.views &&
    room budget.bytes current.bytes requested.bytes &&
    room budget.waits current.waits requested.waits

theorem admitted_allocation_preserves_budget (budget : Usage) (principal : Nat)
    (view : View) (views : List View) (accepted : admit budget principal view views = true) :
    fits budget (usage principal (view :: views)) := by
  simpa [admit, room_iff, usage, Usage.add, fits, Nat.add_comm, and_assoc] using accepted

/-- The limit is on owned resources. It does not remove stored facts or
restrict which query can be retried after resources become available. -/
theorem pointer_vectors_are_part_of_the_charge (principal payload slots width : Nat) :
    (View.usage principal ⟨principal, payload + slots * width, .snapshot⟩).bytes =
      payload + slots * width := by simp [View.usage]

end Mettapedia.Machines.NativeStoreResources
