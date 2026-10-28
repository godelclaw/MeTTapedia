import Std

/-!
# Revisioned space service

A storage protocol model, independent of an evaluator or agent policy. Atom
keys stand for portable terms modulo variable renaming within one term. The
host must implement that coding, backend matching, synchronization and quota
checks faithfully. These laws do not verify C, a filesystem or a Rust bridge.

Every accepted mutation advances a revision, including a no-op. Consequently
an exact retry cannot apply twice after its receipt has been retired. Receipt
retention provides repeatable answers, not unlimited exactly-once delivery.
-/

namespace Mettapedia.Machines.SpaceService

/-- A coding obligation for portable terms, already quotiented by alpha
equivalence. The real codec and byte-rope implementation must establish this
property; count agreement alone cannot establish it. -/
structure PortableKeyCodec where
  encode : Nat → List Nat
  decode : List Nat → Option Nat
  roundtrip : ∀ value, decode (encode value) = some value

theorem portable_keys_do_not_collide (codec : PortableKeyCodec) (left right : Nat)
    (h : codec.encode left = codec.encode right) : left = right := by
  have decoded := congrArg codec.decode h
  rw [codec.roundtrip, codec.roundtrip] at decoded
  exact Option.some.inj decoded

theorem portable_keys_preserve_distinctions (codec : PortableKeyCodec) (left right : Nat)
    (h : left ≠ right) : codec.encode left ≠ codec.encode right := by
  intro same
  exact h (portable_keys_do_not_collide codec left right same)

theorem portable_keys_preserve_occurrence_count (codec : PortableKeyCodec) (rows : List Nat) :
    (rows.map codec.encode).length = rows.length := by simp

theorem portable_projection_recovers_each_row (codec : PortableKeyCodec) (rows : List Nat) :
    (rows.map codec.encode).map codec.decode = rows.map some := by
  simp [List.map_map, codec.roundtrip]

theorem equal_counts_do_not_certify_projection :
    ([7] : List Nat).length = [8].length ∧ ([7] : List Nat) ≠ [8] := by decide

inductive Kind | bag | support deriving DecidableEq, Repr

def insert (kind : Kind) (rows : List Nat) (value : Nat) : List Nat :=
  match kind with
  | .bag => rows ++ [value]
  | .support => if value ∈ rows then rows else rows ++ [value]

theorem bag_insert_adds_one (rows : List Nat) (value : Nat) :
    (insert .bag rows value).length = rows.length + 1 := by
  simp [insert]

theorem support_duplicate_preserves_rows (rows : List Nat) (value : Nat)
    (present : value ∈ rows) : insert .support rows value = rows := by
  simp [insert, present]

theorem support_insert_contains (rows : List Nat) (value : Nat) :
    value ∈ insert .support rows value := by
  simp only [insert]
  split <;> simp_all

structure Store where
  identity : Nat
  revision : Nat
  rows : List Nat
deriving DecidableEq, Repr

inductive Failure | stale | identity | reusedId | expired | offset | limit
deriving DecidableEq, Repr

def conditionalWrite (store : Store) (identity revision : Nat)
    (rows : List Nat) : Except Failure Store :=
  if identity ≠ store.identity then .error .identity
  else if revision ≠ store.revision then .error .stale
  else .ok { store with revision := store.revision + 1, rows := rows }

theorem wrong_identity_refused (store : Store) (identity revision : Nat)
    (rows : List Nat) (h : identity ≠ store.identity) :
    conditionalWrite store identity revision rows = .error .identity := by
  simp [conditionalWrite, h]

theorem stale_write_refused (store : Store) (revision : Nat) (rows : List Nat)
    (h : revision ≠ store.revision) :
    conditionalWrite store store.identity revision rows = .error .stale := by
  simp [conditionalWrite, h]

theorem current_write (store : Store) (rows : List Nat) :
    conditionalWrite store store.identity store.revision rows =
      .ok { store with revision := store.revision + 1, rows := rows } := by
  simp [conditionalWrite]

theorem retry_after_write_is_stale (store : Store) (rows again : List Nat) :
    conditionalWrite { store with revision := store.revision + 1, rows := rows }
      store.identity store.revision again = .error .stale := by
  simp [conditionalWrite]

theorem no_op_advances_revision (store : Store) :
    conditionalWrite store store.identity store.revision store.rows =
      .ok { store with revision := store.revision + 1 } := by
  simp [conditionalWrite]

abbrev Catalog := Nat → Option Store

def update (catalog : Catalog) (name : Nat) (store : Option Store) : Catalog :=
  fun other => if other = name then store else catalog other

theorem update_selected (catalog : Catalog) (name : Nat) (store : Option Store) :
    update catalog name store name = store := by simp [update]

theorem update_other (catalog : Catalog) (name other : Nat) (store : Option Store)
    (h : other ≠ name) : update catalog name store other = catalog other := by
  simp [update, h]

theorem independent_updates_commute (catalog : Catalog) (left right : Nat)
    (a b : Option Store) (h : left ≠ right) :
    update (update catalog left a) right b =
      update (update catalog right b) left a := by
  funext name
  simp only [update]
  split <;> split <;> simp_all

structure Request where
  id : Nat
  identity : Nat
  revision : Nat
  /-- Original request bytes, independently of normalized storage keys. -/
  body : List Nat
deriving DecidableEq, Repr

structure Receipt where
  request : Request
  result : Store
deriving DecidableEq, Repr

def retry (receipt : Receipt) (request : Request) : Except Failure Store :=
  if request = receipt.request then .ok receipt.result else .error .reusedId

theorem identical_retry_preserves_result (receipt : Receipt) :
    retry receipt receipt.request = .ok receipt.result := by simp [retry]

theorem changed_body_is_refused (receipt : Receipt) (request : Request)
    (h : request ≠ receipt.request) : retry receipt request = .error .reusedId := by
  simp [retry, h]

theorem byte_distinct_body_is_refused (receipt : Receipt) (body : List Nat)
    (h : body ≠ receipt.request.body) :
    retry receipt { receipt.request with body := body } = .error .reusedId := by
  apply changed_body_is_refused
  intro same
  exact h (congrArg Request.body same)

structure Journal where
  checkpoint : Store
  synced : List Store
  staged : List Store
deriving DecidableEq, Repr

def recovered (journal : Journal) : Store :=
  journal.synced.getLast?.getD journal.checkpoint

def stage (journal : Journal) (candidate : Store) : Journal :=
  { journal with staged := journal.staged ++ [candidate] }

def synchronize (journal : Journal) : Journal :=
  { journal with synced := journal.synced ++ journal.staged, staged := [] }

theorem staging_cannot_change_recovery (journal : Journal) (candidate : Store) :
    recovered (stage journal candidate) = recovered journal := by rfl

theorem unacknowledged_tail_cannot_change_recovery (journal : Journal) (tail : List Store) :
    recovered { journal with staged := tail } = recovered journal := by rfl

theorem synchronized_candidate_is_recovered (journal : Journal) (candidate : Store) :
    recovered (synchronize (stage journal candidate)) = candidate := by
  simp [recovered, synchronize, stage]

structure Runtime where
  journal : Journal
  visible : Store
deriving DecidableEq, Repr

def publish (runtime : Runtime) : Runtime :=
  { runtime with visible := recovered runtime.journal }

def restart (runtime : Runtime) : Runtime :=
  { journal := { runtime.journal with staged := [] }
    visible := recovered runtime.journal }

def acknowledgement (runtime : Runtime) : Option Store :=
  if runtime.visible = recovered runtime.journal then some runtime.visible else none

theorem acknowledgement_requires_durable_visibility (runtime : Runtime) (store : Store)
    (h : acknowledgement runtime = some store) :
    store = recovered runtime.journal := by
  simp only [acknowledgement] at h
  split at h
  · simpa using (Option.some.inj h).symm.trans ‹_›
  · contradiction

theorem acknowledged_state_survives_restart (runtime : Runtime) (store : Store)
    (h : acknowledgement runtime = some store) :
    (restart runtime).visible = store := by
  exact (acknowledgement_requires_durable_visibility runtime store h).symm

theorem publication_is_acknowledgeable (runtime : Runtime) :
    acknowledgement (publish runtime) = some (recovered runtime.journal) := by
  simp [acknowledgement, publish]

theorem restart_discards_unsynced_tail (runtime : Runtime) :
    (restart runtime).journal.staged = [] := by rfl

def compact (journal : Journal) : Journal :=
  { checkpoint := recovered journal, synced := [], staged := journal.staged }

theorem compaction_preserves_recovery (journal : Journal) :
    recovered (compact journal) = recovered journal := by rfl

structure Snapshot where
  service : Nat
  cursor : Nat
  source : Nat
  revision : Nat
  rows : List Nat
  expires : Nat
deriving DecidableEq, Repr

def capture (service cursor expires : Nat) (store : Store) : Snapshot :=
  ⟨service, cursor, store.identity, store.revision, store.rows, expires⟩

def page (snapshot : Snapshot) (service cursor now offset count : Nat) :
    Except Failure (List Nat) :=
  if service ≠ snapshot.service ∨ cursor ≠ snapshot.cursor then .error .identity
  else if snapshot.expires ≤ now then .error .expired
  else if snapshot.rows.length < offset then .error .offset
  else .ok ((snapshot.rows.drop offset).take count)

/-- The current store is deliberately outside the snapshot page authority. -/
def observedPage (current : Store) (snapshot : Snapshot)
    (service cursor now offset count : Nat) : Except Failure (List Nat) :=
  let _ := current
  page snapshot service cursor now offset count

theorem writes_cannot_change_captured_page (before after : Store) (snapshot : Snapshot)
    (service cursor now offset count : Nat) :
    observedPage before snapshot service cursor now offset count =
      observedPage after snapshot service cursor now offset count := by rfl

theorem later_read_within_lease_has_same_page (snapshot : Snapshot)
    (earlier later offset count : Nat)
    (early : earlier < snapshot.expires) (late : later < snapshot.expires) :
    page snapshot snapshot.service snapshot.cursor earlier offset count =
      page snapshot snapshot.service snapshot.cursor later offset count := by
  simp [page, Nat.not_le.mpr early, Nat.not_le.mpr late]

theorem snapshot_retains_captured_revision (service cursor expires : Nat) (store : Store) :
    (capture service cursor expires store).revision = store.revision := by rfl

theorem snapshot_is_not_current_authority (service cursor expires : Nat) (store : Store)
    (rows : List Nat) :
    conditionalWrite { store with revision := store.revision + 1, rows := rows }
      (capture service cursor expires store).source
      (capture service cursor expires store).revision rows = .error .stale := by
  simp [capture, conditionalWrite]

theorem expired_snapshot_is_error (snapshot : Snapshot) (now offset count : Nat)
    (h : snapshot.expires ≤ now) :
    page snapshot snapshot.service snapshot.cursor now offset count = .error .expired := by
  simp [page, h]

theorem wrong_cursor_is_refused (snapshot : Snapshot) (cursor now offset count : Nat)
    (h : cursor ≠ snapshot.cursor) :
    page snapshot snapshot.service cursor now offset count = .error .identity := by
  simp [page, h]

theorem wrong_service_is_refused (snapshot : Snapshot) (service now offset count : Nat)
    (h : service ≠ snapshot.service) :
    page snapshot service snapshot.cursor now offset count = .error .identity := by
  simp [page, h]

theorem invalid_offset_is_refused (snapshot : Snapshot) (now offset count : Nat)
    (fresh : now < snapshot.expires) (outside : snapshot.rows.length < offset) :
    page snapshot snapshot.service snapshot.cursor now offset count = .error .offset := by
  simp [page, Nat.not_le.mpr fresh, outside]

theorem page_respects_requested_bound (snapshot : Snapshot) (service cursor now offset count : Nat)
    (rows : List Nat) (h : page snapshot service cursor now offset count = .ok rows) :
    rows.length ≤ count := by
  simp only [page] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  simp only [List.length_take, List.length_drop]
  exact Nat.min_le_left _ _

theorem exhausted_snapshot_is_success (snapshot : Snapshot) (now count : Nat)
    (h : now < snapshot.expires) :
    page snapshot snapshot.service snapshot.cursor now snapshot.rows.length count = .ok [] := by
  simp [page, Nat.not_le.mpr h]

theorem expiry_is_not_exhaustion :
    (Except.error Failure.expired : Except Failure (List Nat)) ≠ .ok [] := by intro h; cases h

theorem query_does_not_mutate (store : Store) (service cursor expires : Nat) :
    (capture service cursor expires store).rows = store.rows := by rfl

theorem bag_and_support_differ : insert .bag [7] 7 ≠ insert .support [7] 7 := by decide

theorem stale_unconditional_write_control :
    conditionalWrite ⟨1, 2, [7]⟩ 1 1 [8] ≠ .ok ⟨1, 2, [8]⟩ := by
  simp [conditionalWrite]

theorem unsynced_publication_control :
    acknowledgement ⟨⟨⟨1, 0, []⟩, [], [⟨1, 1, [7]⟩]⟩, ⟨1, 1, [7]⟩⟩ = none := by decide

end Mettapedia.Machines.SpaceService
