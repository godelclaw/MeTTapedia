import Std

/-!
# Revision-bound memory collections

The authoritative store is keyed; an accelerator is a disposable view with a
captured source revision and profile. A validated mutation commits only at its
expected revision. Rebuilding and restart read the committed store, including
deletions. Shadow observations cannot publish a source mutation.

This model specifies the adapter boundary. Faithful key lookup/removal, tensor
validation, synchronized storage and numerical ranking are host obligations;
these theorems do not prove the C implementation or an embedding's relevance.
-/
set_option autoImplicit false
namespace Mettapedia.Algebra.MemoryCollection

structure Record where
  profile : Nat
  embedding : List Int
  document : Nat
  deriving DecidableEq, Repr

structure Store where
  revision : Nat
  profile : Nat
  rows : Nat → Option Record

structure View where
  revision : Nat
  profile : Nat
  rows : Nat → Option Record

def capture (s : Store) : View := ⟨s.revision, s.profile, s.rows⟩

def replace (rows : Nat → Option Record) (id : Nat) (value : Option Record) :
    Nat → Option Record := fun key => if key = id then value else rows key

def commit (s : Store) (expected : Nat) (valid : Bool) (id : Nat)
    (value : Option Record) : Option Store :=
  if expected = s.revision ∧ valid = true then
    some ⟨s.revision + 1, s.profile, replace s.rows id value⟩
  else none

def usable (s : Store) (v : View) : Bool :=
  decide (s.revision = v.revision ∧ s.profile = v.profile)

inductive Observation where
  | unavailable
  | rows (values : List Record)
  deriving DecidableEq, Repr

/-- Refusal is distinct from a successful empty result. -/
def observe (s : Store) (v : View) (select : (Nat → Option Record) → List Record) :
    Observation := if usable s v then .rows (select v.rows) else .unavailable

def recover (durable : Store) : Store := durable
def shadow (s : Store) (_ : Observation) : Store := s

theorem replace_here (rows : Nat → Option Record) (id : Nat) (value : Option Record) :
    replace rows id value id = value := by simp [replace]

theorem replace_elsewhere (rows : Nat → Option Record) (id key : Nat)
    (value : Option Record) (different : key ≠ id) :
    replace rows id value key = rows key := by simp [replace, different]

theorem replacement_overwrites (rows : Nat → Option Record) (id : Nat)
    (first last : Option Record) : replace (replace rows id first) id last = replace rows id last := by
  funext key
  by_cases h : key = id <;> simp [replace, h]

theorem deletion_idempotent (rows : Nat → Option Record) (id : Nat) :
    replace (replace rows id none) id none = replace rows id none := replacement_overwrites ..

theorem stale_commit_refused (s : Store) (expected : Nat) (valid : Bool)
    (id : Nat) (value : Option Record) (stale : expected ≠ s.revision) :
    commit s expected valid id value = none := by simp [commit, stale]

theorem invalid_commit_refused (s : Store) (expected id : Nat) (value : Option Record) :
    commit s expected false id value = none := by simp [commit]

theorem accepted_commit (s : Store) (id : Nat) (value : Option Record) :
    commit s s.revision true id value =
      some ⟨s.revision + 1, s.profile, replace s.rows id value⟩ := by simp [commit]

theorem accepted_advances_revision (s next : Store) (expected id : Nat)
    (valid : Bool) (value : Option Record) (accepted : commit s expected valid id value = some next) :
    next.revision = s.revision + 1 := by
  unfold commit at accepted
  split at accepted
  · cases accepted; rfl
  · contradiction

theorem accepted_preserves_profile (s next : Store) (expected id : Nat)
    (valid : Bool) (value : Option Record) (accepted : commit s expected valid id value = some next) :
    next.profile = s.profile := by
  unfold commit at accepted
  split at accepted
  · cases accepted; rfl
  · contradiction

theorem deletion_survives_recovery (s next : Store) (expected id : Nat)
    (accepted : commit s expected true id none = some next) :
    (recover next).rows id = none := by
  unfold commit at accepted
  split at accepted
  · cases accepted; simp [recover, replace]
  · contradiction

theorem unrelated_key_preserved (s next : Store) (expected id key : Nat)
    (value : Option Record) (different : key ≠ id)
    (accepted : commit s expected true id value = some next) : next.rows key = s.rows key := by
  unfold commit at accepted
  split at accepted
  · cases accepted; simp [replace, different]
  · contradiction

theorem capture_usable (s : Store) : usable s (capture s) = true := by simp [usable, capture]

theorem captured_observation (s : Store) (select : (Nat → Option Record) → List Record) :
    observe s (capture s) select = .rows (select s.rows) := by simp [observe, usable, capture]

theorem stale_view_unavailable (s : Store) (v : View)
    (select : (Nat → Option Record) → List Record) (stale : s.revision ≠ v.revision) :
    observe s v select = .unavailable := by simp [observe, usable, stale]

theorem wrong_profile_unavailable (s : Store) (v : View)
    (select : (Nat → Option Record) → List Record) (wrong : s.profile ≠ v.profile) :
    observe s v select = .unavailable := by simp [observe, usable, wrong]

theorem committed_write_invalidates_old_view (s next : Store) (expected id : Nat)
    (value : Option Record) (select : (Nat → Option Record) → List Record)
    (accepted : commit s expected true id value = some next) :
    observe next (capture s) select = .unavailable := by
  apply stale_view_unavailable
  have advanced := accepted_advances_revision s next expected id true value accepted
  simp only [capture]
  omega

theorem rebuild_recovers_current_rows (s : Store) : (capture (recover s)).rows = s.rows := rfl
theorem restart_preserves_revision (s : Store) : (recover s).revision = s.revision := rfl
theorem shadow_preserves_authority (s : Store) (result : Observation) : shadow s result = s := rfl
theorem failure_is_not_empty : Observation.unavailable ≠ .rows [] := by decide

private def exampleStore : Store := ⟨7, 3, fun _ => none⟩
example : commit exampleStore 6 true 2 none = none := by decide
example : usable exampleStore ⟨6, 3, fun _ => none⟩ = false := by decide
example : observe exampleStore ⟨6, 3, fun _ => none⟩ (fun _ => []) = .unavailable := by decide

end Mettapedia.Algebra.MemoryCollection
