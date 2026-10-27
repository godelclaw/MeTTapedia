import Mettapedia.Util.LinearHash
import Mathlib.Tactic

/-!
# A partial hash index with permanent equality fallback

The source scans its retained keys with a supplied pure comparison. The
indexed worker examines only a matching bucket while every retained key has
an admitted hash. On the first refused hash it keeps the complete inventory
and switches permanently to the source comparison. Accepted occurrences are
published separately, preserving their original representatives and order.

The comparison need not be reflexive: this includes profiles whose NaNs do
not equal themselves. The hash law is required only for admitted pairs that
the comparison accepts. Concrete examples separate finite representations
from equal graph views. Native structural-fact admission, word hashing,
open-addressed storage, compaction and pointer lifetimes remain C obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PartialHashIndex

variable {Key : Type}

def Compatible (same : Key → Key → Bool) (hash : Key → Option Nat) : Prop :=
  ∀ left right first second, same left right = true →
    hash left = some first → hash right = some second → first = second

def contains (same : Key → Key → Bool) (keys : List Key) (query : Key) : Bool :=
  keys.any fun key => same key query

def bucketContains (same : Key → Key → Bool) (hash : Key → Option Nat)
    (keys : List Key) (query : Key) (code : Nat) : Bool :=
  keys.any fun key => (hash key == some code) && same key query

structure State (Key : Type) where
  hashed : Bool
  keys : List Key

def Valid (hash : Key → Option Nat) (state : State Key) : Prop :=
  state.hashed = true → ∀ key ∈ state.keys, ∃ code, hash key = some code

def hit (same : Key → Key → Bool) (hash : Key → Option Nat)
    (state : State Key) (query : Key) : Bool :=
  if state.hashed then
    match hash query with
    | some code => bucketContains same hash state.keys query code
    | none => contains same state.keys query
  else contains same state.keys query

def advance (same : Key → Key → Bool) (hash : Key → Option Nat)
    (state : State Key) (query : Key) : State Key :=
  { hashed := state.hashed && (hash query).isSome
    keys := if hit same hash state query then state.keys else query :: state.keys }

theorem bucket_refines (same : Key → Key → Bool) (hash : Key → Option Nat)
    (law : Compatible same hash) (keys : List Key) (query : Key) (code : Nat)
    (admitted : ∀ key ∈ keys, ∃ h, hash key = some h)
    (current : hash query = some code) :
    bucketContains same hash keys query code = contains same keys query := by
  apply Bool.eq_iff_iff.mpr
  simp only [bucketContains, contains, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨key, member, _, equal⟩
    exact ⟨key, member, equal⟩
  · rintro ⟨key, member, equal⟩
    obtain ⟨h, stored⟩ := admitted key member
    have sameCode := law key query h code equal stored current
    exact ⟨key, member, sameCode ▸ stored, equal⟩

theorem hit_refines (same : Key → Key → Bool) (hash : Key → Option Nat)
    (law : Compatible same hash) (state : State Key) (valid : Valid hash state)
    (query : Key) : hit same hash state query = contains same state.keys query := by
  unfold hit
  split
  · rename_i indexed
    cases observed : hash query with
    | none => rfl
    | some code => exact bucket_refines same hash law state.keys query code (valid indexed) observed
  · rfl

theorem advance_valid (same : Key → Key → Bool) (hash : Key → Option Nat)
    (state : State Key) (valid : Valid hash state) (query : Key) :
    Valid hash (advance same hash state query) := by
  intro indexed key member
  change (state.hashed && (hash query).isSome) = true at indexed
  simp only [Bool.and_eq_true] at indexed
  obtain ⟨prior, present⟩ := indexed
  change key ∈ (if hit same hash state query then state.keys else query :: state.keys) at member
  split at member
  · exact valid prior key member
  · rcases List.mem_cons.mp member with equal | member
    · subst key
      cases observed : hash query with
      | none => simp [observed] at present
      | some code => exact ⟨code, rfl⟩
    · exact valid prior key member

theorem fallback_is_permanent (same : Key → Key → Bool) (hash : Key → Option Nat)
    (keys : List Key) (query : Key) :
    (advance same hash ⟨false, keys⟩ query).hashed = false := rfl

def sourceRun (same : Key → Key → Bool) : List Key → List Key → List Key
  | _, [] => []
  | keys, query :: rest =>
      if contains same keys query then sourceRun same keys rest
      else query :: sourceRun same (query :: keys) rest

def indexedRun (same : Key → Key → Bool) (hash : Key → Option Nat) :
    State Key → List Key → List Key
  | _, [] => []
  | state, query :: rest =>
      if hit same hash state query then indexedRun same hash (advance same hash state query) rest
      else query :: indexedRun same hash (advance same hash state query) rest

/-- Every accepted source occurrence, including its chosen representative,
agrees with the independent full-scan reference through mode changes. -/
theorem run_refines (same : Key → Key → Bool) (hash : Key → Option Nat)
    (law : Compatible same hash) (state : State Key) (valid : Valid hash state)
    (queries : List Key) :
    indexedRun same hash state queries = sourceRun same state.keys queries := by
  induction queries generalizing state with
  | nil => rfl
  | cons query rest ih =>
      simp only [indexedRun, sourceRun]
      have equal := hit_refines same hash law state valid query
      have next := ih (advance same hash state query) (advance_valid same hash state valid query)
      rw [equal]
      split <;> rw [next] <;> simp_all [advance]

inductive Representation where
  | finite (value : Nat)
  | view (value : Nat)
  deriving DecidableEq

def value : Representation → Nat
  | .finite n | .view n => n

def sameValue (left right : Representation) : Bool := value left == value right

def partialHash : Representation → Option Nat
  | .finite n => some ((n * 37 + 17) % 65536)
  | .view _ => none

theorem partial_hash_compatible : Compatible sameValue partialHash := by
  intro left right first second equal a b
  cases left <;> cases right <;> simp_all [sameValue, value, partialHash]

theorem mixed_representations_keep_one_occurrence :
    indexedRun sameValue partialHash ⟨true, []⟩
      [.finite 0, .finite 1, .view 0, .view 2, .finite 2, .finite 1] =
      [.finite 0, .finite 1, .view 2] := by decide

/-- Reentering hash mode would miss the earlier equal unsupported key. -/
theorem restarting_hash_mode_misses_an_equal_view :
    bucketContains sameValue partialHash [.view 0] (.finite 0) 17 = false ∧
      contains sameValue [.view 0] (.finite 0) = true := by decide

#print axioms bucket_refines
#print axioms hit_refines
#print axioms advance_valid
#print axioms fallback_is_permanent
#print axioms run_refines
#print axioms partial_hash_compatible
#print axioms mixed_representations_keep_one_occurrence
#print axioms restarting_hash_mode_misses_an_equal_view

end Mettapedia.Machines.PartialHashIndex
