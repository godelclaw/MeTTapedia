import Std

/-!+# Exact queries through candidate indexes

Hashes select candidates, never authorize equality. Values here abstract the
complete typed field encoding; no hash injectivity is assumed. Index membership
is separate from primary rows, so the model can express a bucket that remains
unchanged while an inspected row changes.

The ordered key sequence abstracts the disk iterator. Key encoding, iterator
coverage/order, the C implementation and I/O remain separate obligations.
The executable collision trace is compared with the real MeTTa query and scoped
commit paths, including a deliberately insufficient bucket-only validation.
-/

namespace Mettapedia.Machines.NativeProviderIndex

abbrev Rows (α : Type) := Nat → Option α
abbrev Index := Nat → Nat → Bool

def consistent {α : Type} (hash : α → Nat) (rows : Rows α) (index : Index) : Prop :=
  ∀ digest key, index digest key = true ↔ ∃ value, rows key = some value ∧ hash value = digest

def satisfies {α : Type} [DecidableEq α] (rows : Rows α) (wanted : α) (key : Nat) : Bool :=
  decide (rows key = some wanted)

def indexed {α : Type} [DecidableEq α] (hash : α → Nat) (rows : Rows α)
    (index : Index) (wanted : α) (key : Nat) : Bool :=
  index (hash wanted) key && satisfies rows wanted key

theorem indexed_selection_is_exact {α : Type} [DecidableEq α] (hash : α → Nat)
    (rows : Rows α) (index : Index) (valid : consistent hash rows index)
    (wanted : α) (key : Nat) : indexed hash rows index wanted key = satisfies rows wanted key := by
  by_cases selected : rows key = some wanted
  · have member : index (hash wanted) key = true := (valid _ _).mpr ⟨wanted, selected, rfl⟩
    simp [indexed, satisfies, selected, member]
  · simp [indexed, satisfies, selected]

/-- Both filtering stages preserve the supplied sequence's order and bag
multiplicity. No set rewrite discards duplicate occurrences. -/
def queryKeys {α : Type} [DecidableEq α] (hash : α → Nat) (rows : Rows α)
    (index : Index) (wanted : α) (keys : List Nat) : List Nat :=
  (keys.filter (index (hash wanted))).filter (satisfies rows wanted)

theorem candidate_filter_preserves_ordered_answer {α : Type} [DecidableEq α]
    (hash : α → Nat) (rows : Rows α) (index : Index) (valid : consistent hash rows index)
    (wanted : α) (keys : List Nat) :
    queryKeys hash rows index wanted keys = keys.filter (satisfies rows wanted) := by
  simp only [queryKeys, List.filter_filter]
  apply List.filter_congr
  intro key _membership
  simpa [indexed, Bool.and_comm] using indexed_selection_is_exact hash rows index valid wanted key

def replaceRows {α : Type} (rows : Rows α) (key : Nat) (value : Option α) : Rows α :=
  fun other => if other = key then value else rows other

/-- Logical membership of deleting the old row's index entry and inserting
the replacement's entry. The physical implementation changes only that row's
old/new entries; consistency says it had no entry in any other bucket. -/
def replaceIndex {α : Type} (hash : α → Nat) (index : Index)
    (key : Nat) (value : Option α) : Index :=
  fun digest other =>
    if other = key then
      match value with
      | none => false
      | some next => decide (hash next = digest)
    else index digest other

theorem replacement_preserves_consistency {α : Type} (hash : α → Nat)
    (rows : Rows α) (index : Index) (valid : consistent hash rows index)
    (key : Nat) (value : Option α) :
    consistent hash (replaceRows rows key value) (replaceIndex hash index key value) := by
  intro digest other
  by_cases same : other = key
  · subst other
    cases value with
    | none => simp [replaceRows, replaceIndex]
    | some next => simp [replaceRows, replaceIndex]
  · simpa [replaceRows, replaceIndex, same] using valid digest other

theorem foreign_row_index_is_unchanged {α : Type} (hash : α → Nat) (index : Index)
    (key other digest : Nat) (value : Option α) (different : other ≠ key) :
    replaceIndex hash index key value digest other = index digest other := by
  simp [replaceIndex, different]

/-- This is why readers record primary rows even for candidates rejected by
the full-value filter. Bucket equality alone is insufficient. -/
theorem complete_reads_preserve_selection {α : Type} [DecidableEq α] (hash : α → Nat)
    (before after : Rows α) (oldIndex newIndex : Index) (wanted : α)
    (sameBucket : ∀ key, oldIndex (hash wanted) key = newIndex (hash wanted) key)
    (sameBodies : ∀ key, oldIndex (hash wanted) key = true → before key = after key)
    (key : Nat) :
    indexed hash before oldIndex wanted key = indexed hash after newIndex wanted key := by
  cases membership : oldIndex (hash wanted) key with
  | false => simp [indexed, membership, ← sameBucket key]
  | true => simp [indexed, membership, ← sameBucket key, satisfies, sameBodies key membership]

def collisionHash (_ : Nat) : Nat := 0
def before : Rows Nat := fun key =>
  if key = 1 then some 0 else if key = 2 then some 1 else none
def after : Rows Nat := replaceRows before 1 (some 1)
def bucket : Index := fun digest key => digest == 0 && (key == 1 || key == 2)

theorem collision_example_indexes_are_consistent :
    consistent collisionHash before bucket ∧ consistent collisionHash after bucket := by
  constructor <;> intro digest key <;>
    by_cases first : key = 1 <;> by_cases second : key = 2 <;>
      simp [collisionHash, before, after, replaceRows, bucket, first, second]
  all_goals constructor <;> intro equal <;> exact equal.symm

def bucketSame : Bool := [1, 2].all (fun key => bucket 0 key == bucket 0 key)
def bodiesSame : Bool := [1, 2].all (fun key => decide (before key = after key))
def validation (includeBodies : Bool) : String :=
  if bucketSame && (!includeBodies || bodiesSame) then "accepted" else "conflict"

theorem bucket_only_authority_has_a_counterexample :
    queryKeys collisionHash before bucket 1 [1, 2] = [2] ∧
    queryKeys collisionHash after bucket 1 [1, 2] = [1, 2] ∧
    validation false = "accepted" ∧ validation true = "conflict" := by decide

def trace : String :=
  let old := (queryKeys collisionHash before bucket 1 [1, 2]).length
  let next := (queryKeys collisionHash after bucket 1 [1, 2]).length
  s!"INDEX_QUERY_TRACE {old} {next} {validation true} {validation false}"

end Mettapedia.Machines.NativeProviderIndex

#eval IO.println Mettapedia.Machines.NativeProviderIndex.trace
