import Mettapedia.Machines.BranchLocalNeed.ReferenceSemantics
import Mathlib.Tactic

/-!
# Persistent bounded index for reference Need heaps

The reference Need heap deliberately exposes an extensional finite-map view
and a persistent semantic update spine.  A native snapshot may additionally
carry this immutable radix index from stable cell keys to the newest frame.
The index is derived: lookup agrees with the semantic heap, while the update
spine remains the authority for lineage, ancestry, promotion, and replay.

Source cell identities remain unbounded. A partial assignment gives native
keys only to the cells represented in a particular heap. Injectivity applies
to assigned keys, not to every possible source identity.

Keys have exactly sixteen hexadecimal digits, matching an internal 64-bit
cell key.  Every successful indexed lookup therefore follows at most sixteen
edges and examines one terminal node.  Updates path-copy the same bounded
route, so sibling snapshots share all unaffected subtries.
-/

namespace Mettapedia.Machines.BranchLocalNeed.NeedHeapIndex

open NeedReference

abbrev Digit := Fin 16

/-- A 64-bit internal key represented without hashing or collisions. -/
abbrev Key := { path : List Digit // path.length = 16 }

/-- A persistent radix trie.  `value` permits the generic list-key proofs;
reference's fixed-width keys place values only at depth sixteen. -/
inductive Trie (α : Type*) where
  | node (value : Option α) (children : Digit → Option (Trie α))

namespace Trie

variable {α : Type*}

def empty : Trie α :=
  .node none (fun _ => none)

def lookup : Trie α → List Digit → Option α
  | .node value _, [] => value
  | .node _ children, digit :: rest =>
      match children digit with
      | none => none
      | some child => child.lookup rest

def insert : Trie α → List Digit → α → Trie α
  | .node _ children, [], value =>
      .node (some value) children
  | .node here children, digit :: rest, value =>
      let child := (children digit).getD empty
      .node here
        (Function.update children digit
          (some (child.insert rest value)))

@[simp] theorem lookup_empty (path : List Digit) :
    (empty : Trie α).lookup path = none := by
  cases path <;> rfl

@[simp] theorem lookup_insert_self
    (trie : Trie α) (path : List Digit) (value : α) :
    (trie.insert path value).lookup path = some value := by
  induction path generalizing trie with
  | nil =>
      cases trie
      rfl
  | cons digit rest ih =>
      cases trie with
      | node here children =>
          simp only [insert, lookup, Function.update_self]
          exact ih _

theorem lookup_insert_other
    (trie : Trie α) {inserted queried : List Digit} (value : α)
    (hDifferent : queried ≠ inserted) :
    (trie.insert inserted value).lookup queried = trie.lookup queried := by
  induction inserted generalizing trie queried with
  | nil =>
      cases queried with
      | nil => exact False.elim (hDifferent rfl)
      | cons digit rest =>
          cases trie
          rfl
  | cons insertedDigit insertedRest ih =>
      cases queried with
      | nil =>
          cases trie
          rfl
      | cons queriedDigit queriedRest =>
          cases trie with
          | node here children =>
              by_cases hDigit : queriedDigit = insertedDigit
              · subst queriedDigit
                have hRest : queriedRest ≠ insertedRest := by
                  intro hEqual
                  exact hDifferent (congrArg (List.cons insertedDigit) hEqual)
                cases hChild : children insertedDigit with
                | none =>
                    simp [insert, lookup, hChild, ih empty hRest]
                | some child =>
                    simp [insert, lookup, hChild, ih child hRest]
              · simp [insert, lookup, Function.update, hDigit]

/-- Lookup work counts node examinations and can stop at an absent child. -/
def lookupSteps : Trie α → List Digit → Nat
  | .node _ _, [] => 1
  | .node _ children, digit :: rest =>
      1 +
        match children digit with
        | none => 0
        | some child => child.lookupSteps rest

theorem lookupSteps_le (trie : Trie α) (path : List Digit) :
    trie.lookupSteps path ≤ path.length + 1 := by
  induction path generalizing trie with
  | nil =>
      cases trie
      simp [lookupSteps]
  | cons digit rest ih =>
      cases trie with
      | node here children =>
          cases hChild : children digit with
          | none => simp [lookupSteps, hChild]
          | some child =>
              simp only [lookupSteps, hChild, List.length_cons]
              have hBound := ih child
              omega

theorem lookupSteps_insert_self
    (trie : Trie α) (path : List Digit) (value : α) :
    (trie.insert path value).lookupSteps path = path.length + 1 := by
  induction path generalizing trie with
  | nil =>
      cases trie
      rfl
  | cons digit rest ih =>
      cases trie with
      | node here children =>
          simp only [insert, lookupSteps, Function.update_self,
            List.length_cons]
          rw [ih]
          omega

def lookupKey (trie : Trie α) (key : Key) : Option α :=
  trie.lookup key.1

def insertKey (trie : Trie α) (key : Key) (value : α) : Trie α :=
  trie.insert key.1 value

@[simp] theorem lookupKey_insert_self
    (trie : Trie α) (key : Key) (value : α) :
    (trie.insertKey key value).lookupKey key = some value :=
  lookup_insert_self trie key.1 value

theorem lookupKey_insert_other
    (trie : Trie α) {inserted queried : Key} (value : α)
    (hDifferent : queried ≠ inserted) :
    (trie.insertKey inserted value).lookupKey queried =
      trie.lookupKey queried := by
  apply lookup_insert_other
  intro hPaths
  exact hDifferent (Subtype.ext hPaths)

theorem lookupKey_steps_le (trie : Trie α) (key : Key) :
    trie.lookupSteps key.1 ≤ 17 := by
  simpa [key.2] using lookupSteps_le trie key.1

theorem lookupKey_insert_steps
    (trie : Trie α) (key : Key) (value : α) :
    (trie.insertKey key value).lookupSteps key.1 = 17 := by
  simpa [insertKey, key.2] using lookupSteps_insert_self trie key.1 value

end Trie

section HeapRefinement

variable {Origin Value StableFault : Type*}

/-- Unassigned cells observe absence; assigned keys agree with the source heap. -/
def Consistent
    (keyOf : CellId → Option Key)
    (heap : Heap Origin Value StableFault)
    (index : Trie (CellRecord Origin Value StableFault)) : Prop :=
  ∀ cell, (keyOf cell).bind index.lookupKey = heap.lookup cell

/-- A finite native key space need distinguish only its assigned source cells. -/
def AssignedKeysUnique (keyOf : CellId → Option Key) : Prop :=
  ∀ {left right key}, keyOf left = some key → keyOf right = some key → left = right

/-- Availability is a semantic premise. A native allocator must derive it
from its finite assignment inventory; arbitrary function-valued assignments
do not provide a decision procedure. -/
def KeyAvailable (keyOf : CellId → Option Key) (key : Key) : Prop :=
  ∀ cell, keyOf cell ≠ some key

def assignKey (keyOf : CellId → Option Key) (cell : CellId) (key : Key) :
    CellId → Option Key :=
  Function.update keyOf cell (some key)

@[simp] theorem assignKey_same (keyOf : CellId → Option Key) (cell : CellId) (key : Key) :
    assignKey keyOf cell key cell = some key :=
  Function.update_self _ _ _

theorem assignKey_other (keyOf : CellId → Option Key) (cell : CellId) (key : Key)
    {other : CellId} (distinct : other ≠ cell) :
    assignKey keyOf cell key other = keyOf other :=
  Function.update_of_ne distinct _ _

theorem assignKey_preserves_unique {keyOf : CellId → Option Key}
    (unique : AssignedKeysUnique keyOf) {cell : CellId} {key : Key}
    (available : KeyAvailable keyOf key) :
    AssignedKeysUnique (assignKey keyOf cell key) := by
  intro left right selected leftRead rightRead
  by_cases leftSame : left = cell
  · subst left
    rw [assignKey_same] at leftRead
    have selectedSame : selected = key := (Option.some.inj leftRead).symm
    subst selected
    by_cases rightSame : right = cell
    · exact rightSame.symm
    · rw [assignKey_other keyOf cell key rightSame] at rightRead
      exact False.elim (available right rightRead)
  · rw [assignKey_other keyOf cell key leftSame] at leftRead
    by_cases rightSame : right = cell
    · subst right
      rw [assignKey_same] at rightRead
      have selectedSame : selected = key := (Option.some.inj rightRead).symm
      subst selected
      exact False.elim (available left leftRead)
    · rw [assignKey_other keyOf cell key rightSame] at rightRead
      exact unique leftRead rightRead

theorem empty_keys_unique : AssignedKeysUnique (fun _ => none) := by
  intro left right key impossible
  contradiction

theorem empty_consistent :
    Consistent (fun _ => none) (Heap.empty : Heap Origin Value StableFault) Trie.empty := by
  intro cell
  rfl

theorem lookup_refines
    {keyOf : CellId → Option Key}
    {heap : Heap Origin Value StableFault}
    {index : Trie (CellRecord Origin Value StableFault)}
    (consistent : Consistent keyOf heap index)
    (cell : CellId) :
    (keyOf cell).bind index.lookupKey = heap.lookup cell :=
  consistent cell

theorem unassigned_lookup_none {keyOf : CellId → Option Key}
    {heap : Heap Origin Value StableFault} {index : Trie (CellRecord Origin Value StableFault)}
    (consistent : Consistent keyOf heap index) {cell : CellId}
    (unassigned : keyOf cell = none) : heap.lookup cell = none := by
  simpa [unassigned] using (consistent cell).symm

theorem setKnownCache_preserves_consistency
    {keyOf : CellId → Option Key}
    (unique : AssignedKeysUnique keyOf)
    {heap : Heap Origin Value StableFault}
    {index : Trie (CellRecord Origin Value StableFault)}
    (consistent : Consistent keyOf heap index)
    (cell : CellId) (key : Key) (assigned : keyOf cell = some key)
    (record : CellRecord Origin Value StableFault)
    (state : Cache Value StableFault) :
    Consistent keyOf
      (heap.setKnownCache cell record state)
      (index.insertKey key { record with cache := state }) := by
  intro other
  by_cases hCell : other = cell
  · subst other
    simp [assigned]
  · rw [Heap.setKnownCache_preserves_other _ _ _ hCell, ← consistent other]
    cases otherRead : keyOf other with
    | none => rfl
    | some otherKey =>
        simp only [Option.bind_some]
        apply Trie.lookupKey_insert_other
        intro same
        subst otherKey
        exact hCell (unique otherRead assigned)

theorem allocate_preserves_consistency
    {keyOf : CellId → Option Key}
    {heap next : Heap Origin Value StableFault}
    {index : Trie (CellRecord Origin Value StableFault)}
    (consistent : Consistent keyOf heap index)
    {cell : CellId} {key : Key} {origin : Origin}
    (available : KeyAvailable keyOf key)
    (allocated : heap.allocate? cell origin = some next) :
    Consistent (assignKey keyOf cell key) next
      (index.insertKey key
        { origin := origin, cache := Cache.suspended }) := by
  intro other
  by_cases hCell : other = cell
  · subst other
    simp only [assignKey_same, Option.bind_some, Trie.lookupKey_insert_self]
    exact (Heap.allocate?_lookup_same allocated).symm
  · rw [assignKey_other keyOf cell key hCell,
      Heap.allocate?_preserves_other allocated hCell, ← consistent other]
    cases otherRead : keyOf other with
    | none => rfl
    | some otherKey =>
        simp only [Option.bind_some]
        apply Trie.lookupKey_insert_other
        intro same
        subst otherKey
        exact available other otherRead

end HeapRefinement

namespace Controls

private def first : CellId := ⟨7, [], 1, 0⟩
private def second : CellId := ⟨7, [0], 1, 0⟩
private def unallocated : CellId := ⟨7, [1], 1, 0⟩
private def firstKey : Key := ⟨List.replicate 16 0, by simp⟩
private def secondKey : Key := ⟨List.replicate 16 1, by simp⟩

private theorem second_ne_first : second ≠ first := by decide
private theorem secondKey_ne_firstKey : secondKey ≠ firstKey := by decide

private def firstHeap : Heap Nat Nat Nat where
  current := Function.update (fun _ => none) first (some ⟨10, .suspended⟩)
  spine := [.allocate first 10]

private def secondHeap : Heap Nat Nat Nat where
  current := Function.update firstHeap.current second (some ⟨20, .suspended⟩)
  spine := .allocate second 20 :: firstHeap.spine

private def firstAssignment : CellId → Option Key :=
  assignKey (fun _ => none) first firstKey

private def secondAssignment : CellId → Option Key :=
  assignKey firstAssignment second secondKey

private def firstIndex : Trie (CellRecord Nat Nat Nat) :=
  Trie.empty.insertKey firstKey ⟨10, .suspended⟩

private def secondIndex : Trie (CellRecord Nat Nat Nat) :=
  firstIndex.insertKey secondKey ⟨20, .suspended⟩

private theorem first_allocated :
    (Heap.empty : Heap Nat Nat Nat).allocate? first 10 = some firstHeap := rfl

private theorem second_allocated :
    firstHeap.allocate? second 20 = some secondHeap := by
  simp only [Heap.allocate?, Heap.lookup, firstHeap,
    Function.update_of_ne second_ne_first]
  rfl

private theorem first_available : KeyAvailable (fun _ => none) firstKey := by
  intro cell
  simp

private theorem second_available : KeyAvailable firstAssignment secondKey := by
  intro cell
  by_cases same : cell = first
  · subst cell
    simpa [firstAssignment] using secondKey_ne_firstKey.symm
  · simp [firstAssignment, assignKey_other _ _ _ same]

theorem two_cells_consistent : Consistent secondAssignment secondHeap secondIndex := by
  have firstConsistent : Consistent firstAssignment firstHeap firstIndex :=
    allocate_preserves_consistency empty_consistent first_available first_allocated
  exact allocate_preserves_consistency firstConsistent second_available second_allocated

theorem two_cells_unique : AssignedKeysUnique secondAssignment :=
  assignKey_preserves_unique (assignKey_preserves_unique empty_keys_unique first_available)
    second_available

theorem sibling_births_have_distinct_keys :
    secondAssignment first = some firstKey ∧ secondAssignment second = some secondKey ∧
      firstKey ≠ secondKey := by
  simp [secondAssignment, firstAssignment,
    assignKey_other _ _ _ second_ne_first.symm, secondKey_ne_firstKey.symm]

theorem unallocated_reads_none : secondHeap.lookup unallocated = none :=
  unassigned_lookup_none two_cells_consistent (by
    simp [secondAssignment, firstAssignment, assignKey,
      show unallocated ≠ first by decide, show unallocated ≠ second by decide])

theorem cache_update_preserves_two_cells :
    Consistent secondAssignment
      (secondHeap.setKnownCache first ⟨10, .suspended⟩ (.value 70))
      (secondIndex.insertKey firstKey ⟨10, .value 70⟩) :=
  setKnownCache_preserves_consistency two_cells_unique two_cells_consistent first firstKey
    sibling_births_have_distinct_keys.1 ⟨10, .suspended⟩ (.value 70)

theorem reused_key_is_unavailable : ¬ KeyAvailable firstAssignment firstKey := by
  intro available
  exact available first (assignKey_same _ _ _)

theorem collision_breaks_consistency :
    ¬ Consistent (assignKey firstAssignment second firstKey) secondHeap
      (firstIndex.insertKey firstKey ⟨20, .suspended⟩) := by
  intro consistent
  have wrong := consistent first
  have firstStill : assignKey firstAssignment second firstKey first = some firstKey := by
    rw [assignKey_other _ _ _ second_ne_first.symm]
    exact assignKey_same _ _ _
  have observed : secondHeap.lookup first = some ⟨10, .suspended⟩ := by
    simp [Heap.lookup, secondHeap, firstHeap, second_ne_first.symm]
  rw [firstStill, Option.bind_some, Trie.lookupKey_insert_self, observed] at wrong
  have impossible : (20 : Nat) = 10 := congrArg (fun record => record.origin)
    (Option.some.inj wrong)
  omega

end Controls

end Mettapedia.Machines.BranchLocalNeed.NeedHeapIndex
