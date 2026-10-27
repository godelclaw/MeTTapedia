import Mettapedia.Algorithms.Compression.FramedTree

/-!
# Source-variable inventories and fresh reconstruction

This is a source-observation codec, not another binding calculus. Expressions
retain all children, including quotation and binder syntax. Variable identities
are represented by a form-local inventory, independently of display names.
The inventory closes the quoted source value: its internal variables are not
logical variables of the enclosing host value.

Reconstruction with a fresh injective assignment preserves every occurrence
and alias. Capture-avoiding transformations *inside* a binder still belong to
the existing scoped-term/matcher development; no such permission is inferred
from merely capturing its source tree.
-/

namespace Mettapedia.Algorithms.Compression.SourceFrame

open KolmogorovComplexity

inductive Term (Variable : Type) where
  | var : Variable → Term Variable
  | literal : BinString → BinString → Term Variable
  | expr : List (Term Variable) → Term Variable
  deriving Repr

variable {V W : Type}

mutual
def occurrences : Term V → List V
  | .var value => [value]
  | .literal _ _ => []
  | .expr children => occurrencesList children

def occurrencesList : List (Term V) → List V
  | [] => []
  | head :: tail => occurrences head ++ occurrencesList tail
end

def rename (mapping : V → W) : Term V → Term W
  | .var value => .var (mapping value)
  | .literal kind payload => .literal kind payload
  | .expr children => .expr (children.map (rename mapping))

mutual
def restore (assignment : Nat → Option V) : Term Nat → Option (Term V)
  | .var index => (assignment index).map .var
  | .literal kind payload => some (.literal kind payload)
  | .expr children => (restoreList assignment children).map .expr

def restoreList (assignment : Nat → Option V) : List (Term Nat) → Option (List (Term V))
  | [] => some []
  | head :: tail => do
      let value ← restore assignment head
      let rest ← restoreList assignment tail
      pure (value :: rest)
end

mutual
/-- Actual restoration after encoding follows the supplied assignment on every
source variable; no reconstruction premise is assumed. -/
theorem restore_rename (code : V → Nat) (assignment : Nat → Option W) (mapping : V → W) :
    ∀ (source : Term V),
      (∀ value ∈ occurrences source, assignment (code value) = some (mapping value)) →
      restore assignment (rename code source) = some (rename mapping source)
  | .var value, reads => by simp [rename, restore, reads value (by simp [occurrences])]
  | .literal kind payload, _ => by simp [rename, restore]
  | .expr children, reads => by
      simp only [rename, restore]
      rw [restoreList_rename code assignment mapping children reads]
      rfl

theorem restoreList_rename (code : V → Nat) (assignment : Nat → Option W) (mapping : V → W) :
    ∀ (sources : List (Term V)),
      (∀ value ∈ occurrencesList sources, assignment (code value) = some (mapping value)) →
      restoreList assignment (sources.map (rename code)) = some (sources.map (rename mapping))
  | [], _ => rfl
  | head :: tail, reads => by
      have first := restore_rename code assignment mapping head
        (fun value present => reads value (by simp [occurrencesList, present]))
      have rest := restoreList_rename code assignment mapping tail
        (fun value present => reads value (by simp [occurrencesList, present]))
      simp [restoreList, first, rest]
end

theorem rename_id (source : Term V) : rename id source = source := by
  induction source using Term.rec
    (motive_2 := fun children => children.map (rename id) = children) with
  | var value => simp [rename]
  | literal kind payload => simp [rename]
  | expr children ih => simp only [rename, ih]
  | nil => rfl
  | cons head tail first rest => simp only [List.map_cons, first, rest]

theorem occurrences_rename (mapping : V → W) (source : Term V) :
    occurrences (rename mapping source) = (occurrences source).map mapping := by
  induction source using Term.rec
    (motive_2 := fun children => occurrencesList (children.map (rename mapping)) =
      (occurrencesList children).map mapping) with
  | var value => simp [rename, occurrences]
  | literal kind payload => simp [rename, occurrences]
  | expr children ih => simpa only [rename, occurrences] using ih
  | nil => rfl
  | cons head tail first rest => simp only [List.map_cons, occurrencesList, first, rest, List.map_append]

def inventory [DecidableEq V] (source : Term V) : List V :=
  (occurrences source).eraseDups

def freeze [DecidableEq V] (source : Term V) : Term Nat :=
  rename (fun value => (inventory source).idxOf value) source

def declarations [DecidableEq V] {Name : Type} (presentation : V → Name) (source : Term V) : List Name :=
  (inventory source).map presentation

/-- A reference restore may reuse the original identities. Production restore
uses the fresh version below instead of serializing process-local identifiers. -/
theorem restore_freeze [DecidableEq V] (source : Term V) :
    restore (fun index => (inventory source)[index]?) (freeze source) = some source := by
  have result := restore_rename (fun value => (inventory source).idxOf value)
    (fun index => (inventory source)[index]?) id source
    (fun value present => List.getElem?_idxOf (by simpa [inventory] using present))
  simpa only [freeze, rename_id] using result

/-- Reconstruction allocates a new identity for each inventory entry while
preserving the entire source expression and its variable relationships. -/
theorem restore_fresh [DecidableEq V] (mapping : V → W) (source : Term V) :
    restore (fun index => ((inventory source).map mapping)[index]?) (freeze source) =
      some (rename mapping source) := by
  apply restore_rename
  intro value present
  rw [List.getElem?_map, List.getElem?_idxOf (by simpa [inventory] using present)]
  rfl

theorem fresh_alias_iff (mapping : V → W) (fresh : Function.Injective mapping) (left right : V) :
    mapping left = mapping right ↔ left = right :=
  fresh.eq_iff

/-- Display names are charged inventory data, not the equality keys used for
variable aliasing. Two identities may therefore have the same presentation. -/
theorem declarations_length [DecidableEq V] {Name : Type} (presentation : V → Name) (source : Term V) :
    (declarations presentation source).length = (inventory source).length := by
  simp [declarations]

theorem restored_occurrences [DecidableEq V] (mapping : V → W) (source : Term V) :
    (restore (fun index => ((inventory source).map mapping)[index]?) (freeze source)).map occurrences =
      some ((occurrences source).map mapping) := by
  rw [restore_fresh]
  simp only [Option.map_some, occurrences_rename]

private def two : Term Bool := .expr [.var false, .var true, .var false]

private theorem inventory_two : inventory two = [false, true] := by decide

example : declarations (fun _ => "x") two = ["x", "x"] := by decide

example : restore (fun index => [7, 8][index]?) (freeze two) =
    some (.expr [.var 7, .var 8, .var 7]) := by
  unfold freeze
  rw [inventory_two]
  simp [two, rename, restore, restoreList, List.idxOf_cons]

/-- Reusing one identity for different inventory entries loses information. -/
example : restore (fun index => [7, 7][index]?) (freeze two) =
    some (.expr [.var 7, .var 7, .var 7]) := by
  unfold freeze
  rw [inventory_two]
  simp [two, rename, restore, restoreList, List.idxOf_cons]

example : restore (fun _ => none) (.var 0) = (none : Option (Term Nat)) := by rfl

end Mettapedia.Algorithms.Compression.SourceFrame
