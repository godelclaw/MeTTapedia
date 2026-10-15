import Mettapedia.Data.Fin.OptionSequence
import Mathlib.Data.List.Basic

/-!
# Compiling a finite family of lookups to list positions

Each required value is assigned its first matching list position. Compilation
fails if any value is absent. The resulting positions remain valid when both
the list and requirements are mapped. Recompiling after a noninjective map
can choose different positions, so compiled positions must be retained when
occurrence identity matters.

`compileIndexed` is the complementary declaration-table construction: each
row retains its source position, even when an earlier row is refused. Its
lookup theorem identifies the exact source row and compiler result.
-/

set_option autoImplicit false

namespace List

universe u v
variable {α : Type u} {β : Type v} {k : Nat}

/-- A physical occurrence in an ordered flat map is addressed by the length
of preceding rows and its position within the selected row. -/
theorem getElem?_flatMap_occurrence (f : α → List β) (entries : List α)
    (row : Fin entries.length) (branch : Nat)
    (bounded : branch < (f entries[row]).length) :
    (entries.flatMap f)[((entries.take row.val).flatMap f).length + branch]? =
      (f entries[row])[branch]? := by
  induction entries with
  | nil => exact Fin.elim0 row
  | cons entry rest ih =>
      obtain ⟨row, rowBounded⟩ := row
      cases row with
      | zero =>
          simp only [Fin.getElem_fin, getElem_cons_zero] at bounded ⊢
          simpa only [take_zero, flatMap_nil, length_nil, Nat.zero_add, flatMap_cons,
            getElem_cons_zero] using getElem?_append_left bounded
      | succ row =>
          have tailBounded : row < rest.length := by simpa using rowBounded
          simp only [Fin.getElem_fin, getElem_cons_succ] at bounded ⊢
          have tail := ih ⟨row, tailBounded⟩ bounded
          simp only [Fin.getElem_fin] at tail
          simp only [take_succ_cons, flatMap_cons, length_append, Nat.add_assoc]
          rw [getElem?_append_right (by omega)]
          simpa only [Nat.add_sub_cancel_left] using tail

/-- Every successful global ordinal decomposes into actual bounded row and
branch ordinals. Equal values in different rows are not identified. -/
theorem getElem?_flatMap_decompose (f : α → List β) (entries : List α)
    (ordinal : Nat) (value : β)
    (selected : (entries.flatMap f)[ordinal]? = some value) :
    ∃ (row : Fin entries.length) (branch : Nat),
      branch < (f entries[row]).length ∧
      ordinal = ((entries.take row.val).flatMap f).length + branch ∧
      (f entries[row])[branch]? = some value := by
  induction entries generalizing ordinal with
  | nil => simp at selected
  | cons entry rest ih =>
      rw [flatMap_cons] at selected
      by_cases inHead : ordinal < (f entry).length
      · refine ⟨⟨0, by simp⟩, ordinal, inHead, by simp, ?_⟩
        simpa only [Fin.getElem_fin, getElem_cons_zero, getElem?_append_left inHead] using selected
      · have beyond : (f entry).length ≤ ordinal := by omega
        rw [getElem?_append_right beyond] at selected
        obtain ⟨row, branch, bounded, offset, found⟩ := ih (ordinal - (f entry).length) selected
        refine ⟨⟨row.val + 1, by simp only [length_cons]; omega⟩, branch, ?_, ?_, ?_⟩
        · simpa only [Fin.getElem_fin, getElem_cons_succ] using bounded
        · simp only [take_succ_cons, flatMap_cons, length_append]
          omega
        · simpa only [Fin.getElem_fin, getElem_cons_succ] using found

/-- The physical row and branch positions are uniquely recoverable from a
global ordinal. This is uniqueness of positions, not uniqueness of payloads. -/
theorem flatMap_occurrence_ordinals_unique (f : α → List β) (entries : List α)
    (first second : Fin entries.length) (left right : Nat)
    (leftBounded : left < (f entries[first]).length)
    (rightBounded : right < (f entries[second]).length)
    (same : ((entries.take first.val).flatMap f).length + left =
      ((entries.take second.val).flatMap f).length + right) :
    first = second ∧ left = right := by
  induction entries with
  | nil => exact Fin.elim0 first
  | cons entry rest ih =>
      obtain ⟨first, firstBounded⟩ := first
      obtain ⟨second, secondBounded⟩ := second
      cases first with
      | zero =>
          cases second with
          | zero =>
              exact ⟨rfl, by simpa using same⟩
          | succ second =>
              simp only [Fin.getElem_fin, getElem_cons_zero] at leftBounded
              simp only [take_zero, flatMap_nil, length_nil, Nat.zero_add,
                take_succ_cons, flatMap_cons, length_append] at same
              omega
      | succ first =>
          cases second with
          | zero =>
              simp only [Fin.getElem_fin, getElem_cons_zero] at rightBounded
              simp only [take_zero, flatMap_nil, length_nil, Nat.zero_add,
                take_succ_cons, flatMap_cons, length_append] at same
              omega
          | succ second =>
              have firstTail : first < rest.length := by simpa using firstBounded
              have secondTail : second < rest.length := by simpa using secondBounded
              have sameTail : ((rest.take first).flatMap f).length + left =
                  ((rest.take second).flatMap f).length + right := by
                simp only [take_succ_cons, flatMap_cons, length_append] at same
                omega
              obtain ⟨rowEq, branchEq⟩ := ih ⟨first, firstTail⟩ ⟨second, secondTail⟩
                (by simpa using leftBounded) (by simpa using rightBounded) sameTail
              have valuesEq := congrArg Fin.val rowEq
              exact ⟨by apply Fin.ext; simpa using congrArg Nat.succ valuesEq, branchEq⟩

/-- Relocate a bounded row occurrence to its physical position in the complete
flat map. Equal payloads retain different positions. -/
def flatMapIndex (f : α → List β) (entries : List α)
    (occurrence : (row : Fin entries.length) × Fin (f entries[row]).length) :
    Fin (entries.flatMap f).length :=
  ⟨((entries.take occurrence.1.val).flatMap f).length + occurrence.2.val, by
    have selected := getElem?_flatMap_occurrence f entries occurrence.1
      occurrence.2.val occurrence.2.isLt
    rw [getElem?_eq_getElem occurrence.2.isLt] at selected
    exact (getElem?_eq_some_iff.mp selected).1⟩

@[simp] theorem flatMapIndex_val (f : α → List β) (entries : List α)
    (occurrence : (row : Fin entries.length) × Fin (f entries[row]).length) :
    (flatMapIndex f entries occurrence).val =
      ((entries.take occurrence.1.val).flatMap f).length + occurrence.2.val := rfl

theorem getElem_flatMapIndex (f : α → List β) (entries : List α)
    (occurrence : (row : Fin entries.length) × Fin (f entries[row]).length) :
    (entries.flatMap f)[flatMapIndex f entries occurrence] =
      (f entries[occurrence.1])[occurrence.2] := by
  have selected := getElem?_flatMap_occurrence f entries occurrence.1
    occurrence.2.val occurrence.2.isLt
  rw [getElem?_eq_getElem occurrence.2.isLt] at selected
  exact (getElem?_eq_some_iff.mp selected).2

theorem flatMapIndex_injective (f : α → List β) (entries : List α) :
    Function.Injective (flatMapIndex f entries) := by
  rintro ⟨first, left⟩ ⟨second, right⟩ same
  have position := congrArg Fin.val same
  obtain ⟨rows, branches⟩ := flatMap_occurrence_ordinals_unique f entries first second
    left.val right.val left.isLt right.isLt position
  subst second
  have branch : left = right := Fin.ext branches
  subst right
  rfl

theorem flatMapIndex_surjective (f : α → List β) (entries : List α) :
    Function.Surjective (flatMapIndex f entries) := by
  intro position
  obtain ⟨row, branch, bounded, offset, _⟩ := getElem?_flatMap_decompose f entries
    position.val (entries.flatMap f)[position]
    (getElem?_eq_getElem position.isLt)
  exact ⟨⟨row, ⟨branch, bounded⟩⟩, Fin.ext offset.symm⟩

/-- Every physical position has one row address and one bounded local address.
The inverse recovers positions even when row values are duplicated. -/
noncomputable def flatMapIndexEquiv (f : α → List β) (entries : List α) :
    ((row : Fin entries.length) × Fin (f entries[row]).length) ≃
      Fin (entries.flatMap f).length :=
  Equiv.ofBijective (flatMapIndex f entries)
    ⟨flatMapIndex_injective f entries, flatMapIndex_surjective f entries⟩

/-- Compile an ordered inventory to explicit indices. Refused rows leave
holes; later successful rows keep their original positions. -/
def compileIndexed (compile : α → Option β) : List α → (start : Nat := 0) → List (Nat × β)
  | [], _ => []
  | entry :: rest, start =>
      match compile entry with
      | none => compileIndexed compile rest (start + 1)
      | some value => (start, value) :: compileIndexed compile rest (start + 1)

theorem lookup_compileIndexed_below (compile : α → Option β) (entries : List α)
    (start key : Nat) (below : key < start) :
    (compileIndexed compile entries start).lookup key = none := by
  induction entries generalizing start with
  | nil => rfl
  | cons entry rest ih =>
      have belowTail : key < start + 1 := by omega
      have different : start ≠ key := by omega
      have unequal : (key == start) = false := by simp [Ne.symm different]
      cases compiled : compile entry with
      | none => simpa only [compileIndexed, compiled] using ih (start + 1) belowTail
      | some value =>
          simp only [compileIndexed, compiled, lookup_cons, unequal]
          exact ih (start + 1) belowTail

/-- An explicit indexed table has exactly the source inventory's partial
lookup, including unsuccessful compilation and out-of-range requests. -/
theorem lookup_compileIndexed (compile : α → Option β) (entries : List α)
    (start index : Nat) :
    (compileIndexed compile entries start).lookup (start + index) =
      entries[index]?.bind compile := by
  induction entries generalizing start index with
  | nil => simp [compileIndexed]
  | cons entry rest ih =>
      cases index with
      | zero =>
          cases compiled : compile entry with
          | none =>
              simpa [compileIndexed, compiled] using
                lookup_compileIndexed_below compile rest (start + 1) start (by omega)
          | some value => simp [compileIndexed, compiled]
      | succ index =>
          have position : start + (index + 1) = (start + 1) + index := by omega
          have unequal : ((start + 1) + index == start) = false := by simp; omega
          cases compiled : compile entry with
          | none => simpa only [compileIndexed, compiled, List.getElem?_cons_succ,
                position] using ih (start + 1) index
          | some value =>
              simp only [compileIndexed, compiled, position, lookup_cons, unequal,
                List.getElem?_cons_succ]
              exact ih (start + 1) index

theorem lookup_compileIndexed_zero (compile : α → Option β) (entries : List α) (index : Nat) :
    (compileIndexed compile entries).lookup index = entries[index]?.bind compile := by
  simpa using lookup_compileIndexed compile entries 0 index

theorem compileIndexed_key_ge (compile : α → Option β) (entries : List α)
    (start : Nat) {row : Nat × β} (member : row ∈ compileIndexed compile entries start) :
    start ≤ row.1 := by
  induction entries generalizing start with
  | nil => simp [compileIndexed] at member
  | cons entry rest ih =>
      cases found : compile entry with
      | none =>
          have lower := ih (start + 1) (by simpa [compileIndexed, found] using member)
          omega
      | some value =>
          simp only [compileIndexed, found, mem_cons] at member
          rcases member with rfl | member
          · exact Nat.le_refl _
          · have lower := ih (start + 1) member
            omega

theorem mem_compileIndexed_value (compile : α → Option β) (entries : List α)
    (start : Nat) {row : Nat × β} (member : row ∈ compileIndexed compile entries start) :
    ∃ entry ∈ entries, compile entry = some row.2 := by
  induction entries generalizing start with
  | nil => simp [compileIndexed] at member
  | cons entry rest ih =>
      cases found : compile entry with
      | none =>
          obtain ⟨source, belongs, compiled⟩ := ih (start + 1)
            (by simpa [compileIndexed, found] using member)
          exact ⟨source, mem_cons_of_mem _ belongs, compiled⟩
      | some value =>
          simp only [compileIndexed, found, mem_cons] at member
          rcases member with rfl | member
          · exact ⟨entry, by simp, found⟩
          · obtain ⟨source, belongs, compiled⟩ := ih (start + 1) member
            exact ⟨source, mem_cons_of_mem _ belongs, compiled⟩

/-- Explicit source positions are unique even when compilation leaves holes. -/
theorem compileIndexed_keys_nodup (compile : α → Option β) (entries : List α)
    (start : Nat := 0) : (compileIndexed compile entries start).map Prod.fst |>.Nodup := by
  induction entries generalizing start with
  | nil => simp [compileIndexed]
  | cons entry rest ih =>
      cases found : compile entry with
      | none => simpa [compileIndexed, found] using ih (start + 1)
      | some value =>
          simp only [compileIndexed, found, map_cons, nodup_cons]
          refine ⟨?_, ih (start + 1)⟩
          intro member
          obtain ⟨row, belongs, same⟩ := mem_map.mp member
          have lower := compileIndexed_key_ge compile rest (start + 1) belongs
          omega

/-- Unique association keys make row reversal preserve lookup. -/
theorem lookup_reverse_of_nodup_keys (entries : List (Nat × β))
    (unique : (entries.map Prod.fst).Nodup) (key : Nat) :
    entries.reverse.lookup key = entries.lookup key := by
  induction entries with
  | nil => rfl
  | cons row rest ih =>
      rcases row with ⟨index, value⟩
      obtain ⟨absent, distinct⟩ := nodup_cons.mp (by simpa only [map_cons] using unique)
      have tail := ih distinct
      have missing : rest.lookup index = none := by
        apply lookup_eq_none_iff.mpr
        intro row member
        have different : index ≠ row.1 := fun same =>
          absent (mem_map.mpr ⟨row, member, same.symm⟩)
        simpa using different
      by_cases same : key = index
      · subst key
        simp [reverse_cons, lookup_append, tail, missing]
      · have unequal : (key == index) = false := by simp; omega
        simp [reverse_cons, lookup_append, tail, lookup_cons, unequal]

theorem lookup_compileIndexed_reverse (compile : α → Option β) (entries : List α)
    (key : Nat) :
    (compileIndexed compile entries).reverse.lookup key = entries[key]?.bind compile := by
  rw [lookup_reverse_of_nodup_keys _ (compileIndexed_keys_nodup compile entries),
    lookup_compileIndexed_zero]

example : (compileIndexed (fun n : Nat => if n = 0 then none else some (n + 1)) [7, 0, 9]).lookup 2 =
    some 10 := by decide

example : (compileIndexed (fun n : Nat => if n = 0 then none else some (n + 1)) [7, 0, 9]).lookup 1 =
    none := by decide

/-- Reversing a search is harmless when every matching entry has the same
    value. This compares values, without identifying their occurrences. -/
theorem find?_reverse_of_unique_matches (entries : List α) (p : α → Bool)
    (unique : ∀ a ∈ entries, ∀ b ∈ entries, p a = true → p b = true → a = b) :
    entries.reverse.find? p = entries.find? p := by
  induction entries with
  | nil => rfl
  | cons first rest ih =>
      have tail := ih (fun a ma b mb => unique a (mem_cons_of_mem first ma)
        b (mem_cons_of_mem first mb))
      rw [reverse_cons, find?_append, tail]
      by_cases head : p first = true
      · cases found : rest.find? p with
        | none => simp [head]
        | some chosen =>
            have same := unique chosen (mem_cons_of_mem first (mem_of_find?_eq_some found))
              first mem_cons_self (find?_some found) head
            cases same
            simp [head]
      · simp [head]

variable [DecidableEq α]

def findPositions (entries : List α) (required : Fin k → α) : Option (Fin k → Nat) :=
  Fin.sequenceOption k (fun index => entries.findIdx? (fun entry => decide (entry = required index)))

theorem findPositions_getElem? {entries : List α} {required : Fin k → α}
    {positions : Fin k → Nat} (compiled : findPositions entries required = some positions)
    (index : Fin k) : entries[positions index]? = some (required index) := by
  have located := Fin.sequenceOption_sound k compiled index
  have selected := List.of_findIdx?_eq_some located
  cases found : entries[positions index]? with
  | none => simp [found] at selected
  | some entry =>
      simp only [found, decide_eq_true_eq] at selected
      simp only [selected]

theorem findPositions_isSome_iff (entries : List α) (required : Fin k → α) :
    (findPositions entries required).isSome = true ↔ ∀ index, required index ∈ entries := by
  rw [findPositions, Fin.sequenceOption_isSome_iff]
  simp only [List.findIdx?_isSome, List.any_eq_true, decide_eq_true_eq]
  constructor
  · intro found index
    obtain ⟨entry, member, same⟩ := found index
    simpa only [same] using member
  · intro present index
    exact ⟨required index, present index, rfl⟩

/-- Mapping preserves the compiled occurrences, without an injectivity
hypothesis and without running the position search again. -/
theorem findPositions_map_getElem? {entries : List α} {required : Fin k → α}
    {positions : Fin k → Nat} (compiled : findPositions entries required = some positions)
    (f : α → β) (index : Fin k) :
    (entries.map f)[positions index]? = some (f (required index)) := by
  rw [List.getElem?_map, findPositions_getElem? compiled index, Option.map_some]

theorem findPositions_retains_first_duplicate :
    (findPositions [4, 9, 4] (fun _ : Fin 1 => 4)).map (fun positions => positions 0) = some 0 := by
  decide +kernel

theorem findPositions_missing_rejected :
    findPositions [4, 9, 4] (fun index : Fin 2 => if index = 0 then 4 else 7) = none := by
  decide +kernel

theorem noninjective_map_changes_recompiled_position :
    (findPositions [1, 2] (fun _ : Fin 1 => 2)).map (fun positions => positions 0) = some 1 ∧
    (findPositions ([1, 2].map fun _ => 0) (fun _ : Fin 1 => 0)).map
      (fun positions => positions 0) = some 0 := by
  decide +kernel

/-- Empty rows do not collapse the ordinals of later duplicate payloads. -/
theorem flatMap_duplicate_occurrences :
    let entries := [[7, 7], [], [7, 7]]
    (entries.flatMap id)[3]? = some 7 ∧
      ((entries.take 2).flatMap id).length + 1 = 3 ∧
      (entries[2]? >>= fun row => row[1]?) = some 7 := by
  decide +kernel

/-- Equal payloads can have different ordinals; their equality cannot justify
identifying the corresponding derivation occurrences. -/
theorem flatMap_payload_equality_does_not_identify_occurrences :
    ([7, 7] : List Nat)[0]? = ([7, 7] : List Nat)[1]? ∧ (0 : Nat) ≠ 1 := by
  decide +kernel

#print axioms getElem?_flatMap_occurrence
#print axioms getElem?_flatMap_decompose
#print axioms flatMap_occurrence_ordinals_unique
#print axioms getElem_flatMapIndex
#print axioms flatMapIndex_injective
#print axioms flatMapIndex_surjective
#print axioms flatMapIndexEquiv
#print axioms findPositions_getElem?
#print axioms findPositions_isSome_iff
#print axioms findPositions_map_getElem?
#print axioms noninjective_map_changes_recompiled_position

end List
