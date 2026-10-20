import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Enum

/-!
# Residual collections for matching and contextual reduction

A bag selection consumes one occurrence. A set selection may consume its selected
member or retain it: a set containing `a` also represents a collection containing
two copies of `a`. The second branch is required both for repeated pattern
variables and for rewriting modulo idempotence.

The executable residuals below are characterized against permutation for bags
and membership equality for sets. Set completeness assumes a duplicate-free
carrier, as supplied by canonicalization. It permits any presentation of the
residual and returns an equivalent representative.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionSelection

universe u
variable {α : Type u}

/-- Extensional equality of finite set presentations. -/
def SameMembers (left right : List α) : Prop :=
  ∀ item, item ∈ left ↔ item ∈ right

theorem SameMembers.refl (items : List α) : SameMembers items items := fun _ => Iff.rfl

theorem SameMembers.symm {left right : List α} (same : SameMembers left right) :
    SameMembers right left := fun item => (same item).symm

theorem SameMembers.trans {first second third : List α}
    (firstSecond : SameMembers first second) (secondThird : SameMembers second third) :
    SameMembers first third := fun item => (firstSecond item).trans (secondThird item)

/-- Residual candidates at a known selected occurrence. The caller checks that
the index is in range. `idempotent = false` gives ordinary bag consumption. -/
def residuals (idempotent : Bool) (items : List α) (selected : Nat) : List (List α) :=
  if idempotent then [items.eraseIdx selected, items] else [items.eraseIdx selected]

/-- A choice retains its source index and whether its selected occurrence was
kept in the residual. This distinguishes the two set contexts. -/
structure Choice (α : Type u) where
  selected : Nat
  value : α
  residual : List α
  retained : Bool
  deriving DecidableEq, Repr

/-- Enumerate only in-range choices, retaining occurrence indices for bags. -/
def choices (idempotent : Bool) (items : List α) : List (Choice α) :=
  items.zipIdx.flatMap fun (item, index) =>
    let consumed : Choice α := ⟨index, item, items.eraseIdx index, false⟩
    if idempotent then [consumed, ⟨index, item, items, true⟩] else [consumed]

theorem bag_residuals (items : List α) (selected : Nat) :
    residuals false items selected = [items.eraseIdx selected] := rfl

theorem set_residuals (items : List α) (selected : Nat) :
    residuals true items selected = [items.eraseIdx selected, items] := rfl

/-- Bag residuals account for exactly one selected occurrence, modulo order. -/
theorem bag_residuals_exact {items rest : List α} {selected : Nat}
    (within : selected < items.length) :
    (∃ actual ∈ residuals false items selected, actual.Perm rest) ↔
      items.Perm (items[selected] :: rest) := by
  have split := List.getElem_cons_eraseIdx_perm within
  simp only [residuals, Bool.false_eq_true, ↓reduceIte, List.mem_singleton, exists_eq_left]
  constructor
  · intro same
    exact split.symm.trans (same.cons _)
  · intro same
    exact (split.trans same).cons_inv

private theorem selected_split {items : List α} {selected : Nat}
    (within : selected < items.length) (item : α) :
    item ∈ items ↔ item = items[selected] ∨ item ∈ items.eraseIdx selected := by
  simpa only [List.mem_cons] using (List.getElem_cons_eraseIdx_perm within).mem_iff.symm

/-- Each set residual reconstructs the original set when the selected member
is put back, including the branch which retained it. -/
theorem set_residuals_sound {items rest : List α} {selected : Nat}
    (within : selected < items.length) (member : rest ∈ residuals true items selected) :
    SameMembers items (items[selected] :: rest) := by
  simp only [residuals, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · intro item
    simpa only [List.mem_cons] using selected_split within item
  · intro item
    simp only [List.mem_cons]
    constructor
    · exact Or.inr
    · rintro (rfl | member)
      · exact List.getElem_mem within
      · exact member

/-- Every residual satisfying the independent set equation is represented by
one of the two choices. Overlap with the selected member is allowed. -/
theorem set_residuals_complete {items rest : List α} {selected : Nat}
    (distinct : items.Nodup) (within : selected < items.length)
    (covers : SameMembers items (items[selected] :: rest)) :
    ∃ actual ∈ residuals true items selected, SameMembers actual rest := by
  classical
  by_cases retained : items[selected] ∈ rest
  · refine ⟨items, by simp [residuals], ?_⟩
    intro item
    have covered := covers item
    simp only [List.mem_cons] at covered
    constructor
    · intro member
      rcases covered.mp member with rfl | member
      · exact retained
      · exact member
    · intro member
      exact covered.mpr (.inr member)
  · refine ⟨items.eraseIdx selected, by simp [residuals], ?_⟩
    have erasedDistinct := (List.getElem_cons_eraseIdx_perm within).nodup_iff.mpr distinct
    have removed : items[selected] ∉ items.eraseIdx selected := (List.nodup_cons.mp erasedDistinct).1
    intro item
    constructor
    · intro member
      have inSource := List.mem_of_mem_eraseIdx member
      rcases List.mem_cons.mp ((covers item).mp inSource) with same | inRest
      · exact False.elim (removed (same ▸ member))
      · exact inRest
    · intro member
      have inSource := (covers item).mpr (List.mem_cons_of_mem _ member)
      rcases (selected_split within item).mp inSource with same | inErased
      · exact False.elim (retained (same ▸ member))
      · exact inErased

theorem set_residuals_exact {items rest : List α} {selected : Nat}
    (distinct : items.Nodup) (within : selected < items.length) :
    (∃ actual ∈ residuals true items selected, SameMembers actual rest) ↔
      SameMembers items (items[selected] :: rest) := by
  constructor
  · rintro ⟨actual, member, same⟩ item
    have reconstructed := set_residuals_sound within member item
    simpa only [List.mem_cons, same item] using reconstructed
  · exact set_residuals_complete distinct within

/-- Enumerate the values assigned to a fixed number of collection-pattern
positions, together with their residual. The recursion is on the number of
positions, including when a set choice retains its selected member. -/
def allocations (idempotent : Bool) : Nat → List α → List (List α × List α)
  | 0, items => [([], items)]
  | count + 1, items =>
      items.zipIdx.flatMap fun (item, index) =>
        (residuals idempotent items index).flatMap fun rest =>
          (allocations idempotent count rest).map fun (selected, final) =>
            (item :: selected, final)

theorem allocations_cons_iff {idempotent : Bool} {count : Nat}
    {items selected rest : List α} {head : α} :
    (head :: selected, rest) ∈ allocations idempotent (count + 1) items ↔
      ∃ index, ∃ within : index < items.length, items[index] = head ∧
        ∃ intermediate ∈ residuals idempotent items index,
          (selected, rest) ∈ allocations idempotent count intermediate := by
  simp only [allocations, List.mem_flatMap, List.exists_mem_zipIdx', List.mem_map]
  constructor
  · rintro ⟨index, within, intermediate, member, ⟨tail, final⟩, allocated, same⟩
    have equal := Prod.mk.inj same
    have heads := List.cons.inj equal.1
    dsimp at equal heads
    exact ⟨index, within, heads.1, intermediate, member, by simpa [heads.2, equal.2] using allocated⟩
  · rintro ⟨index, within, same, intermediate, member, allocated⟩
    exact ⟨index, within, intermediate, member, (selected, rest), allocated, by simp [same]⟩

/-- Set allocation covers precisely the original members; a selected value
may occur repeatedly and may also occur in the residual. -/
theorem set_allocations_sound {count : Nat} {items selected rest : List α}
    (member : (selected, rest) ∈ allocations true count items) :
    selected.length = count ∧ SameMembers items (selected ++ rest) := by
  induction count generalizing items selected rest with
  | zero =>
      simp only [allocations, List.mem_singleton, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩
      exact ⟨rfl, SameMembers.refl _⟩
  | succ count ih =>
      cases selected with
      | nil =>
          simp only [allocations, List.mem_flatMap, List.mem_map,
            Prod.mk.injEq, List.cons_ne_nil, false_and, exists_false, and_false] at member
      | cons head selected =>
          obtain ⟨index, within, same, intermediate, residual, tail⟩ :=
            allocations_cons_iff.mp member
          obtain ⟨length, covered⟩ := ih tail
          refine ⟨by simp [length], ?_⟩
          intro item
          have one := set_residuals_sound within residual item
          simpa only [List.mem_cons, List.cons_append, covered item, same] using one

theorem residuals_nodup {idempotent : Bool} {items rest : List α} {index : Nat}
    (distinct : items.Nodup) (member : rest ∈ residuals idempotent items index) :
    rest.Nodup := by
  cases idempotent <;> simp only [residuals, Bool.false_eq_true, ↓reduceIte,
    List.mem_cons, List.not_mem_nil, or_false] at member
  · subst rest
    exact distinct.sublist (List.eraseIdx_sublist ..)
  · rcases member with rfl | rfl
    · exact distinct.sublist (List.eraseIdx_sublist ..)
    · exact distinct

/-- All solutions of the set coverage equation have an executable allocation.
Only the residual representation may differ; the ordered selected values are
preserved exactly, including repeated values. -/
theorem set_allocations_complete {items selected rest : List α}
    (distinct : items.Nodup) (covers : SameMembers items (selected ++ rest)) :
    ∃ actual, (selected, actual) ∈ allocations true selected.length items ∧
      SameMembers actual rest := by
  induction selected generalizing items with
  | nil =>
      exact ⟨items, by simp [allocations], covers⟩
  | cons head selected ih =>
      have headIn : head ∈ items := (covers head).mpr (by simp)
      obtain ⟨index, within, same⟩ := List.mem_iff_getElem.mp headIn
      have one : SameMembers items (items[index] :: (selected ++ rest)) := by
        simpa only [same, List.cons_append] using covers
      obtain ⟨intermediate, residual, covered⟩ := set_residuals_complete distinct within one
      obtain ⟨actual, allocated, sameRest⟩ := ih (residuals_nodup distinct residual) covered
      refine ⟨actual, ?_, sameRest⟩
      exact allocations_cons_iff.mpr ⟨index, within, same, intermediate, residual, allocated⟩

theorem set_allocations_exact {items selected rest : List α}
    (distinct : items.Nodup) :
    (∃ actual, (selected, actual) ∈ allocations true selected.length items ∧
      SameMembers actual rest) ↔ SameMembers items (selected ++ rest) := by
  constructor
  · rintro ⟨actual, allocated, same⟩ item
    have covered := (set_allocations_sound allocated).2 item
    simpa only [List.mem_append, same item] using covered
  · exact set_allocations_complete distinct

/-- Bag allocation preserves the full multiset, including repeated values. -/
theorem bag_allocations_sound {count : Nat} {items selected rest : List α}
    (member : (selected, rest) ∈ allocations false count items) :
    selected.length = count ∧ items.Perm (selected ++ rest) := by
  induction count generalizing items selected rest with
  | zero =>
      simp only [allocations, List.mem_singleton, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩
      exact ⟨rfl, List.Perm.refl _⟩
  | succ count ih =>
      cases selected with
      | nil =>
          simp only [allocations, List.mem_flatMap, List.mem_map, Prod.mk.injEq,
            List.cons_ne_nil, false_and, exists_false, and_false] at member
      | cons head selected =>
          obtain ⟨index, within, same, intermediate, residual, tail⟩ :=
            allocations_cons_iff.mp member
          obtain ⟨length, permutation⟩ := ih tail
          refine ⟨by simp [length], ?_⟩
          have one := bag_residuals_exact within |>.mp ⟨intermediate, residual, permutation⟩
          simpa only [same, List.cons_append] using one

/-- Every multiset allocation is enumerated, with its residual represented
in source order. Duplicate source values need no distinctness hypothesis. -/
theorem bag_allocations_complete {items selected rest : List α}
    (covers : items.Perm (selected ++ rest)) :
    ∃ actual, (selected, actual) ∈ allocations false selected.length items ∧ actual.Perm rest := by
  induction selected generalizing items with
  | nil => exact ⟨items, by simp [allocations], covers⟩
  | cons head selected ih =>
      have headIn : head ∈ items := covers.mem_iff.mpr (by simp)
      obtain ⟨index, within, same⟩ := List.mem_iff_getElem.mp headIn
      have one : items.Perm (items[index] :: (selected ++ rest)) := by
        simpa only [same, List.cons_append] using covers
      obtain ⟨intermediate, residual, covered⟩ := bag_residuals_exact within |>.mpr one
      obtain ⟨actual, allocated, sameRest⟩ := ih covered
      exact ⟨actual, allocations_cons_iff.mpr
        ⟨index, within, same, intermediate, residual, allocated⟩, sameRest⟩

theorem bag_allocations_exact {items selected rest : List α} :
    (∃ actual, (selected, actual) ∈ allocations false selected.length items ∧ actual.Perm rest) ↔
      items.Perm (selected ++ rest) := by
  constructor
  · rintro ⟨actual, allocated, same⟩
    exact (bag_allocations_sound allocated).2.trans ((List.Perm.refl selected).append same)
  · exact bag_allocations_complete

/-- The empty target offers no selection even in the idempotent case. -/
example : choices true ([] : List Nat) = [] := by decide

/-- A singleton set has a consuming context and a context retaining a copy. -/
example : (choices true [7]).map (·.residual) = [[], [7]] := by decide

/-- A singleton bag has only the consuming context. -/
example : (choices false [7]).map (·.residual) = [[]] := by decide

/-- Equal bag values still have two independently selected occurrences. -/
example : (choices false [7, 7]).map (·.selected) = [0, 1] := by decide

/-- Two set-pattern variables may both select the same singleton member. -/
example : ([7, 7], []) ∈ allocations true 2 [7] := by decide

/-- A rest variable may also retain that same member. -/
example : ([7, 7], [7]) ∈ allocations true 2 [7] := by decide

/-- Bag matching cannot use a single occurrence twice. -/
example : ([7, 7], []) ∉ allocations false 2 [7] := by decide

/-- Removing an unrelated element cannot satisfy the set reconstruction law. -/
example : ¬ SameMembers [7, 8] (7 :: ([] : List Nat)) := by
  intro same
  have := (same 8).mp (by simp)
  simp at this

end Mettapedia.OSLF.MeTTaIL.CollectionSelection
