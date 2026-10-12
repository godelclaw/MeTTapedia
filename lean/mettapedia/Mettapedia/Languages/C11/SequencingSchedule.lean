import Mettapedia.Languages.C11.Sequencing
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.OfMap
import Mathlib.Order.WellFounded

/-!
# Executable scheduling of finite C evaluation occurrences

An enabled occurrence has no pending sequencing predecessor. The scheduler
offers every such occurrence, retaining the original sequencing relation;
choosing one does not add edges to that relation. Its executable selection
and deletion have independent occurrence-removal rules in both directions.
Every valid nonempty finite residual has an enabled occurrence. Each
selection decreases the pending occurrence count and preserves uniqueness.

This is scheduling within a constructed finite evaluation, not termination
of C programs. Calls and loops may construct further evaluations forever.
Memory safety, operator validity and interaction admission must also hold
at the selected occurrence. The scheduling rules alone do not certify them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.SequencingSchedule

open Sequencing

universe u

def Ready {Index : Type u} (order : Order Index) (pending : List Index) (index : Index) : Prop :=
  index ∈ pending ∧ ∀ predecessor ∈ pending, ¬ order.Precedes predecessor index

def enabled {Index : Type u} (order : Order Index) (pending : List Index) (index : Index) : Bool :=
  pending.all (fun predecessor => decide (order.before predecessor index ≠ true))

def choices {Index : Type u} (order : Order Index) (pending : List Index) : List Index :=
  pending.filter (enabled order pending)

theorem mem_choices_iff {Index : Type u} (order : Order Index) (pending : List Index) (index : Index) :
    index ∈ choices order pending ↔ Ready order pending index := by
  simp only [choices, List.mem_filter, enabled, List.all_eq_true, decide_eq_true_eq, Ready, Order.Precedes]

theorem ready_exists {Index : Type u} [DecidableEq Index]
    (enumeration : Enumeration Index) (order : Order Index) (valid : order.Valid)
    (pending : List Index) (nonempty : pending ≠ []) : ∃ index, Ready order pending index := by
  let : Fintype Index := Fintype.ofList enumeration.items enumeration.complete
  let : IsTrans Index order.Precedes := ⟨valid.2⟩
  let : Std.Irrefl order.Precedes := ⟨valid.1⟩
  have wellFounded := Finite.wellFounded_of_trans_of_irrefl order.Precedes
  have inhabited : {index : Index | index ∈ pending}.Nonempty := by
    cases pending with
    | nil => exact False.elim (nonempty rfl)
    | cons head tail => exact ⟨head, by simp⟩
  obtain ⟨index, present, minimal⟩ := wellFounded.has_min {index : Index | index ∈ pending} inhabited
  exact ⟨index, present, minimal⟩

theorem choices_nonempty {Index : Type u} [DecidableEq Index]
    (enumeration : Enumeration Index) (order : Order Index) (valid : order.Valid)
    (pending : List Index) (nonempty : pending ≠ []) : choices order pending ≠ [] := by
  obtain ⟨index, ready⟩ := ready_exists enumeration order valid pending nonempty
  have present := (mem_choices_iff order pending index).mpr ready
  intro empty
  rw [empty] at present
  cases present

/-- One occurrence is removed at its actual position in the residual. -/
inductive Removal {Index : Type u} (index : Index) : List Index → List Index → Prop where
  | here (tail : List Index) : Removal index (index :: tail) tail
  | there (head : Index) (before after : List Index) (different : head ≠ index)
      (following : Removal index before after) : Removal index (head :: before) (head :: after)

theorem Removal.present {Index : Type u} {index : Index} {before after : List Index}
    (removed : Removal index before after) : index ∈ before := by
  induction removed with
  | here tail => simp
  | there head before after different following ih => exact List.mem_cons_of_mem head ih

theorem Removal.length {Index : Type u} {index : Index} {before after : List Index}
    (removed : Removal index before after) : after.length + 1 = before.length := by
  induction removed with
  | here tail => rfl
  | there head before after different following ih => simp only [List.length_cons]; omega

theorem Removal.sublist {Index : Type u} {index : Index} {before after : List Index}
    (removed : Removal index before after) : after.Sublist before := by
  induction removed with
  | here tail => exact List.Sublist.cons _ (List.Sublist.refl _)
  | there head before after different following ih => exact List.Sublist.cons_cons _ ih

theorem Removal.unique {Index : Type u} {index : Index} {before after : List Index}
    (removed : Removal index before after) (unique : before.Nodup) : after.Nodup :=
  unique.sublist removed.sublist

theorem Removal.absent {Index : Type u} {index : Index} {before after : List Index}
    (removed : Removal index before after) (unique : before.Nodup) : index ∉ after := by
  induction removed with
  | here tail => exact (List.nodup_cons.mp unique).1
  | there head before after different following ih =>
      simp only [List.mem_cons, not_or]
      exact ⟨Ne.symm different, ih (List.nodup_cons.mp unique).2⟩

theorem Removal.erase {Index : Type u} [DecidableEq Index] {index : Index} {before after : List Index}
    (removed : Removal index before after) : before.erase index = after := by
  induction removed with
  | here tail => simp
  | there head before after different following ih => simp [different, ih]

theorem removal_erase {Index : Type u} [DecidableEq Index] (index : Index) (pending : List Index)
    (present : index ∈ pending) : Removal index pending (pending.erase index) := by
  induction pending with
  | nil => cases present
  | cons head tail ih =>
      by_cases same : head = index
      · subst head
        simpa using Removal.here (index := index) tail
      · have following : index ∈ tail := by simpa [Ne.symm same] using present
        simpa [same] using Removal.there head tail (tail.erase index) same (ih following)

inductive Step {Index : Type u} (order : Order Index) : List Index → Index → List Index → Prop where
  | consume (before after : List Index) (index : Index)
      (ready : Ready order before index) (removed : Removal index before after) : Step order before index after

def select {Index : Type u} [DecidableEq Index] (order : Order Index)
    (pending : List Index) (index : Index) : Option (List Index) :=
  if index ∈ choices order pending then some (pending.erase index) else none

theorem select_sound {Index : Type u} [DecidableEq Index] (order : Order Index)
    (before after : List Index) (index : Index) (selected : select order before index = some after) :
    Step order before index after := by
  by_cases enabled : index ∈ choices order before
  · simp only [select, enabled, ↓reduceIte, Option.some.injEq] at selected
    subst after
    have ready := (mem_choices_iff order before index).mp enabled
    exact .consume _ _ index ready (removal_erase index before ready.1)
  · simp [select, enabled] at selected

theorem select_complete {Index : Type u} [DecidableEq Index] (order : Order Index)
    (before after : List Index) (index : Index) (stepped : Step order before index after) :
    select order before index = some after := by
  cases stepped with
  | consume before after ready removed =>
      simp [select, (mem_choices_iff order before index).mpr ready, removed.erase]

theorem select_iff {Index : Type u} [DecidableEq Index] (order : Order Index)
    (before after : List Index) (index : Index) :
    select order before index = some after ↔ Step order before index after :=
  ⟨select_sound order before after index, select_complete order before after index⟩

theorem selected_decreases {Index : Type u} [DecidableEq Index] (order : Order Index)
    (before after : List Index) (index : Index) (selected : select order before index = some after) :
    after.length + 1 = before.length := by
  cases select_sound order before after index selected with
  | consume before after ready removed => exact removed.length

theorem selected_unique {Index : Type u} [DecidableEq Index] (order : Order Index)
    (before after : List Index) (index : Index) (selected : select order before index = some after)
    (unique : before.Nodup) : after.Nodup ∧ index ∉ after := by
  cases select_sound order before after index selected with
  | consume before after ready removed => exact ⟨removed.unique unique, removed.absent unique⟩

theorem no_repeat {Index : Type u} [DecidableEq Index] (order : Order Index)
    (before after : List Index) (index : Index) (selected : select order before index = some after)
    (unique : before.Nodup) : select order after index = none := by
  have absent := (selected_unique order before after index selected unique).2
  have notEnabled : index ∉ choices order after := fun present => absent ((mem_choices_iff order after index).mp present).1
  simp [select, notEnabled]

theorem sequence_second_requires_first_finished {First Second : Type u}
    (first : Order First) (second : Order Second) (pending : List (First ⊕ Second))
    (right : Second) (ready : Ready (first.sequence second) pending (.inr right)) :
    ∀ left : First, .inl left ∉ pending := by
  intro left present
  exact ready.2 (.inl left) present rfl

theorem sequenceRight_first_requires_second_finished {First Second : Type u}
    (first : Order First) (second : Order Second) (pending : List (First ⊕ Second))
    (left : First) (ready : Ready (first.sequenceRight second) pending (.inl left)) :
    ∀ right : Second, .inr right ∉ pending := by
  intro right present
  exact ready.2 (.inr right) present rfl

end Mettapedia.Languages.C11.SequencingSchedule
