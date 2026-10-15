import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCertified

/-!
# Readout cursors on suspended scoped matching

A consumer reads only unconsumed emitted answers and still-pending structural
work. Advancing a cursor distinguishes an actual selected receipt from the
remaining alternatives. Embedded matching preserves this denotation when the
consumer has reached the current end of its emitted list.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine

theorem mem_drop_cursor_iff {α : Type} (items : List α) (cursor : Nat) (item : α) :
    item ∈ items.drop cursor ↔ items[cursor]? = some item ∨ item ∈ items.drop (cursor + 1) := by
  induction items generalizing cursor with
  | nil => simp
  | cons head tail ih =>
      cases cursor with
      | zero => simp [eq_comm]
      | succ cursor => simpa only [List.drop_succ_cons, List.getElem?_cons_succ, Nat.succ_add] using ih cursor

def MatcherUnread (request : Request) (state : State) (cursor : Nat) (answer : Answer) : Prop :=
  answer ∈ state.answers.drop cursor ∨ ∃ work ∈ state.agenda, WorkAccepts request work answer

theorem unread_cursor_split (request : Request) (state : State) (cursor : Nat) (answer : Answer) :
    MatcherUnread request state cursor answer ↔ state.answers[cursor]? = some answer ∨
      MatcherUnread request state (cursor + 1) answer := by
  unfold MatcherUnread
  rw [mem_drop_cursor_iff]
  exact or_assoc

theorem start_unread_iff (request : Request) (answer : Answer) :
    MatcherUnread request (start request) 0 answer ↔ answer.Valid request :=
  start_accepts_iff request answer

theorem unread_at_end_iff (request : Request) (state : State) (answer : Answer) :
    MatcherUnread request state state.answers.length answer ↔
      ∃ work ∈ state.agenda, WorkAccepts request work answer := by
  simp only [MatcherUnread, List.drop_length, List.not_mem_nil, false_or]

theorem unread_tick_of_no_answer (request : Request) (state : State) (cursor : Nat) (answer : Answer)
    (bounded : cursor ≤ state.answers.length) (unavailable : state.answers[cursor]? = none) :
    MatcherUnread request (tick request state) cursor answer ↔ MatcherUnread request state cursor answer := by
  have atEnd : cursor = state.answers.length := by
    have beyond := List.getElem?_eq_none_iff.mp unavailable
    omega
  subst cursor
  rw [unread_at_end_iff]
  cases agendaEq : state.agenda with
  | nil => simp only [tick, agendaEq, MatcherUnread, List.drop_length,
      List.not_mem_nil, false_or, false_and, exists_false]
  | cons work agenda =>
    cases tasksEq : work.tasks with
    | nil =>
      simp only [tick, agendaEq, tasksEq, MatcherUnread]
      rw [List.drop_append_of_le_length (Nat.le_refl _), List.drop_length]
      simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (same | later)
        · exact ⟨work, .inl rfl, (workAccepts_nil_iff tasksEq).mpr same⟩
        · obtain ⟨branch, member, accepted⟩ := later
          exact ⟨branch, .inr member, accepted⟩
      · rintro ⟨branch, (same | later), accepted⟩
        · subst branch
          exact .inl ((workAccepts_nil_iff tasksEq).mp accepted)
        · exact .inr ⟨branch, later, accepted⟩
    | cons task tasks =>
      simp only [tick, agendaEq, tasksEq, MatcherUnread, List.drop_length,
        List.not_mem_nil, false_or]
      have pending : work.tasks ≠ [] := by rw [tasksEq]; exact List.cons_ne_nil _ _
      constructor
      · rintro ⟨branch, member, accepted⟩
        rcases List.mem_append.mp member with generated | later
        · exact ⟨work, List.mem_cons_self,
            (advance_accepts_iff request work answer pending).mp ⟨branch, generated, accepted⟩⟩
        · exact ⟨branch, List.mem_cons_of_mem _ later, accepted⟩
      · rintro ⟨branch, member, accepted⟩
        rcases List.mem_cons.mp member with same | later
        · subst branch
          obtain ⟨generated, member, accepted⟩ :=
            (advance_accepts_iff request work answer pending).mpr accepted
          exact ⟨generated, List.mem_append_left _ member, accepted⟩
        · exact ⟨branch, List.mem_append_right _ later, accepted⟩

end Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine
