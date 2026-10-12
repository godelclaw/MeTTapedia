import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceLocalCompletion
import Mettapedia.OSLF.NativeTypes.Decision.Stream

/-!
# Suspended work for the actual local occurrence machine

Each pause advances one retained engine task. Each yield transfers one
ordered, proof-bearing occurrence without repeating earlier execution.
Accessibility and the finite expansion forest occur only in propositions;
starting the stream constructs neither the forest nor an exhaustive budget.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier.LocalEquationFree.Suspended

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open GeneralPremise.Scheduler (TaskForest)
open Mettapedia.OSLF.NativeTypes.Decision.Scheduling (Stream)

structure Cursor (request : Request) where
  state : State request
  index : Nat
  restricted : LocalAgenda request state.agenda
  finite : Nonempty (TaskForest (localExpansion request) state.agenda)

def Cursor.readNext {request : Request} (cursor : Cursor request) : Cursor request :=
  {cursor with index := cursor.index + 1}

def Cursor.tickNext {request : Request} (cursor : Cursor request) : Cursor request where
  state := tick request cursor.state
  index := cursor.index
  restricted := tick_local request cursor.state cursor.restricted
  finite := by
    obtain ⟨forest⟩ := cursor.finite
    exact ⟨advanceForest request cursor.state cursor.restricted forest⟩

inductive Progress (request : Request) : Cursor request → Cursor request → Prop where
  | read (cursor : Cursor request) (answer : Answer request)
      (found : cursor.state.answers[cursor.index]? = some answer) :
      Progress request cursor.readNext cursor
  | tick (cursor : Cursor request)
      (missing : cursor.state.answers[cursor.index]? = none)
      (pending : cursor.state.agenda ≠ []) : Progress request cursor.tickNext cursor

theorem accessible_from_forest (request : Request) (cursor : Cursor request)
    (forest : TaskForest (localExpansion request) cursor.state.agenda) :
    Acc (Progress request) cursor := by
  refine Acc.intro cursor ?_
  intro next step
  cases step with
  | read cursor answer found =>
      have within := (List.getElem?_eq_some_iff.mp found).1
      have decreased : cursor.state.answers.length - (cursor.index + 1) <
          cursor.state.answers.length - cursor.index := by omega
      exact accessible_from_forest request cursor.readNext forest
  | tick cursor missing pending =>
      have decreased := advanceForest_cost request cursor.state cursor.restricted forest pending
      exact accessible_from_forest request cursor.tickNext
        (advanceForest request cursor.state cursor.restricted forest)
termination_by (forest.cost, cursor.state.answers.length - cursor.index)
decreasing_by
  all_goals simp only [Cursor.readNext, Cursor.tickNext, Prod.lex_def]
  · exact Or.inr ⟨trivial, decreased⟩
  · exact Or.inl (by omega)

theorem Cursor.accessible {request : Request} (cursor : Cursor request) :
    Acc (Progress request) cursor := by
  obtain ⟨forest⟩ := cursor.finite
  exact accessible_from_forest request cursor forest

instance cursorWellFounded {request : Request} : WellFoundedRelation (Cursor request) where
  rel := Progress request
  wf := ⟨Cursor.accessible⟩

def fromCursor {request : Request} (cursor : Cursor request) : Stream (Answer request) :=
  match _found : cursor.state.answers[cursor.index]? with
  | some answer => .yield answer fun _ => fromCursor cursor.readNext
  | none => if _pending : cursor.state.agenda = [] then .done
    else .pause fun _ => fromCursor cursor.tickNext
termination_by cursor
decreasing_by
  · exact Progress.read cursor answer _found
  · exact Progress.tick cursor _found _pending

theorem fromCursor_eq {request : Request} (cursor : Cursor request) :
    fromCursor cursor =
      match _found : cursor.state.answers[cursor.index]? with
      | some answer => .yield answer fun _ => fromCursor cursor.readNext
      | none => if _pending : cursor.state.agenda = [] then .done
        else .pause fun _ => fromCursor cursor.tickNext := by
  rw [fromCursor]

private theorem final_found {request : Request} (cursor : Cursor request) (fuel : Nat)
    (answer : Answer request) (found : cursor.state.answers[cursor.index]? = some answer) :
    (GeneralOccurrenceFrontier.run request fuel cursor.state).answers[cursor.index]? = some answer := by
  obtain ⟨extra, equal⟩ := answers_prefix request fuel cursor.state
  rw [equal, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

theorem cursor_readouts {request : Request} (cursor : Cursor request)
    (forest : TaskForest (localExpansion request) cursor.state.agenda)
    :
    (fromCursor cursor).flatten =
        (GeneralOccurrenceFrontier.run request forest.cost cursor.state).answers.drop cursor.index ∧
      (fromCursor cursor).workBound = forest.cost +
        ((GeneralOccurrenceFrontier.run request forest.cost cursor.state).answers.drop cursor.index).length := by
  rw [fromCursor_eq]
  split
  · rename_i answer found
    have within := (List.getElem?_eq_some_iff.mp found).1
    have decreased : cursor.state.answers.length - (cursor.index + 1) <
        cursor.state.answers.length - cursor.index := by omega
    have child := cursor_readouts cursor.readNext forest
    have after := final_found cursor forest.cost answer found
    have drop : (GeneralOccurrenceFrontier.run request forest.cost cursor.state).answers.drop cursor.index =
        answer :: (GeneralOccurrenceFrontier.run request forest.cost cursor.state).answers.drop (cursor.index + 1) := by
      have within := (List.getElem?_eq_some_iff.mp after).1
      have value := (List.getElem?_eq_some_iff.mp after).2
      rw [List.drop_eq_getElem_cons within, value]
    change (Stream.yield answer _).flatten = _ ∧ (Stream.yield answer _).workBound = _
    simp only [Stream.flatten, Stream.workBound, Cursor.readNext] at child ⊢
    rw [child.1, child.2, drop]
    simp only [List.length_cons]
    exact ⟨trivial, by omega⟩
  · rename_i missing
    split
    · rename_i idle
      have forestCost : forest.cost = 0 := by
        let emptyForest : TaskForest (localExpansion request) [] := idle ▸ forest
        have equal : emptyForest.cost = forest.cost := by
          simp only [emptyForest, TaskForest.cost_cast]
        have zero : emptyForest.cost = 0 := by cases emptyForest; rfl
        exact equal.symm.trans zero
      have absent := List.getElem?_eq_none_iff.mp missing
      rw [run_idle request forest.cost cursor.state idle, List.drop_eq_nil_of_le absent, forestCost]
      exact ⟨rfl, rfl⟩
    · rename_i pending
      let childForest : TaskForest (localExpansion request) cursor.tickNext.state.agenda :=
        advanceForest request cursor.state cursor.restricted forest
      have cost := advanceForest_cost request cursor.state cursor.restricted forest pending
      change childForest.cost + 1 = forest.cost at cost
      have decreased : childForest.cost < forest.cost := by omega
      have child := cursor_readouts cursor.tickNext childForest
      have runSame : GeneralOccurrenceFrontier.run request childForest.cost cursor.tickNext.state =
          GeneralOccurrenceFrontier.run request forest.cost cursor.state := by
        rw [← cost]
        rfl
      change (Stream.pause _).flatten = _ ∧ (Stream.pause _).workBound = _
      simp only [Stream.flatten, Stream.workBound] at ⊢
      rw [runSame] at child
      change (fromCursor cursor.tickNext).flatten =
          (GeneralOccurrenceFrontier.run request forest.cost cursor.state).answers.drop cursor.index ∧
        (fromCursor cursor.tickNext).workBound = childForest.cost +
          ((GeneralOccurrenceFrontier.run request forest.cost cursor.state).answers.drop cursor.index).length at child
      exact ⟨child.1, by rw [child.2]; omega⟩
termination_by (forest.cost, cursor.state.answers.length - cursor.index)
decreasing_by
  · simp only [Cursor.readNext, Prod.lex_def]
    exact Or.inr ⟨trivial, decreased⟩
  · simp only [Prod.lex_def]
    exact Or.inl decreased

def initial {request : Request} (empty : request.plan.equations = [])
    (checked : sourceChecked request = true) : Cursor request where
  state := tick request (start request)
  index := 0
  restricted := first_tick_local empty checked
  finite := ⟨(first_tick_agenda empty checked).symm ▸ remainingForest request⟩

def stream (request : Request) (empty : request.plan.equations = []) : Stream (Answer request) :=
  if checked : sourceChecked request = true then
    .pause fun _ => fromCursor (initial empty checked)
  else .done

theorem stream_readouts (request : Request) (empty : request.plan.equations = []) :
    (stream request empty).flatten = (run request (workBound request)).answers ∧
      (stream request empty).workBound = workBound request +
        (run request (workBound request)).answers.length := by
  unfold stream
  split
  · rename_i checked
    let cursor := initial empty checked
    let forest : TaskForest (localExpansion request) cursor.state.agenda :=
      (first_tick_agenda empty checked).symm ▸ remainingForest request
    have result := cursor_readouts cursor forest
    have cost : forest.cost = (remainingForest request).cost := by
      exact TaskForest.cost_cast (first_tick_agenda empty checked).symm (remainingForest request)
    have runSame : GeneralOccurrenceFrontier.run request forest.cost cursor.state =
        run request (workBound request) := by
      rw [cost]
      simp only [run, workBound, checked, if_true, cursor, initial, GeneralOccurrenceFrontier.run]
    change (fromCursor cursor).flatten =
        (GeneralOccurrenceFrontier.run request forest.cost cursor.state).answers ∧
      (fromCursor cursor).workBound = forest.cost +
        (GeneralOccurrenceFrontier.run request forest.cost cursor.state).answers.length at result
    rw [runSame] at result
    change (fromCursor cursor).flatten = _ ∧ 1 + (fromCursor cursor).workBound = _
    exact ⟨result.1, by rw [result.2, cost]; simp only [workBound, checked, if_true]; omega⟩
  · rename_i rejected
    simp only [run, workBound, if_neg rejected, GeneralOccurrenceFrontier.run, start,
      Stream.flatten, Stream.workBound, List.length_nil]
    exact ⟨trivial, trivial⟩

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier.LocalEquationFree.Suspended
