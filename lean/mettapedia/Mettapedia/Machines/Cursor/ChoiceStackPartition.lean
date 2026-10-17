import Mettapedia.Machines.Cursor.RetainedWork

/-!
# Partitioning nested alternatives without duplicating the older search

A finite pure search has a focused tree and a stack of older alternatives.
An inner fork can be externalized as two independent continuations and one
continuation for the older stack. Copying that stack into both inner branches
would repeat its answers. Equal answers remain distinct occurrences.

The tree interpreter and the small-step stack machine are separate definitions.
The transition and bounded-run laws connect them. The partition then supplies
the permutation required by retained work's route-switch law. Native binding
checkpoints, owners, effects and capture admission remain implementation
obligations; this model does not erase them or justify reordering effects.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ChoiceStackPartition

inductive Search (α : Type) where
  | empty
  | answer (value : α)
  | fork (left right : Search α)
  deriving DecidableEq

def Search.answers {α : Type} : Search α → List α
  | .empty => []
  | .answer value => [value]
  | .fork left right => left.answers ++ right.answers

structure State (α : Type) where
  focus : Search α
  older : List (Search α)
  deriving DecidableEq

variable {α : Type}

def State.answers (state : State α) : List α :=
  state.focus.answers ++ state.older.flatMap Search.answers

/-- One administrative or answering step of depth-first search. -/
def State.tick : State α → Option α × State α
  | ⟨.empty, []⟩ => (none, ⟨.empty, []⟩)
  | ⟨.empty, next :: older⟩ => (none, ⟨next, older⟩)
  | ⟨.answer value, older⟩ => (some value, ⟨.empty, older⟩)
  | ⟨.fork left right, older⟩ => (none, ⟨left, right :: older⟩)

theorem tick_answers (state : State α) :
    (state.tick).1.toList ++ (state.tick).2.answers = state.answers := by
  rcases state with ⟨focus, older⟩
  cases focus <;> cases older <;>
    simp [State.tick, State.answers, Search.answers, List.append_assoc]

def State.run : Nat → State α → List α × State α
  | 0, state => ([], state)
  | fuel + 1, state =>
      let (answer, next) := state.tick
      let (answers, rest) := next.run fuel
      (answer.toList ++ answers, rest)

/-- Every bounded slice keeps exactly the unanswered suffix. -/
theorem run_answers (fuel : Nat) (state : State α) :
    (state.run fuel).1 ++ (state.run fuel).2.answers = state.answers := by
  induction fuel generalizing state with
  | zero => simp [State.run]
  | succ fuel ih =>
      simpa only [State.run, List.append_assoc, ih] using tick_answers state

/-- Inner branches have no older alternatives. The older stack is retained
once as its own continuation, with backtracking as its next step. -/
def partition (left right : Search α) (older : List (Search α)) : List (State α) :=
  [⟨left, []⟩, ⟨right, []⟩, ⟨.empty, older⟩]

def frontierAnswers (frontier : List (State α)) : List α :=
  frontier.flatMap State.answers

theorem partition_answers (left right : Search α) (older : List (Search α)) :
    frontierAnswers (partition left right older) =
      (State.mk (.fork left right) older).answers := by
  simp [partition, frontierAnswers, State.answers, Search.answers, List.append_assoc]

/-- Scheduling the independent residuals in another order keeps their bag. -/
theorem partition_permuted (left right : Search α) (older : List (Search α))
    (scheduled : List (State α)) (order : scheduled.Perm (partition left right older)) :
    (frontierAnswers scheduled).Perm (State.mk (.fork left right) older).answers := by
  rw [← partition_answers]
  exact order.flatMap (fun _ _ => List.Perm.refl _)

theorem handoff_keeps_prefix (delivered : List α) (left right : Search α)
    (older : List (Search α)) (scheduled : List (State α))
    (order : scheduled.Perm (partition left right older)) :
    (delivered ++ frontierAnswers scheduled).Perm
      (delivered ++ (State.mk (.fork left right) older).answers) :=
  (partition_permuted left right older scheduled order).append_left delivered

/-- A partial run of every branch retains all undelivered occurrences. -/
theorem partition_slices (fuel : Nat) (left right : Search α)
    (older : List (Search α)) :
    ((partition left right older).flatMap fun state =>
      (state.run fuel).1 ++ (state.run fuel).2.answers) =
        (State.mk (.fork left right) older).answers := by
  simp only [run_answers]
  exact partition_answers left right older

namespace Controls

theorem duplicates_survive :
    frontierAnswers (partition (.answer 7) (.answer 7) [.answer 7]) = [7, 7, 7] := by
  decide

theorem copying_older_repeats_answers :
    ¬ (frontierAnswers [⟨.answer 1, [.answer 3]⟩, ⟨.answer 2, [.answer 3]⟩]).Perm
        (State.mk (.fork (.answer 1) (.answer 2)) [.answer 3]).answers := by
  decide

theorem dropping_older_loses_answers :
    ¬ (frontierAnswers [⟨.answer 1, []⟩, ⟨.answer 2, []⟩]).Perm
        (State.mk (.fork (.answer 1) (.answer 2)) [.answer 3]).answers := by
  decide

theorem scheduling_may_change_order :
    frontierAnswers [⟨.empty, [.answer 3]⟩, ⟨.answer 1, []⟩, ⟨.answer 2, []⟩] ≠
        (State.mk (.fork (.answer 1) (.answer 2)) [.answer 3]).answers := by
  decide

theorem bounded_prefix_is_not_replayed :
    (State.run 2 ⟨.fork (.answer 1) (.answer 2), [.answer 3]⟩).1 = [1] ∧
    (State.run 2 ⟨.fork (.answer 1) (.answer 2), [.answer 3]⟩).2.answers = [2, 3] := by
  decide

end Controls
end Mettapedia.Machines.Cursor.ChoiceStackPartition
