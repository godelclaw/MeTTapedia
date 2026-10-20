import Mettapedia.Machines.OrderedProtocol

/-!
# HE completed-publication controls

Ordered source alternatives share their reached world. These controls
instantiate the common traversal and publication algebra, including error
priority, duplicate occurrences, and child publication before resumption.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.StateAlgebra

open Mettapedia.Machines.OrderedProtocol.Completion

/-! ## Chronology canaries -/

/-- A tiny stateful step: emit the updated counter and retain it as state. -/
private def addStep
    (increment initial : Nat) (results : List Nat) (final : Nat) : Prop :=
  results = [initial + increment] ∧ final = initial + increment

/-- Positive: the second alternative observes the state produced by the
first, so the outputs are `1` and then `3`. -/
theorem ordered_state_threads_across_alternatives :
    OrderedStateFlatMapRel addStep [1, 2] 0 [1, 3] 3 := by
  apply OrderedStateFlatMapRel.cons
      (middle := 1) (headResults := [1]) (tailResults := [3])
  · exact ⟨rfl, rfl⟩
  · apply OrderedStateFlatMapRel.cons
        (middle := 3) (headResults := [3]) (tailResults := [])
    · exact ⟨rfl, rfl⟩
    · exact .nil 3

private theorem addStep_final_state
    {increments : List Nat} {initial final : Nat} {results : List Nat}
    (run : OrderedStateFlatMapRel addStep increments initial results final) :
    final = initial + increments.sum := by
  induction run with
  | nil => simp
  | @cons increment increments initial middle final
      headResults tailResults headStep _ inductionHypothesis =>
      rcases headStep with ⟨_headResults, rfl⟩
      rw [inductionHypothesis]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Negative: interpreting sibling alternatives from the same initial state
would emit `[1, 2]` and finish at `2`; that branch-isolated behavior is not an
ordered state traversal. -/
theorem branch_isolated_state_is_rejected :
    ¬OrderedStateFlatMapRel addStep [1, 2] 0 [1, 2] 2 := by
  intro run
  have finalState := addStep_final_state run
  simp at finalState

/-- Discarding an error result retains the effects of the completed branch
that produced it, before the next branch is evaluated. -/
theorem publication_keeps_discarded_branch_state :
    PublishedTraversalRel addStep (fun value => value == 1) [1, 2] 0 [3] 3 := by
  apply PublishedTraversalRel.completed ordered_state_threads_across_alternatives
  exact .successes ⟨3, by simp, rfl⟩

theorem publication_cannot_rewind_discarded_branch :
    ¬PublishedTraversalRel addStep (fun value => value == 1) [1, 2] 0 [3] 2 := by
  intro closed
  obtain ⟨raw, traversed, _⟩ := closed.decompose
  have finalState := addStep_final_state traversed
  simp at finalState

private def priorityError (value : Nat) : Bool := value != 0

/-- A completed all-error phase publishes both physical occurrences. -/
theorem completed_errors_keep_occurrences :
    SuccessPriorityRel priorityError [1, 1] [1, 1] :=
  .allErrors (by
    intro item member
    have same : item = 1 := by simpa using member
    subst item
    rfl)

/-- Selecting successes also preserves separate equal occurrences. -/
theorem completed_successes_keep_occurrences :
    SuccessPriorityRel priorityError [0,1,0] [0,0] :=
  .successes ⟨0,by simp,rfl⟩

/-- The same error prefix does not license publication after a success has
arrived. Completion is a semantic boundary, not a prefix membership test. -/
theorem an_error_prefix_is_not_completed_failure :
    SuccessPriorityRel priorityError [1] [1] ∧
      SuccessPriorityRel priorityError [1, 0] [0] ∧
      ¬SuccessPriorityRel priorityError [1, 0] [1] := by
  have finished : SuccessPriorityRel priorityError [1, 0] [0] :=
    .successes ⟨0, by simp, rfl⟩
  refine ⟨.allErrors (by
    intro item member
    have same : item = 1 := by simpa using member
    subst item
    rfl), finished, ?_⟩
  intro falseCompletion
  have impossible := falseCompletion.functional finished
  cases impossible

/-- Filtering a child before resuming its caller differs from filtering only
after that caller fails. Tags 0, 1 and 2 are success, early error and later
error. The earlier error cannot be resurrected at the parent's boundary. -/
theorem nested_priority_cannot_be_delayed :
    let resume : Nat → List Nat := fun value => if value = 0 then [2] else [value]
    SuccessPriorityRel priorityError [0, 1] [0] ∧
      SuccessPriorityRel priorityError ([0].flatMap resume) [2] ∧
      SuccessPriorityRel priorityError ([0, 1].flatMap resume) [2, 1] ∧
      ¬SuccessPriorityRel priorityError ([0, 1].flatMap resume) [2] := by
  dsimp only
  have delayed : SuccessPriorityRel priorityError [2, 1] [2, 1] :=
    .allErrors (by intro item member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                   rcases member with rfl | rfl <;> rfl)
  refine ⟨.successes ⟨0, by simp, rfl⟩, .allErrors ?_, delayed, ?_⟩
  · intro item member
    have same : item = 2 := by simpa using member
    subst item
    rfl
  · intro lost
    have impossible := lost.functional delayed
    cases impossible

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.StateAlgebra
