import Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness

/-!
# Ordered execution and exact residuals of retained HE control

Internal advances preserve the independent recursive evaluator's ordered
meaning. Publication moves one occurrence into the retained output history.
Every finite run either completes or returns its full residual configuration;
neither a stuck state nor a foreign interaction is introduced by this pure,
read-only evaluator profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveExecution

open RecursiveTasks RecursiveMachine RecursiveCorrectness
open Mettapedia.GSLT.Distinction.ProductiveBlocks

theorem next_space (dispatch : GroundedDispatch) (state after : Configuration)
    (advanced : next dispatch state = some after) : after.space = state.space := by
  cases state with
  | mk space control stack emitted =>
      cases control with
      | work task => cases advanced; rfl
      | returning results =>
          cases stack with
          | nil => simp [next] at advanced
          | cons frame remaining => cases advanced; rfl

theorem next_emitted (dispatch : GroundedDispatch) (state after : Configuration)
    (advanced : next dispatch state = some after) : after.emitted = state.emitted := by
  cases state with
  | mk space control stack emitted =>
      cases control with
      | work task => cases advanced; rfl
      | returning results =>
          cases stack with
          | nil => simp [next] at advanced
          | cons frame remaining => cases advanced; rfl

theorem next_denote (dispatch : GroundedDispatch) (state after : Configuration)
    (advanced : next dispatch state = some after) : after.denote dispatch = state.denote dispatch := by
  cases state with
  | mk space control stack emitted =>
      cases control with
      | work task =>
          cases advanced
          simp only [Configuration.denote, Configuration.remaining, List.foldl_append]
          change emitted ++ stack.foldl _ (expandedDenote space dispatch (enter space dispatch task)) = _
          rw [enter_denote]
          rfl
      | returning results =>
          cases stack with
          | nil => simp [next] at advanced
          | cons frame remaining =>
              cases advanced
              simp only [Configuration.denote, Configuration.remaining, List.foldl_append, List.foldl_cons]
              change emitted ++ remaining.foldl _ (expandedDenote space dispatch (resume space frame results)) = _
              rw [resume_denote]
              rfl

/-- Complete evaluator evidence retained across an observed finite run. -/
structure Retains (dispatch : GroundedDispatch) (before after : Configuration)
    (events : ResultSet) : Prop where
  space : after.space = before.space
  meaning : after.denote dispatch = before.denote dispatch
  history : after.emitted = before.emitted ++ events

theorem Retains.refl (dispatch : GroundedDispatch) (state : Configuration) :
    Retains dispatch state state [] := ⟨rfl, rfl, (List.append_nil _).symm⟩

theorem Retains.trans {dispatch : GroundedDispatch} {first middle last : Configuration}
    {left right : ResultSet} (before : Retains dispatch first middle left)
    (after : Retains dispatch middle last right) :
    Retains dispatch first last (left ++ right) := by
  refine ⟨after.space.trans before.space, after.meaning.trans before.meaning, ?_⟩
  rw [after.history, before.history, List.append_assoc]

theorem next_retains (dispatch : GroundedDispatch) (state after : Configuration)
    (advanced : next dispatch state = some after) : Retains dispatch state after [] := by
  refine ⟨next_space dispatch state after advanced, next_denote dispatch state after advanced, ?_⟩
  simpa using next_emitted dispatch state after advanced

/-- The outcome of this profile is completion or an exact exhausted residual. -/
def RunCorrespondence (dispatch : GroundedDispatch) (initial : Configuration) :
    ResultSet × Outcome Configuration Configuration Empty → Prop
  | (events, .exhausted residual) => Retains dispatch initial residual events
  | (events, .finished final) =>
      Retains dispatch initial final events ∧ final.control = .returning [] ∧ final.stack = []
  | _ => False

theorem run_correspondence (dispatch : GroundedDispatch) (budget : Nat) (state : Configuration) :
    RunCorrespondence dispatch state ((machine dispatch).run budget state) := by
  induction budget generalizing state with
  | zero => exact Retains.refl dispatch state
  | succ budget ih =>
      cases state with
      | mk space control stack emitted =>
          cases control with
          | work task =>
              let after : Configuration :=
                ⟨space, (enter space dispatch task).1,
                  (enter space dispatch task).2 ++ stack, emitted⟩
              have retained := next_retains dispatch
                ⟨space, .work task, stack, emitted⟩ after rfl
              have later := ih after
              simp only [Machine.run, machine, next]
              change RunCorrespondence dispatch ⟨space, .work task, stack, emitted⟩
                ((machine dispatch).run budget after)
              rcases found : (machine dispatch).run budget after with ⟨events, outcome⟩
              rw [found] at later
              cases outcome <;> simp only [RunCorrespondence] at later ⊢
              · exact ⟨by simpa using retained.trans later.1, later.2⟩
              · simpa using retained.trans later
          | returning results =>
              cases stack with
              | cons frame remaining =>
                  let after : Configuration :=
                    ⟨space, (resume space frame results).1,
                      (resume space frame results).2 ++ remaining, emitted⟩
                  have retained := next_retains dispatch
                    ⟨space, .returning results, frame :: remaining, emitted⟩ after rfl
                  have later := ih after
                  simp only [Machine.run, machine, next]
                  change RunCorrespondence dispatch ⟨space, .returning results, frame :: remaining, emitted⟩
                    ((machine dispatch).run budget after)
                  rcases found : (machine dispatch).run budget after with ⟨events, outcome⟩
                  rw [found] at later
                  cases outcome <;> simp only [RunCorrespondence] at later ⊢
                  · exact ⟨by simpa using retained.trans later.1, later.2⟩
                  · simpa using retained.trans later
              | nil =>
                  cases results with
                  | nil =>
                      exact ⟨Retains.refl dispatch _, rfl, rfl⟩
                  | cons result pending =>
                      let after : Configuration :=
                        ⟨space, .returning pending, [], emitted ++ [result]⟩
                      have retained : Retains dispatch
                          ⟨space, .returning (result :: pending), [], emitted⟩ after [result] := by
                        refine ⟨rfl, ?_, rfl⟩
                        simp [after, Configuration.denote, Configuration.remaining, Control.denote,
                          List.append_assoc]
                      have later := ih after
                      simp only [Machine.run, machine, next]
                      change RunCorrespondence dispatch
                        ⟨space, .returning (result :: pending), [], emitted⟩
                        ([result] ++ ((machine dispatch).run budget after).1,
                          ((machine dispatch).run budget after).2)
                      rcases found : (machine dispatch).run budget after with ⟨events, outcome⟩
                      rw [found] at later
                      cases outcome <;> simp only [RunCorrespondence] at later ⊢
                      · exact ⟨retained.trans later.1, later.2⟩
                      · exact retained.trans later

theorem finished_results (space : Space) (dispatch : GroundedDispatch) (task : Task)
    (budget : Nat) (events : ResultSet) (final : Configuration)
    (finished : (machine dispatch).run budget (Configuration.initial space task) =
      (events, .finished final)) :
    events = task.denote space dispatch ∧ final.emitted = events ∧ final.space = space := by
  have qualified := run_correspondence dispatch budget (Configuration.initial space task)
  rw [finished] at qualified
  rcases qualified with ⟨retained, control, stack⟩
  have history : final.emitted = events := by simpa [Configuration.initial] using retained.history
  have meaning := retained.meaning
  simp only [Configuration.denote, Configuration.remaining, control, stack,
    List.foldl_nil, Control.denote, List.append_nil] at meaning
  exact ⟨history.symm.trans meaning, history, retained.space⟩

end Mettapedia.Languages.MeTTa.HE.RecursiveExecution
