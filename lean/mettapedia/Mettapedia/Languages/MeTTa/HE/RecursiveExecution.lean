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

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
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

/-- Checked completion, rather than an arbitrary fuel choice, earns stability
of all six evaluator entry points and their retained list traversals. Larger
depth preserves the complete occurrence list, including equal-valued results
with different binding histories. This read-only profile does not commit host
effects. -/
theorem completed_depth_stable (space : Space) (dispatch : GroundedDispatch) (task : Task)
    (budget extra : Nat) (events : ResultSet) (final : Configuration)
    (completed : (Checked.machine dispatch).run budget (Configuration.initial space task) =
      (events, .finished final)) :
    (task.replenish extra).denote space dispatch = task.denote space dispatch := by
  have original := (finished_results space dispatch task budget events final
    (Checked.finished_refines dispatch budget _ _ _ completed)).1
  have larger := Checked.completed_deepen dispatch extra budget
    (Configuration.initial space task) final events completed
  rw [Configuration.deepen_initial] at larger
  have increased := (finished_results space dispatch (task.replenish extra) budget events
    (final.deepen extra) larger).1
  exact increased.symm.trans original

/-- Completion provides an eventual constant evaluator observation at the
current depth. The certificate is the actual checked execution, with no
assumed source-to-machine correspondence in its premises. -/
theorem completed_atom_depth_stable (space : Space) (dispatch : GroundedDispatch)
    (value expected : Atom) (bindings : Bindings) (live : List Atom)
    (depth budget : Nat) (events : ResultSet) (final : Configuration)
    (completed : (Checked.machine dispatch).run budget
      (Configuration.initial space (.atom value expected bindings depth live)) =
        (events, .finished final)) :
    ∀ extra, evalAtom space dispatch value expected bindings (depth + extra) live = events := by
  intro extra
  have stable := completed_depth_stable space dispatch
    (.atom value expected bindings depth live) budget extra events final completed
  have original := (finished_results space dispatch (.atom value expected bindings depth live)
    budget events final (Checked.finished_refines dispatch budget _ _ _ completed)).1
  exact stable.trans original.symm

/-- Draining a completed result list publishes each physical occurrence once,
in order, and appends it to the receiver's existing history. -/
theorem checked_drain_results (space : Space) (dispatch : GroundedDispatch)
    (results history : ResultSet) :
    (Checked.machine dispatch).run (results.length + 1)
      ⟨space, .returning results, [], history⟩ =
      (results, .finished ⟨space, .returning [], [], history ++ results⟩) := by
  induction results generalizing history with
  | nil =>
      simp [Machine.run, Checked.machine, Checked.guardMachine, Checked.blocked,
        RecursiveMachine.machine, next, Transition.relabel]
  | cons result remaining ih =>
      simpa [Machine.run, Checked.machine, Checked.guardMachine, Checked.blocked,
        RecursiveMachine.machine, next, Transition.relabel, List.append_assoc] using
        congrArg (fun run : ResultSet × Outcome Configuration Configuration Checked.ResourceRequest =>
          ([result] ++ run.1, run.2)) (ih (history ++ [result]))

/-- Local matcher coverage suffices for complete checked primitive unification.
The budget is constructed from the actual full result list, including equal
occurrences. No evaluator termination or desired-output premise is used. -/
theorem checked_unify_results (space : Space) (dispatch : GroundedDispatch)
    (target pattern yes no : Atom) (bindings : Bindings) (fuel : Nat)
    (live : List Atom) (caller : Option Atom)
    (covered : unifyMatchesCovered target pattern bindings fuel = true) :
    let results := minimalStep space dispatch
      (.expression [.symbol "unify", target, pattern, yes, no]) bindings (fuel + 1) live caller
    (Checked.machine dispatch).run (results.length + 2)
      (Configuration.initial space (.primitive
        (.expression [.symbol "unify", target, pattern, yes, no]) bindings (fuel + 1) live caller)) =
      (results, .finished ⟨space, .returning [], [], results⟩) := by
  dsimp only
  rw [show (minimalStep space dispatch
      (.expression [.symbol "unify", target, pattern, yes, no]) bindings (fuel + 1) live caller).length + 2 =
      ((minimalStep space dispatch
      (.expression [.symbol "unify", target, pattern, yes, no]) bindings (fuel + 1) live caller).length + 1) + 1 by omega]
  rw [Machine.run_succ_silent (Checked.machine dispatch)
    (next := ⟨space, .returning (minimalStep space dispatch
      (.expression [.symbol "unify", target, pattern, yes, no]) bindings (fuel + 1) live caller), [], []⟩) (by
    simp [Configuration.initial, Checked.machine, Checked.guardMachine, Checked.blocked,
      Checked.taskReady, minimalCoreSupported, covered, RecursiveMachine.machine, next,
      enter, minimalStep, Transition.relabel])]
  simpa using checked_drain_results space dispatch
    (minimalStep space dispatch (.expression [.symbol "unify", target, pattern, yes, no])
      bindings (fuel + 1) live caller) []

end Mettapedia.Languages.MeTTa.HE.RecursiveExecution
