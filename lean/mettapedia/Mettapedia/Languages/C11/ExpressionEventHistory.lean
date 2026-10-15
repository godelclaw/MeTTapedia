import Mettapedia.Languages.C11.ExpressionEventExecution

/-!
# Connected expression histories and exact residual execution

Every admitted finite history of the independent occurrence rules is realized
by the executable scheduler, with the same occurrence observations and exact
semantic memory/cache endpoint. Every executable prefix constructs a connected
history. Pending occurrence count and receipt count are conserved, and an
occurrence cannot execute twice. Prefix resumption retains the original source
plan and complete memory, cache and pending state.

These are histories of constructed finite integer-expression evaluations.
Calls, loops and data-dependent branch construction require source rules that
construct their next evaluation. Finite occurrence progress does not imply
termination of arbitrary C programs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ExpressionEventHistory

open ExpressionEvents ExpressionEventExecution IntegerMemoryModel
open Mettapedia.GSLT.Distinction.ProductiveBlocks (Machine)

variable {Index : Type} {model : Model}

structure Occurrence (Index : Type) (model : Model) where
  index : Index
  outcome : Outcome model
  deriving DecidableEq, Repr

def observation (receipt : Receipt Index model) : Occurrence Index model := ⟨receipt.index, receipt.outcome⟩

inductive SemanticHistory [DecidableEq Index] (policy : SignedConversionPolicy) (plan : Plan Index model) :
    SemanticState Index model → List (Occurrence Index model) → SemanticState Index model → Prop where
  | nil (state : SemanticState Index model) : SemanticHistory policy plan state [] state
  | cons (before middle after : SemanticState Index model) (event : Occurrence Index model)
      (events : List (Occurrence Index model))
      (step : Reduction policy plan before event.index event.outcome middle)
      (following : SemanticHistory policy plan middle events after) :
      SemanticHistory policy plan before (event :: events) after

inductive History [DecidableEq Index] (policy : SignedConversionPolicy) (plan : Plan Index model) :
    State Index model → List (Receipt Index model) → State Index model → Prop where
  | nil (state : State Index model) : History policy plan state [] state
  | cons (receipt : Receipt Index model) (events : List (Receipt Index model)) (final : State Index model)
      (justified : ValidReceipt policy plan receipt)
      (following : History policy plan receipt.after events final) :
      History policy plan receipt.before (receipt :: events) final

theorem History.semantic [DecidableEq Index] {policy : SignedConversionPolicy} {plan : Plan Index model}
    {before after : State Index model} {events : List (Receipt Index model)}
    (history : History policy plan before events after) :
    SemanticHistory policy plan (represent before) (events.map observation) (represent after) := by
  induction history with
  | nil state => exact .nil _
  | cons receipt events final justified following ih => exact .cons _ _ _ _ _ justified ih

theorem history_realization [DecidableEq Index] (policy : SignedConversionPolicy) (plan : Plan Index model)
    (before after : SemanticState Index model) (events : List (Occurrence Index model))
    (history : SemanticHistory policy plan before events after)
    (actual : State Index model) (represented : represent actual = before) (rest : List Index) :
    ∃ receipts saved,
      represent saved = after ∧ receipts.map observation = events ∧ History policy plan actual receipts saved ∧
      (machine model policy).run events.length
          ⟨plan, actual, events.map Occurrence.index ++ rest⟩ =
        (receipts, .exhausted ⟨plan, saved, rest⟩) := by
  induction history generalizing actual with
  | nil state => exact ⟨[], actual, represented, rfl, .nil _, rfl⟩
  | cons before middle after event events step following ih =>
      rw [← represented] at step
      obtain ⟨saved, computed, savedRepresentation⟩ := execute_complete policy plan actual middle event.index event.outcome step
      obtain ⟨receipts, final, finalRepresentation, observations, connected, ran⟩ := ih saved savedRepresentation
      let receipt : Receipt Index model := ⟨event.index, event.outcome, actual, saved⟩
      refine ⟨receipt :: receipts, final, finalRepresentation, ?_, ?_, ?_⟩
      · simp only [List.map_cons, observation, receipt, observations]
      · exact .cons receipt receipts final (execute_sound _ _ _ _ _ _ computed) connected
      · have stepped := step_of_execute policy plan actual saved event.index
          (events.map Occurrence.index ++ rest) event.outcome computed
        simp only [List.length_cons, List.map_cons, List.cons_append]
        rw [(machine model policy).run_succ_publish stepped, ran]
        rfl

theorem History.origins [DecidableEq Index] {policy : SignedConversionPolicy} {plan : Plan Index model}
    {before after : State Index model} {events : List (Receipt Index model)}
    (history : History policy plan before events after) : ∀ receipt ∈ events, receipt.index ∈ before.pending := by
  induction history with
  | nil state => simp
  | cons receipt events final justified following ih =>
      cases justified with
      | execute _ _ _ partition continuing clean scheduled operation cached halted =>
          cases scheduled with
          | consume _ _ ready removed =>
              intro emitted present
              rcases List.mem_cons.mp present with rfl | present
              · exact ready.1
              · exact removed.sublist.subset (ih emitted present)

theorem History.account [DecidableEq Index] {policy : SignedConversionPolicy} {plan : Plan Index model}
    {before after : State Index model} {events : List (Receipt Index model)}
    (history : History policy plan before events after) :
    after.pending.length + events.length = before.pending.length := by
  induction history with
  | nil state => simp
  | cons receipt events final justified following ih =>
      cases justified with
      | execute _ _ _ partition continuing clean scheduled operation cached halted =>
          cases scheduled with
          | consume _ _ ready removed =>
              have consumed := removed.length
              change receipt.after.pending.length + 1 = receipt.before.pending.length at consumed
              simp only [List.length_cons]
              omega

theorem History.unique [DecidableEq Index] {policy : SignedConversionPolicy} {plan : Plan Index model}
    {before after : State Index model} {events : List (Receipt Index model)}
    (history : History policy plan before events after) (unique : before.pending.Nodup) :
    (events.map Receipt.index).Nodup ∧ after.pending.Nodup := by
  induction history with
  | nil state => exact ⟨by simp, unique⟩
  | cons receipt events final justified following ih =>
      cases justified with
      | execute _ _ _ partition continuing clean scheduled operation cached halted =>
          cases scheduled with
          | consume _ _ ready removed =>
              obtain ⟨laterUnique, residualUnique⟩ := ih (removed.unique unique)
              refine ⟨?_, residualUnique⟩
              simp only [List.map_cons, List.nodup_cons]
              refine ⟨?_, laterUnique⟩
              intro repeated
              obtain ⟨later, present, same⟩ := List.mem_map.mp repeated
              have pending := following.origins later present
              rw [same] at pending
              exact removed.absent unique pending

def verdictConfiguration : Verdict Index model → Configuration Index model
  | .returned _ saved | .terminal _ _ saved | .unsequenced _ _ saved | .refused saved => saved

def endpoint : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome
    (Configuration Index model) (Verdict Index model) (SelectionRequest Index) → Option (Configuration Index model)
  | .exhausted saved | .stuck saved | .suspended _ saved => some saved
  | .finished verdict => some (verdictConfiguration verdict)
  | .faulted => none

inductive StepShape [DecidableEq Index] (policy : SignedConversionPolicy)
    (configuration : Configuration Index model) :
    Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition
      (Configuration Index model) (Receipt Index model) (Verdict Index model) (SelectionRequest Index) → Prop where
  | finished (verdict : Verdict Index model) (saved : verdictConfiguration verdict = configuration) :
      StepShape policy configuration (.finish verdict)
  | suspended (request : SelectionRequest Index) : StepShape policy configuration (.call request configuration)
  | published (index : Index) (outcome : Outcome model) (after : State Index model) (rest : List Index)
      (selected : configuration.selections = index :: rest)
      (computed : execute policy configuration.plan configuration.state index = some (outcome, after)) :
      StepShape policy configuration (.publish [⟨index, outcome, configuration.state, after⟩]
        ⟨configuration.plan, after, rest⟩)

theorem machine_shape [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (configuration : Configuration Index model) :
    ∃ transition, (machine model policy).step configuration = some transition ∧ StepShape policy configuration transition := by
  cases conflict : configuration.plan.component.evaluation.findConflict configuration.plan.component.enumeration with
  | some pair =>
      rcases pair with ⟨first, second⟩
      exact ⟨.finish (.unsequenced first second configuration), by simp only [machine, conflict], .finished _ rfl⟩
  | none =>
      by_cases checked : partitionCheck configuration.plan configuration.state.pending configuration.state.cache = true
      · have base : (machine model policy).step configuration = some
          (match configuration.state.halted with
          | some (index, outcome) =>
              if outcome.terminal then .finish (.terminal index outcome configuration)
              else .finish (.refused configuration)
          | none =>
              match configuration.state.pending with
              | [] =>
                  match lookupScalar configuration.state.cache configuration.plan.component.result with
                  | some scalar => .finish (.returned scalar configuration)
                  | none => .finish (.refused configuration)
              | _ :: _ =>
                  match configuration.selections with
                  | [] => .call ⟨SequencingSchedule.choices configuration.plan.component.evaluation.order
                      configuration.state.pending⟩ configuration
                  | index :: rest =>
                      match execute policy configuration.plan configuration.state index with
                      | none => .finish (.refused configuration)
                      | some (outcome, after) => .publish [⟨index, outcome, configuration.state, after⟩]
                          ⟨configuration.plan, after, rest⟩) := by
          simp only [machine, conflict, checked, ↓reduceIte]
          rfl
        cases halted : configuration.state.halted with
        | some stopped =>
            rcases stopped with ⟨index, outcome⟩
            by_cases terminal : outcome.terminal = true
            · exact ⟨_, by simpa [halted, terminal] using base, .finished _ rfl⟩
            · exact ⟨_, by simpa [halted, terminal] using base, .finished _ rfl⟩
        | none =>
            cases pending : configuration.state.pending with
            | nil =>
                cases result : lookupScalar configuration.state.cache configuration.plan.component.result with
                | none => exact ⟨_, by simpa only [halted, pending, result] using base, .finished _ rfl⟩
                | some scalar => exact ⟨_, by simpa only [halted, pending, result] using base, .finished _ rfl⟩
            | cons head tail =>
                cases selected : configuration.selections with
                | nil => exact ⟨_, by simpa only [halted, pending, selected] using base, .suspended _⟩
                | cons index rest =>
                    cases computed : execute policy configuration.plan configuration.state index with
                    | none => exact ⟨_, by simpa only [halted, pending, selected, computed] using base, .finished _ rfl⟩
                    | some result =>
                        rcases result with ⟨outcome, after⟩
                        exact ⟨_, by simpa only [halted, pending, selected, computed] using base,
                          .published _ _ _ _ selected computed⟩
      · exact ⟨.finish (.refused configuration), by simp [machine, conflict, checked], .finished _ rfl⟩

theorem run_history [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (fuel : Nat) (initial : Configuration Index model) :
    ∃ final, endpoint ((machine model policy).run fuel initial).2 = some final ∧ final.plan = initial.plan ∧
      History policy initial.plan initial.state ((machine model policy).run fuel initial).1 final.state := by
  induction fuel generalizing initial with
  | zero => exact ⟨initial, rfl, rfl, .nil _⟩
  | succ fuel ih =>
      obtain ⟨transition, stepped, shape⟩ := machine_shape model policy initial
      cases shape with
      | finished verdict saved =>
          rw [(machine model policy).run_succ_finish stepped]
          exact ⟨initial, by simp only [endpoint, saved], rfl, .nil _⟩
      | suspended request =>
          rw [(machine model policy).run_succ_call stepped]
          exact ⟨initial, rfl, rfl, .nil _⟩
      | published index outcome after rest selected computed =>
          rw [(machine model policy).run_succ_publish stepped]
          obtain ⟨final, endState, planRetained, following⟩ := ih ⟨initial.plan, after, rest⟩
          exact ⟨final, endState, planRetained,
            .cons ⟨index, outcome, initial.state, after⟩ _ final.state
              (execute_sound _ _ _ _ _ _ computed) following⟩

theorem run_conserves_occurrences [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (fuel : Nat) (initial : Configuration Index model) :
    ∃ final, endpoint ((machine model policy).run fuel initial).2 = some final ∧ final.plan = initial.plan ∧
      final.state.pending.length + ((machine model policy).run fuel initial).1.length = initial.state.pending.length := by
  obtain ⟨final, endState, samePlan, history⟩ := run_history model policy fuel initial
  exact ⟨final, endState, samePlan, history.account⟩

theorem run_unique_occurrences [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (fuel : Nat) (initial : Configuration Index model) (unique : initial.state.pending.Nodup) :
    (((machine model policy).run fuel initial).1.map Receipt.index).Nodup := by
  obtain ⟨final, endState, samePlan, history⟩ := run_history model policy fuel initial
  exact (history.unique unique).1

theorem resume_retains_plan [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (fuel : Nat) (initial saved : Configuration Index model) (events : List (Receipt Index model))
    (paused : (machine model policy).run fuel initial = (events, .exhausted saved)) : saved.plan = initial.plan := by
  obtain ⟨final, endState, samePlan, history⟩ := run_history model policy fuel initial
  rw [paused] at endState
  have same : saved = final := Option.some.inj endState
  exact (congrArg Configuration.plan same).trans samePlan

theorem resume_no_repeat [DecidableEq Index] (model : Model) (policy : SignedConversionPolicy)
    (first second : Nat) (initial saved : Configuration Index model) (events : List (Receipt Index model))
    (unique : initial.state.pending.Nodup)
    (paused : (machine model policy).run first initial = (events, .exhausted saved)) :
    ((events ++ ((machine model policy).run second saved).1).map Receipt.index).Nodup := by
  have once := run_unique_occurrences model policy (first + second) initial unique
  rw [resume_after_prefix model policy first second initial saved events paused] at once
  exact once

end Mettapedia.Languages.C11.ExpressionEventHistory
