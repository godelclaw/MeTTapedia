import Mettapedia.Languages.C11.StatementMachine

/-!
# Finite source histories and actual statement-machine endpoints

An independently judged history can contain arbitrarily many loop iterations
and expressions of arbitrary depth. Its executable realization retains the
same control, memory meaning, cache and choice suffix. Every exhausted run has
a source history with exactly one source transition per consumed machine tick.
Visible events remain ordered occurrences, including expression boundaries
and loop iterations. These finite laws do not imply program termination.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.StatementHistory

open IntegerMemoryModel LocatedStatements
open StatementExecution StatementMachine
open Mettapedia.GSLT.Distinction.ProductiveBlocks (Machine)

variable {model : Model}

inductive History (policy : SignedConversionPolicy) : SemanticConfiguration model →
    List (Option (Event model)) → SemanticConfiguration model → Prop where
  | nil (state : SemanticConfiguration model) : History policy state [] state
  | cons (before middle after : SemanticConfiguration model) (event : Option (Event model))
      (events : List (Option (Event model))) (stepped : StatementSemantics.Step policy before event middle)
      (following : History policy middle events after) : History policy before (event :: events) after

theorem history_realization (policy : SignedConversionPolicy) (before after : SemanticConfiguration model)
    (events : List (Option (Event model))) (history : History policy before events after)
    (initial : Configuration model) (represented : represent initial = before) :
    ∃ saved receipts, represent saved = after ∧
      (machine model policy).run events.length initial = (receipts, .exhausted saved) ∧
      receipts.map Receipt.event = events.filterMap id := by
  induction history generalizing initial with
  | nil state => exact ⟨initial, [], represented, rfl, rfl⟩
  | cons before middle after event events stepped following ih =>
      have independent : StatementSemantics.Step policy (represent initial) event middle := by
        rw [represented]
        exact stepped
      obtain ⟨next, computed, representedNext⟩ := execute_complete _ _ _ _ independent
      obtain ⟨saved, receipts, representedFinal, run, observations⟩ := ih next representedNext
      cases event with
      | none =>
          refine ⟨saved, receipts, representedFinal, ?_, ?_⟩
          · rw [List.length_cons, (machine model policy).run_succ_silent
              (step_of_execute _ _ _ _ computed), run]
          · simpa only [List.filterMap_cons, id_eq] using observations
      | some event =>
          refine ⟨saved, ⟨event, initial, next⟩ :: receipts, representedFinal, ?_, ?_⟩
          · rw [List.length_cons, (machine model policy).run_succ_publish
              (step_of_execute _ _ _ _ computed), run]
            rfl
          · simp only [List.map_cons, List.filterMap_cons, id_eq, observations]

theorem exhausted_has_source_history (policy : SignedConversionPolicy) (fuel : Nat)
    (initial saved : Configuration model) (receipts : List (Receipt model))
    (paused : (machine model policy).run fuel initial = (receipts, .exhausted saved)) :
    ∃ events, History policy (represent initial) events (represent saved) ∧
      events.length = fuel ∧ receipts.map Receipt.event = events.filterMap id := by
  induction fuel generalizing initial receipts with
  | zero =>
      have same : [] = receipts ∧ initial = saved := by
        simpa only [Machine.run, Prod.mk.injEq,
          Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome.exhausted.injEq] using paused
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨[], .nil _, rfl, rfl⟩
  | succ fuel ih =>
      cases computed : execute policy initial with
      | none =>
          cases classified : classify initial with
          | silent next => exact False.elim (classify_not_silent _ _ classified)
          | publish events next => exact False.elim (classify_not_publish _ _ _ classified)
          | fail events => exact False.elim (classify_not_fail _ _ classified)
          | finish verdict | call request next => simp [Machine.run, machine, computed, classified] at paused
      | some result =>
          rcases result with ⟨event, next⟩
          have independent := execute_sound _ _ _ _ computed
          cases event with
          | none =>
              have following : (machine model policy).run fuel next = (receipts, .exhausted saved) := by
                simpa only [Machine.run, machine, computed] using paused
              obtain ⟨events, history, length, observations⟩ := ih next receipts following
              exact ⟨none :: events, .cons _ _ _ _ _ independent history,
                by simp only [List.length_cons, length], by
                  simpa only [List.filterMap_cons, id_eq] using observations⟩
          | some event =>
              rcases child : (machine model policy).run fuel next with ⟨remaining, outcome⟩
              rw [(machine model policy).run_succ_publish (step_of_execute _ _ _ _ computed), child] at paused
              have equal : [⟨event, initial, next⟩] ++ remaining = receipts ∧ outcome = .exhausted saved := by
                simpa only [Prod.mk.injEq] using paused
              have ending : outcome = .exhausted saved := equal.2
              have following : (machine model policy).run fuel next = (remaining, .exhausted saved) := by
                rw [child, ending]
              obtain ⟨events, history, length, observations⟩ := ih next remaining following
              refine ⟨some event :: events, .cons _ _ _ _ _ independent history, ?_, ?_⟩
              · simp only [List.length_cons, length]
              · rw [← equal.1]
                simp only [List.singleton_append, List.map_cons, List.filterMap_cons, id_eq, observations]

theorem history_append (policy : SignedConversionPolicy) (before middle after : SemanticConfiguration model)
    (first second : List (Option (Event model))) (firstHistory : History policy before first middle)
    (suffix : History policy middle second after) : History policy before (first ++ second) after := by
  induction firstHistory with
  | nil => exact suffix
  | cons before intermediate middle event rest stepped following ih =>
      exact .cons _ _ _ _ _ stepped (ih suffix)

end Mettapedia.Languages.C11.StatementHistory
