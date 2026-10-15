import Mettapedia.Languages.C11.StatementExecution

/-!
# Retained statement machine, faults and productive resumption

The machine retains the actual memory, expression packet, choice suffix and
structured continuation. Full-expression boundaries and loop iterations are
distinct events. Scheduling requests suspend without consuming an occurrence.
Terminal expression observations propagate with the complete saved state;
unsequenced conflicts are reported before expression execution can commit.

The byte-memory admission profile does not classify every possible C fault.
A refused occurrence or malformed residual is therefore distinct from a
proved source unsequenced conflict or an exact terminal arithmetic outcome.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.StatementMachine

open IntegerMemoryModel LocatedExpressions ExpressionEvents LocatedStatements
open LocatedExpressionData (IndexData encodeIndex)
open StatementExecution
open Mettapedia.GSLT.Distinction.ProductiveBlocks (Machine Transition)

variable {model : Model}

structure Receipt (model : Model) where
  event : Event model
  before : Configuration model
  after : Configuration model

inductive Verdict (model : Model) where
  | returned (value : Option (IntegerScalar.Value model.parameters)) (saved : Configuration model)
  | fallthrough (saved : Configuration model)
  | invalidControl (flow : Flow) (saved : Configuration model)
  | terminal (expression : Expression model) (index : IndexData) (outcome : Outcome model)
      (saved : Configuration model)
  | unsequenced (expression : Expression model) (first second : IndexData) (saved : Configuration model)
  | refused (saved : Configuration model)

structure SelectionRequest (model : Model) where
  expression : Expression model
  enabled : List IndexData

def classify (configuration : Configuration model) :
    Transition (Configuration model) (Receipt model) (Verdict model) (SelectionRequest model) :=
  match configuration with
  | .returned value _ _ => .finish (.returned value configuration)
  | .flow .normal .stop _ _ => .finish (.fallthrough configuration)
  | .flow flow .stop _ _ => .finish (.invalidControl flow configuration)
  | .expression expression saved _ selections =>
      match (compile expression).component.evaluation.findConflict (compile expression).component.enumeration with
      | some (first, second) => .finish (.unsequenced expression (encodeIndex expression first)
          (encodeIndex expression second) configuration)
      | none => if ExpressionEventExecution.partitionCheck (compile expression) saved.pending saved.cache then
          match saved.halted with
          | some (index, outcome) => if outcome.terminal then
              .finish (.terminal expression (encodeIndex expression index) outcome configuration)
              else .finish (.refused configuration)
          | none => match saved.pending, selections with
              | _ :: _, [] => .call ⟨expression,
                  (SequencingSchedule.choices (compile expression).component.evaluation.order saved.pending).map
                    (encodeIndex expression)⟩ configuration
              | _, _ => .finish (.refused configuration)
        else .finish (.refused configuration)
  | _ => .finish (.refused configuration)

theorem classify_not_silent (configuration next : Configuration model)
    (computed : classify configuration = .silent next) : False := by
  cases configuration <;> simp only [classify] at computed <;>
    repeat first | split at computed | contradiction

theorem classify_not_publish (configuration next : Configuration model) (events : List (Receipt model))
    (computed : classify configuration = .publish events next) : False := by
  cases configuration <;> simp only [classify] at computed <;>
    repeat first | split at computed | contradiction

theorem classify_not_fail (configuration : Configuration model) (events : List (Receipt model))
    (computed : classify configuration = .fail events) : False := by
  cases configuration <;> simp only [classify] at computed <;>
    repeat first | split at computed | contradiction

def machine (model : Model) (policy : SignedConversionPolicy) :
    Machine (Configuration model) (Receipt model) (Verdict model) (SelectionRequest model) where
  step configuration := some <|
    match execute policy configuration with
    | none => classify configuration
    | some (none, next) => .silent next
    | some (some event, next) => .publish [⟨event, configuration, next⟩] next

theorem step_of_execute (policy : SignedConversionPolicy) (before after : Configuration model)
    (event : Option (Event model)) (computed : execute policy before = some (event, after)) :
    (machine model policy).step before = some (match event with
      | none => .silent after
      | some event => .publish [⟨event, before, after⟩] after) := by
  cases event <;> simp only [machine, computed]

def ValidReceipt (policy : SignedConversionPolicy) (receipt : Receipt model) : Prop :=
  StatementSemantics.Step policy (represent receipt.before) (some receipt.event) (represent receipt.after)

theorem step_receipt_valid (policy : SignedConversionPolicy) (before after : Configuration model)
    (events : List (Receipt model))
    (computed : (machine model policy).step before = some (.publish events after)) :
    ∀ receipt ∈ events, ValidReceipt policy receipt := by
  cases executed : execute policy before with
  | none =>
      have classified : classify before = .publish events after := by
        simpa only [machine, executed, Option.some.injEq] using computed
      exact False.elim (classify_not_publish _ _ _ classified)
  | some result =>
      rcases result with ⟨event, next⟩
      cases event with
      | none => simp only [machine, executed] at computed; cases computed
      | some event =>
          simp only [machine, executed, Option.some.injEq, Transition.publish.injEq] at computed
          obtain ⟨rfl, rfl⟩ := computed
          intro receipt present
          have same : receipt = ⟨event, before, next⟩ := by simpa using present
          cases same
          exact execute_sound _ _ _ _ executed

theorem run_receipts_valid (policy : SignedConversionPolicy) (fuel : Nat) (initial : Configuration model) :
    ∀ receipt ∈ ((machine model policy).run fuel initial).1, ValidReceipt policy receipt := by
  induction fuel generalizing initial with
  | zero => simp [Machine.run]
  | succ fuel ih =>
      cases executed : execute policy initial with
      | none =>
          cases classified : classify initial with
          | silent next => exact False.elim (classify_not_silent _ _ classified)
          | publish events next => exact False.elim (classify_not_publish _ _ _ classified)
          | fail events => exact False.elim (classify_not_fail _ _ classified)
          | finish verdict | call request next => simp [Machine.run, machine, executed, classified]
      | some result =>
          rcases result with ⟨event, next⟩
          cases event with
          | none => simpa only [Machine.run, machine, executed] using ih next
          | some event =>
              rw [(machine model policy).run_succ_publish (step_of_execute _ _ _ _ executed)]
              intro receipt present
              rcases List.mem_append.mp present with present | present
              · exact step_receipt_valid _ _ _ _ (step_of_execute _ _ _ _ executed) receipt present
              · exact ih next receipt present

noncomputable def productive (model : Model) (policy : SignedConversionPolicy) :
    (machine model policy).Productive where
  rank := rank
  moves configuration := by simp only [machine, ne_eq, reduceCtorEq, not_false_eq_true]
  silent_decreases := by
    intro before after stepped
    cases computed : execute policy before with
    | none =>
        have classified : classify before = .silent after := by
          simpa only [machine, computed, Option.some.injEq] using stepped
        exact False.elim (classify_not_silent _ _ classified)
    | some result =>
        rcases result with ⟨event, next⟩
        cases event with
        | some event => simp only [machine, computed] at stepped; cases stepped
        | none =>
            have same : next = after := by simpa only [machine, computed, Option.some.injEq,
              Transition.silent.injEq] using stepped
            cases same
            exact execute_administrative_decreases _ _ _ computed

theorem resume_after_prefix (policy : SignedConversionPolicy) (first second : Nat)
    (initial saved : Configuration model) (events : List (Receipt model))
    (paused : (machine model policy).run first initial = (events, .exhausted saved)) :
    (machine model policy).run (first + second) initial =
      (events ++ ((machine model policy).run second saved).1, ((machine model policy).run second saved).2) :=
  (machine model policy).established_and_pending first second initial saved events paused

theorem resumed_accounts (policy : SignedConversionPolicy) (price : Configuration model → Nat)
    (first second : Nat) (initial saved : Configuration model) (events : List (Receipt model))
    (paused : (machine model policy).run first initial = (events, .exhausted saved)) :
    (machine model policy).spent price (first + second) initial =
      (machine model policy).spent price first initial + (machine model policy).spent price second saved := by
  rw [(machine model policy).spent_add, paused]
  rfl

def controlPrice : Configuration model → Nat
  | .statement _ _ _ _ | .flow _ _ _ _ => 1
  | _ => 0

def administrativePrice (policy : SignedConversionPolicy) (configuration : Configuration model) : Nat :=
  match execute policy configuration with
  | some (none, _) => 1
  | _ => 0

def occurrencePrice (policy : SignedConversionPolicy) (configuration : Configuration model) : Nat :=
  match execute policy configuration with
  | some (some (.occurrence _ _ _), _) => 1
  | _ => 0

def boundaryPrice (policy : SignedConversionPolicy) (configuration : Configuration model) : Nat :=
  match execute policy configuration with
  | some (some (.boundary _ _ _), _) => 1
  | _ => 0

def requestPrice (policy : SignedConversionPolicy) (configuration : Configuration model) : Nat :=
  match (machine model policy).step configuration with
  | some (.call _ _) => 1
  | _ => 0

theorem conflicting_expression_no_step (policy : SignedConversionPolicy) (expression : Expression model)
    (saved : ExpressionEventExecution.State (Index expression) model) (continuation : AfterExpression model)
    (selections : List IndexData) (first second : Index expression)
    (conflict : (compile expression).component.evaluation.findConflict (compile expression).component.enumeration =
      some (first, second)) : execute policy (.expression expression saved continuation selections) = none := by
  have forbidden : ExpressionEventExecution.admissible (compile expression) = false := by
    simp only [ExpressionEventExecution.admissible, conflict, reduceCtorEq, decide_false]
  have unfinished : finishedExpression? expression saved = none := by
    simp only [finishedExpression?, forbidden, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  cases selections with
  | nil => simp only [execute, unfinished]
  | cons data rest =>
      cases decoded : LocatedExpressionData.decodeIndex expression data <;>
        simp [execute, unfinished, decoded, ExpressionEventExecution.execute,
          ExpressionEventExecution.permitted, forbidden]

theorem conflict_reported (policy : SignedConversionPolicy) (expression : Expression model)
    (saved : ExpressionEventExecution.State (Index expression) model) (continuation : AfterExpression model)
    (selections : List IndexData) (first second : Index expression)
    (conflict : (compile expression).component.evaluation.findConflict (compile expression).component.enumeration =
      some (first, second)) :
    (machine model policy).step (.expression expression saved continuation selections) =
      some (.finish (.unsequenced expression (encodeIndex expression first) (encodeIndex expression second)
        (.expression expression saved continuation selections))) ∧
      (compile expression).component.evaluation.BadPair first second := by
  exact ⟨by simp only [machine, conflicting_expression_no_step _ _ _ _ _ _ _ conflict, classify, conflict],
    (compile expression).component.evaluation.findConflict_sound (compile expression).component.enumeration _ conflict⟩

theorem conflict_no_commits (policy : SignedConversionPolicy) (expression : Expression model)
    (saved : ExpressionEventExecution.State (Index expression) model) (continuation : AfterExpression model)
    (selections : List IndexData) (first second : Index expression) (fuel : Nat)
    (conflict : (compile expression).component.evaluation.findConflict (compile expression).component.enumeration =
      some (first, second)) :
    ((machine model policy).run fuel (.expression expression saved continuation selections)).1 = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [(machine model policy).run_succ_finish (conflict_reported _ _ _ _ _ _ _ conflict).1]

theorem halted_expression_no_step (policy : SignedConversionPolicy) (expression : Expression model)
    (saved : ExpressionEventExecution.State (Index expression) model) (continuation : AfterExpression model)
    (selections : List IndexData) (index : Index expression) (outcome : Outcome model)
    (halted : saved.halted = some (index, outcome)) :
    execute policy (.expression expression saved continuation selections) = none := by
  have unfinished : finishedExpression? expression saved = none := by simp [finishedExpression?, halted]
  cases selections with
  | nil => simp only [execute, unfinished]
  | cons data rest =>
      cases decoded : LocatedExpressionData.decodeIndex expression data <;>
        simp [execute, unfinished, decoded, ExpressionEventExecution.execute, halted]

theorem terminal_propagates (policy : SignedConversionPolicy) (expression : Expression model)
    (saved : ExpressionEventExecution.State (Index expression) model) (continuation : AfterExpression model)
    (selections : List IndexData) (index : Index expression) (outcome : Outcome model)
    (clean : (compile expression).component.evaluation.findConflict (compile expression).component.enumeration = none)
    (partition : ExpressionEventExecution.partitionCheck (compile expression) saved.pending saved.cache = true)
    (halted : saved.halted = some (index, outcome)) (terminal : outcome.terminal = true) :
    (machine model policy).step (.expression expression saved continuation selections) =
      some (.finish (.terminal expression (encodeIndex expression index) outcome
        (.expression expression saved continuation selections))) := by
  simp only [machine, halted_expression_no_step _ _ _ _ _ _ _ halted, classify,
    clean, partition, ↓reduceIte, halted, terminal]

end Mettapedia.Languages.C11.StatementMachine
