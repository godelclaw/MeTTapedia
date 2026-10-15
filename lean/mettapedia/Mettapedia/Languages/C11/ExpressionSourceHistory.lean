import Mettapedia.Languages.C11.ExpressionSourceExecution
import Mettapedia.Languages.C11.ExpressionEventHistory

/-!
# Source histories realized by retained expression execution

The source trace uses independently defined source actions and sequencing.
Constructive realization preserves its ordered occurrence observations and
exact semantic memory/cache endpoint. Conversely, every executable prefix
produces a source trace. The source-generated occurrence identities are unique,
and the common retained-state driver supplies prefix resumption and work
accounting without replaying a consumed modification occurrence.

The located, call-free integer syntax remains the declared source profile.
These finite-expression results do not assert termination of arbitrary C
programs or grant authority for external effects.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ExpressionSourceHistory

open IntegerMemoryModel LocatedExpressions ExpressionEvents ExpressionEventExecution
open ExpressionSourceExecution ExpressionEventHistory

variable {model : Model}

inductive Trace (policy : SignedConversionPolicy) (expression : Expression model) :
    SemanticState (Index expression) model → List (Occurrence (Index expression) model) →
      SemanticState (Index expression) model → Prop where
  | nil (state : SemanticState (Index expression) model) : Trace policy expression state [] state
  | cons (before middle after : SemanticState (Index expression) model)
      (event : Occurrence (Index expression) model) (events : List (Occurrence (Index expression) model))
      (step : Advance policy expression before event.index event.outcome middle)
      (following : Trace policy expression middle events after) :
      Trace policy expression before (event :: events) after

theorem trace_iff (policy : SignedConversionPolicy) (expression : Expression model)
    (before after : SemanticState (Index expression) model)
    (events : List (Occurrence (Index expression) model)) :
    SemanticHistory policy (compile expression) before events after ↔
      Trace policy expression before events after := by
  constructor
  · intro history
    induction history with
    | nil state => exact .nil _
    | cons before middle after event events step following ih =>
        exact .cons _ _ _ _ _ ((reduction_iff _ _ _ _ _ _).mp step) ih
  · intro history
    induction history with
    | nil state => exact .nil _
    | cons before middle after event events step following ih =>
        exact .cons _ _ _ _ _ ((reduction_iff _ _ _ _ _ _).mpr step) ih

def begin (expression : Expression model) (memory : ObjectAccessMemory.State model.characters)
    (selections : List (Index expression)) : Configuration (Index expression) model :=
  ⟨compile expression, initialState (compile expression) memory, selections⟩

theorem initial_occurrences (expression : Expression model)
    (memory : ObjectAccessMemory.State model.characters) (selections : List (Index expression)) :
    (begin expression memory selections).state.pending =
      (compile expression).component.enumeration.items := by
  change ((compile expression).component.enumeration.items).dedup = _
  exact List.dedup_eq_self.mpr (compiled_occurrences_unique expression)

theorem initial_admitted (expression : Expression model)
    (memory : ObjectAccessMemory.State model.characters) (selections : List (Index expression)) :
    Partition (compile expression) (begin expression memory selections).state.pending
      (begin expression memory selections).state.cache := initial_partition _ _

theorem source_history_realization (policy : SignedConversionPolicy) (expression : Expression model)
    (before after : SemanticState (Index expression) model)
    (events : List (Occurrence (Index expression) model))
    (history : Trace policy expression before events after)
    (actual : State (Index expression) model) (represented : represent actual = before)
    (rest : List (Index expression)) :
    ∃ receipts saved,
      represent saved = after ∧ receipts.map observation = events ∧
      History policy (compile expression) actual receipts saved ∧
      (machine model policy).run events.length
          ⟨compile expression, actual, events.map Occurrence.index ++ rest⟩ =
        (receipts, .exhausted ⟨compile expression, saved, rest⟩) :=
  history_realization _ _ _ _ _ ((trace_iff _ _ _ _ _).mpr history) actual represented rest

theorem run_source_trace (policy : SignedConversionPolicy) (expression : Expression model)
    (fuel : Nat) (actual : State (Index expression) model) (selections : List (Index expression)) :
    ∃ final, endpoint ((machine model policy).run fuel ⟨compile expression, actual, selections⟩).2 = some final ∧
      final.plan = compile expression ∧
      Trace policy expression (represent actual)
        (((machine model policy).run fuel ⟨compile expression, actual, selections⟩).1.map observation)
        (represent final.state) := by
  obtain ⟨final, retained, samePlan, history⟩ := run_history model policy fuel
    ⟨compile expression, actual, selections⟩
  exact ⟨final, retained, samePlan, (trace_iff _ _ _ _ _).mp history.semantic⟩

theorem run_account (policy : SignedConversionPolicy) (expression : Expression model)
    (fuel : Nat) (memory : ObjectAccessMemory.State model.characters) (selections : List (Index expression)) :
    ∃ final, endpoint ((machine model policy).run fuel (begin expression memory selections)).2 = some final ∧
      final.plan = compile expression ∧
      final.state.pending.length + ((machine model policy).run fuel (begin expression memory selections)).1.length =
        (compile expression).component.enumeration.items.length := by
  obtain ⟨final, retained, samePlan, account⟩ := run_conserves_occurrences model policy fuel
    (begin expression memory selections)
  exact ⟨final, retained, samePlan, by simpa only [initial_occurrences] using account⟩

theorem prefix_resume_without_repeated_occurrences (policy : SignedConversionPolicy)
    (expression : Expression model) (first second : Nat)
    (memory : ObjectAccessMemory.State model.characters) (selections : List (Index expression))
    (saved : Configuration (Index expression) model) (events : List (Receipt (Index expression) model))
    (paused : (machine model policy).run first (begin expression memory selections) = (events, .exhausted saved)) :
    (machine model policy).run (first + second) (begin expression memory selections) =
      (events ++ ((machine model policy).run second saved).1, ((machine model policy).run second saved).2) ∧
    saved.plan = compile expression ∧
    ((events ++ ((machine model policy).run second saved).1).map Receipt.index).Nodup := by
  have unique : (begin expression memory selections).state.pending.Nodup := by
    rw [initial_occurrences]
    exact compiled_occurrences_unique _
  exact ⟨resume_after_prefix _ _ _ _ _ _ _ paused,
    resume_retains_plan _ _ _ _ _ _ paused,
    resume_no_repeat _ _ _ _ _ _ _ unique paused⟩

end Mettapedia.Languages.C11.ExpressionSourceHistory
