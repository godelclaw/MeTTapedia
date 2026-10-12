import Mettapedia.Languages.C11.ExpressionSourceActions
import Mettapedia.Languages.C11.ExpressionEventExecution

/-!
# Source execution joined to retained integer-expression occurrences

Source reduction uses the independent source sequencing and action rules,
cached operand values and owned byte-memory judgments. Its executable
realization selects an actual ready source occurrence and constructs the
same semantic endpoint. Both directions cover arbitrary located-expression
depth, rather than assuming a plan supplied by the caller is a source plan.

Unsequenced conflicts are tested on the source relation and actual complete
object identities. They cannot be repaired by a chronological choice. The
pure profile still needs separate source rules for general lvalues, branches,
calls, volatile/external effects and non-integer values. Failed memory
admission is not classified here as every possible source-level C fault.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ExpressionSourceExecution

open IntegerMemoryModel LocatedExpressions ExpressionEvents ExpressionEventExecution
open ExpressionSourceOrder ExpressionSourceActions

variable {model : Model}

def Unsequenced (expression : Expression model) (first second : Index expression) : Prop :=
  first ≠ second ∧ ¬ Before expression first second ∧ ¬ Before expression second first

def Undefined (expression : Expression model) : Prop :=
  ∃ first second left right, Unsequenced expression first second ∧
    Action expression first left ∧ Action expression second right ∧ Sequencing.Conflict left.access right.access

theorem compiled_conflict_iff (expression : Expression model) :
    (compile expression).component.evaluation.Undefined ↔ Undefined expression := by
  constructor
  · rintro ⟨first, second, ⟨different, forward, backward⟩, conflict⟩
    refine ⟨first, second, (compile expression).operation first, (compile expression).operation second,
      ⟨different, ?_, ?_⟩, compiled_action _ _, compiled_action _ _, ?_⟩
    · exact fun ordered => forward ((compiled_order_iff _ _ _).mpr ordered)
    · exact fun ordered => backward ((compiled_order_iff _ _ _).mpr ordered)
    · simpa only [compiled_access] using conflict
  · rintro ⟨first, second, left, right, ⟨different, forward, backward⟩, leftAction, rightAction, conflict⟩
    refine ⟨first, second, ⟨different, ?_, ?_⟩, ?_⟩
    · exact fun ordered => forward ((compiled_order_iff _ _ _).mp ordered)
    · exact fun ordered => backward ((compiled_order_iff _ _ _).mp ordered)
    · rw [← action_complete _ _ _ leftAction, ← action_complete _ _ _ rightAction] at conflict
      simpa only [compiled_access] using conflict

def Ready (expression : Expression model) (pending : List (Index expression)) (index : Index expression) : Prop :=
  index ∈ pending ∧ ∀ predecessor ∈ pending, ¬ Before expression predecessor index

theorem ready_iff (expression : Expression model) (pending : List (Index expression)) (index : Index expression) :
    SequencingSchedule.Ready (compile expression).component.evaluation.order pending index ↔ Ready expression pending index := by
  constructor
  · rintro ⟨present, minimal⟩
    exact ⟨present, fun predecessor pending ordered => minimal predecessor pending ((compiled_order_iff _ _ _).mpr ordered)⟩
  · rintro ⟨present, minimal⟩
    exact ⟨present, fun predecessor pending ordered => minimal predecessor pending ((compiled_order_iff _ _ _).mp ordered)⟩

inductive Advance (policy : SignedConversionPolicy) (expression : Expression model) :
    SemanticState (Index expression) model → Index expression → Outcome model →
      SemanticState (Index expression) model → Prop where
  | execute (before after : SemanticState (Index expression) model) (index : Index expression)
      (operation : Operation (Index expression) model) (outcome : Outcome model)
      (partition : Partition (compile expression) before.pending before.cache)
      (continuing : before.halted = none) (defined : ¬ Undefined expression)
      (ready : Ready expression before.pending index)
      (removed : SequencingSchedule.Removal index before.pending after.pending)
      (action : Action expression index operation)
      (evaluation : OperationEvaluation model policy before.cache before.memory operation outcome after.memory)
      (cached : after.cache = (index, outcome) :: before.cache)
      (halted : after.halted = haltAfter index outcome) : Advance policy expression before index outcome after

theorem reduction_iff (policy : SignedConversionPolicy) (expression : Expression model)
    (before after : SemanticState (Index expression) model) (index : Index expression) (outcome : Outcome model) :
    Reduction policy (compile expression) before index outcome after ↔ Advance policy expression before index outcome after := by
  constructor
  · intro reduced
    cases reduced with
    | execute _ _ _ partition continuing clean scheduled operation cached halted =>
        cases scheduled with
        | consume _ _ ready removed =>
            exact .execute _ _ _ _ _ partition continuing
              (fun undefined => clean ((compiled_conflict_iff _).mpr undefined))
              ((ready_iff _ _ _).mp ready) removed (compiled_action _ _) operation cached halted
  · intro advanced
    cases advanced with
    | execute _ _ operation _ partition continuing defined ready removed action evaluation cached halted =>
        have sourceAction := action_complete _ _ _ action
        rw [← sourceAction] at evaluation
        exact .execute _ _ _ _ partition continuing
          (fun conflict => defined ((compiled_conflict_iff _).mp conflict))
          (.consume _ _ index ((ready_iff _ _ _).mpr ready) removed) evaluation cached halted

theorem execute_sound (policy : SignedConversionPolicy) (expression : Expression model)
    (before after : State (Index expression) model) (index : Index expression) (outcome : Outcome model)
    (executed : ExpressionEventExecution.execute policy (compile expression) before index = some (outcome, after)) :
    Advance policy expression (represent before) index outcome (represent after) :=
  (reduction_iff _ _ _ _ _ _).mp (ExpressionEventExecution.execute_sound _ _ _ _ _ _ executed)

theorem execute_complete (policy : SignedConversionPolicy) (expression : Expression model)
    (before : State (Index expression) model) (after : SemanticState (Index expression) model)
    (index : Index expression) (outcome : Outcome model)
    (advanced : Advance policy expression (represent before) index outcome after) :
    ∃ saved, ExpressionEventExecution.execute policy (compile expression) before index = some (outcome, saved) ∧ represent saved = after :=
  ExpressionEventExecution.execute_complete _ _ _ _ _ _ ((reduction_iff _ _ _ _ _ _).mpr advanced)

theorem execute_iff (policy : SignedConversionPolicy) (expression : Expression model)
    (before : State (Index expression) model) (after : SemanticState (Index expression) model)
    (index : Index expression) (outcome : Outcome model) :
    (∃ saved, ExpressionEventExecution.execute policy (compile expression) before index = some (outcome, saved) ∧ represent saved = after) ↔
      Advance policy expression (represent before) index outcome after := by
  constructor
  · rintro ⟨saved, executed, rfl⟩; exact execute_sound _ _ _ _ _ _ executed
  · exact execute_complete _ _ _ _ _ _

theorem invalid_source_schedule_cannot_repair (expression : Expression model)
    (policy : SignedConversionPolicy) (memory : State (Index expression) model)
    (index : Index expression) (undefined : Undefined expression) :
    ExpressionEventExecution.execute policy (compile expression) memory index = none := by
  have conflict := (compiled_conflict_iff _).mpr undefined
  have notAllowed : admissible (compile expression) = false := by
    cases allowed : admissible (compile expression)
    · rfl
    · exact False.elim (((admissible_iff _).mp allowed) conflict)
  simp [ExpressionEventExecution.execute, permitted, notAllowed]

end Mettapedia.Languages.C11.ExpressionSourceExecution
