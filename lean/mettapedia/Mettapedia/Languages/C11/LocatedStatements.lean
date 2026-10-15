import Mettapedia.Languages.C11.LocatedExpressionData

/-!
# Located C11 statement control and complete expression continuations

The declaration-free statement component follows the Cesta CStmt forms for
expression statements, blocks, selection, iteration and structured jumps.
Every controlling, discarded and returned expression retains the established
located-expression occurrence state. A result occurrence alone cannot finish
a full expression: its pending modifications must also have been consumed.

The memory is the established byte/catalog model. Declarations, automatic
object lifetimes, function calls and nonlocal labels require further control
and ownership components; a declaration-free block supplies no cleanup action.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.LocatedStatements

open IntegerMemoryModel LocatedExpressions ExpressionEvents
open LocatedExpressionData (IndexData)

variable {model : Model}

inductive Statement (model : Model) where
  | empty
  | expression (operand : Expression model)
  | sequence (first second : Statement model)
  | block (body : List (Statement model))
  | conditional (condition : Expression model) (yes no : Statement model)
  | whileLoop (condition : Expression model) (body : Statement model)
  | doLoop (body : Statement model) (condition : Expression model)
  | forLoop (initial condition increment : Option (Expression model)) (body : Statement model)
  | breakLoop
  | continueLoop
  | returnValue (value : Option (Expression model))

inductive Continuation (model : Model) where
  | stop
  | sequence (following : Statement model) (outer : Continuation model)
  | block (following : List (Statement model)) (outer : Continuation model)
  | whileBody (condition : Expression model) (body : Statement model) (outer : Continuation model)
  | doBody (body : Statement model) (condition : Expression model) (outer : Continuation model)
  | forBody (condition increment : Option (Expression model)) (body : Statement model)
      (outer : Continuation model)

inductive AfterExpression (model : Model) where
  | discard (following : Continuation model)
  | conditional (yes no : Statement model) (following : Continuation model)
  | whileCondition (condition : Expression model) (body : Statement model) (following : Continuation model)
  | doCondition (body : Statement model) (condition : Expression model) (following : Continuation model)
  | forInitial (condition increment : Option (Expression model)) (body : Statement model)
      (following : Continuation model)
  | forCondition (condition increment : Option (Expression model)) (body : Statement model)
      (following : Continuation model)
  | forIncrement (condition increment : Option (Expression model)) (body : Statement model)
      (following : Continuation model)
  | returnValue

inductive Flow where
  | normal | broken | continued
  deriving DecidableEq, Repr

inductive State (model : Model) (Memory : Type) (ExpressionState : Expression model → Type) where
  | statement (statement : Statement model) (continuation : Continuation model) (memory : Memory)
      (selections : List IndexData)
  | flow (flow : Flow) (continuation : Continuation model) (memory : Memory) (selections : List IndexData)
  | expression (expression : Expression model) (saved : ExpressionState expression)
      (continuation : AfterExpression model) (selections : List IndexData)
  | returned (value : Option (IntegerScalar.Value model.parameters)) (memory : Memory) (selections : List IndexData)

abbrev Configuration (model : Model) := State model (ObjectAccessMemory.State model.characters)
  (fun expression => ExpressionEventExecution.State (Index expression) model)

abbrev SemanticConfiguration (model : Model) := State model (ObjectAccessMemory.SemanticState model.characters)
  (fun expression => ExpressionEventExecution.SemanticState (Index expression) model)

def represent {model : Model} : Configuration model → SemanticConfiguration model
  | .statement statement continuation memory selections =>
      .statement statement continuation (ObjectAccessMemory.represent memory) selections
  | .flow flow continuation memory selections =>
      .flow flow continuation (ObjectAccessMemory.represent memory) selections
  | .expression expression saved continuation selections =>
      .expression expression (ExpressionEventExecution.represent saved) continuation selections
  | .returned value memory selections => .returned value (ObjectAccessMemory.represent memory) selections

def sourceInitial (expression : Expression model) (memory : ObjectAccessMemory.SemanticState model.characters) :
    ExpressionEventExecution.SemanticState (Index expression) model :=
  ⟨(compile expression).component.enumeration.items.dedup, memory, [], none⟩

theorem initial_represents (expression : Expression model) (memory : ObjectAccessMemory.State model.characters) :
    ExpressionEventExecution.represent (ExpressionEventExecution.initialState (compile expression) memory) =
      sourceInitial expression (ObjectAccessMemory.represent memory) := rfl

def initial (statement : Statement model) (memory : ObjectAccessMemory.State model.characters)
    (selections : List IndexData := []) : Configuration model := .statement statement .stop memory selections

inductive Boundary where
  | discard | conditional | whileCondition | doCondition | forInitial | forCondition | forIncrement | returnValue
  deriving DecidableEq, Repr

def AfterExpression.boundary {model : Model} : AfterExpression model → Boundary
  | .discard _ => .discard
  | .conditional _ _ _ => .conditional
  | .whileCondition _ _ _ => .whileCondition
  | .doCondition _ _ _ => .doCondition
  | .forInitial _ _ _ _ => .forInitial
  | .forCondition _ _ _ _ => .forCondition
  | .forIncrement _ _ _ _ => .forIncrement
  | .returnValue => .returnValue

inductive Loop where
  | whileLoop | doLoop | forLoop
  deriving DecidableEq, Repr

inductive Event (model : Model) where
  | occurrence (expression : Expression model) (index : IndexData) (outcome : Outcome model)
  | boundary (kind : Boundary) (expression : Expression model) (value : IntegerScalar.Value model.parameters)
  | iteration (kind : Loop)
  deriving DecidableEq, Repr

def truth (value : IntegerScalar.Value model.parameters) : Bool := value.integer.value != 0

inductive Truth (value : IntegerScalar.Value model.parameters) : Bool → Prop where
  | zero (equal : value.integer.value = 0) : Truth value false
  | nonzero (different : value.integer.value ≠ 0) : Truth value true

theorem truth_iff (value : IntegerScalar.Value model.parameters) (selected : Bool) :
    truth value = selected ↔ Truth value selected := by
  cases selected with
  | false =>
      constructor
      · intro selected
        exact .zero (by simpa [truth] using selected)
      · intro selected
        cases selected with | zero equal => simp [truth, equal]
  | true =>
      constructor
      · intro selected
        exact .nonzero (by simpa [truth] using selected)
      · intro selected
        cases selected with | nonzero different => simp [truth, different]

structure CompleteExpression (expression : Expression model)
    (saved : ExpressionEventExecution.SemanticState (Index expression) model)
    (value : IntegerScalar.Value model.parameters) : Prop where
  partition : ExpressionEventExecution.Partition (compile expression) saved.pending saved.cache
  pending : saved.pending = []
  continuing : saved.halted = none
  clean : ¬ ExpressionSourceExecution.Undefined expression
  result : lookupScalar saved.cache (LocatedExpressions.result expression) = some value

noncomputable def Continuation.rank {model : Model} : Continuation model → Nat
  | .stop => 0
  | .sequence statement outer => 2 * sizeOf statement + 1 + outer.rank
  | .block statements outer => 2 * sizeOf statements + 1 + outer.rank
  | .whileBody _ _ outer | .doBody _ _ outer | .forBody _ _ _ outer => 1 + outer.rank

noncomputable def rank {model : Model} : Configuration model → Nat
  | .statement statement continuation _ _ => 2 * sizeOf statement + continuation.rank
  | .flow _ continuation _ _ => 1 + continuation.rank
  | .expression _ _ _ _ | .returned _ _ _ => 0

end Mettapedia.Languages.C11.LocatedStatements
