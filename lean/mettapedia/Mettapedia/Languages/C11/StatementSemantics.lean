import Mettapedia.Languages.C11.LocatedStatements

/-!
# Independent transitions for located C11 statement control

Structural transitions retain memory and unused occurrence selections. Loop
body completion is a source iteration transition, even when its body and
optional condition are empty; it is not unbounded silent administration.
Expression boundaries require the complete retained expression judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.StatementSemantics

open IntegerMemoryModel LocatedExpressions ExpressionEvents LocatedStatements
open LocatedExpressionData (IndexData encodeIndex decodeIndex)

variable {model : Model}

inductive BeginFor (condition increment : Option (Expression model)) (body : Statement model)
    (following : Continuation model) (memory : ObjectAccessMemory.SemanticState model.characters)
    (selections : List IndexData) : SemanticConfiguration model → Prop where
  | condition (operand : Expression model) (present : condition = some operand) :
      BeginFor condition increment body following memory selections
        (.expression operand (sourceInitial operand memory)
          (.forCondition condition increment body following) selections)
  | omitted (absent : condition = none) :
      BeginFor condition increment body following memory selections
        (.statement body (.forBody condition increment body following) memory selections)

inductive BeginIncrement (condition increment : Option (Expression model)) (body : Statement model)
    (following : Continuation model) (memory : ObjectAccessMemory.SemanticState model.characters)
    (selections : List IndexData) : SemanticConfiguration model → Prop where
  | increment (operand : Expression model) (present : increment = some operand) :
      BeginIncrement condition increment body following memory selections
        (.expression operand (sourceInitial operand memory)
          (.forIncrement condition increment body following) selections)
  | omitted (target : SemanticConfiguration model) (absent : increment = none)
      (begun : BeginFor condition increment body following memory selections target) :
      BeginIncrement condition increment body following memory selections target

inductive Administrative : SemanticConfiguration model → SemanticConfiguration model → Prop where
  | empty (following : Continuation model) (memory : ObjectAccessMemory.SemanticState model.characters)
      (selections : List IndexData) :
      Administrative (.statement .empty following memory selections) (.flow .normal following memory selections)
  | expression (operand : Expression model) (following : Continuation model)
      (memory : ObjectAccessMemory.SemanticState model.characters) (selections : List IndexData) :
      Administrative (.statement (.expression operand) following memory selections)
        (.expression operand (sourceInitial operand memory) (.discard following) selections)
  | sequence (first second : Statement model) (following : Continuation model)
      (memory : ObjectAccessMemory.SemanticState model.characters) (selections : List IndexData) :
      Administrative (.statement (.sequence first second) following memory selections)
        (.statement first (.sequence second following) memory selections)
  | blockEmpty (following : Continuation model) (memory : ObjectAccessMemory.SemanticState model.characters)
      (selections : List IndexData) :
      Administrative (.statement (.block []) following memory selections) (.flow .normal following memory selections)
  | blockCons (first : Statement model) (rest : List (Statement model)) (following : Continuation model)
      (memory : ObjectAccessMemory.SemanticState model.characters) (selections : List IndexData) :
      Administrative (.statement (.block (first :: rest)) following memory selections)
        (.statement first (.block rest following) memory selections)
  | conditional (condition : Expression model) (yes no : Statement model) (following : Continuation model)
      (memory : ObjectAccessMemory.SemanticState model.characters) (selections : List IndexData) :
      Administrative (.statement (.conditional condition yes no) following memory selections)
        (.expression condition (sourceInitial condition memory) (.conditional yes no following) selections)
  | whileLoop (condition : Expression model) (body : Statement model) (following : Continuation model)
      (memory : ObjectAccessMemory.SemanticState model.characters) (selections : List IndexData) :
      Administrative (.statement (.whileLoop condition body) following memory selections)
        (.expression condition (sourceInitial condition memory) (.whileCondition condition body following) selections)
  | doLoop (body : Statement model) (condition : Expression model) (following : Continuation model)
      (memory : ObjectAccessMemory.SemanticState model.characters) (selections : List IndexData) :
      Administrative (.statement (.doLoop body condition) following memory selections)
        (.statement body (.doBody body condition following) memory selections)
  | forInitial (operand : Expression model) (condition increment : Option (Expression model))
      (body : Statement model) (following : Continuation model)
      (memory : ObjectAccessMemory.SemanticState model.characters) (selections : List IndexData) :
      Administrative (.statement (.forLoop (some operand) condition increment body) following memory selections)
        (.expression operand (sourceInitial operand memory) (.forInitial condition increment body following) selections)
  | forOmitted (condition increment : Option (Expression model)) (body : Statement model)
      (following : Continuation model) (memory : ObjectAccessMemory.SemanticState model.characters)
      (selections : List IndexData) (target : SemanticConfiguration model)
      (begun : BeginFor condition increment body following memory selections target) :
      Administrative (.statement (.forLoop none condition increment body) following memory selections) target
  | breakLoop (following : Continuation model) (memory : ObjectAccessMemory.SemanticState model.characters)
      (selections : List IndexData) :
      Administrative (.statement .breakLoop following memory selections) (.flow .broken following memory selections)
  | continueLoop (following : Continuation model) (memory : ObjectAccessMemory.SemanticState model.characters)
      (selections : List IndexData) :
      Administrative (.statement .continueLoop following memory selections) (.flow .continued following memory selections)
  | returnEmpty (following : Continuation model) (memory : ObjectAccessMemory.SemanticState model.characters)
      (selections : List IndexData) :
      Administrative (.statement (.returnValue none) following memory selections) (.returned none memory selections)
  | returnValue (operand : Expression model) (following : Continuation model)
      (memory : ObjectAccessMemory.SemanticState model.characters) (selections : List IndexData) :
      Administrative (.statement (.returnValue (some operand)) following memory selections)
        (.expression operand (sourceInitial operand memory) .returnValue selections)
  | normalSequence (statement : Statement model) (following : Continuation model)
      (memory : ObjectAccessMemory.SemanticState model.characters) (selections : List IndexData) :
      Administrative (.flow .normal (.sequence statement following) memory selections)
        (.statement statement following memory selections)
  | normalBlockEmpty (following : Continuation model) (memory : ObjectAccessMemory.SemanticState model.characters)
      (selections : List IndexData) :
      Administrative (.flow .normal (.block [] following) memory selections) (.flow .normal following memory selections)
  | normalBlockCons (first : Statement model) (rest : List (Statement model)) (following : Continuation model)
      (memory : ObjectAccessMemory.SemanticState model.characters) (selections : List IndexData) :
      Administrative (.flow .normal (.block (first :: rest) following) memory selections)
        (.statement first (.block rest following) memory selections)
  | brokenSequence (statement : Statement model) (following : Continuation model)
      (memory : ObjectAccessMemory.SemanticState model.characters) (selections : List IndexData) :
      Administrative (.flow .broken (.sequence statement following) memory selections)
        (.flow .broken following memory selections)
  | continuedSequence (statement : Statement model) (following : Continuation model)
      (memory : ObjectAccessMemory.SemanticState model.characters) (selections : List IndexData) :
      Administrative (.flow .continued (.sequence statement following) memory selections)
        (.flow .continued following memory selections)
  | brokenBlock (statements : List (Statement model)) (following : Continuation model)
      (memory : ObjectAccessMemory.SemanticState model.characters) (selections : List IndexData) :
      Administrative (.flow .broken (.block statements following) memory selections)
        (.flow .broken following memory selections)
  | continuedBlock (statements : List (Statement model)) (following : Continuation model)
      (memory : ObjectAccessMemory.SemanticState model.characters) (selections : List IndexData) :
      Administrative (.flow .continued (.block statements following) memory selections)
        (.flow .continued following memory selections)
  | breakWhile (condition : Expression model) (body : Statement model) (following : Continuation model)
      (memory : ObjectAccessMemory.SemanticState model.characters) (selections : List IndexData) :
      Administrative (.flow .broken (.whileBody condition body following) memory selections)
        (.flow .normal following memory selections)
  | breakDo (body : Statement model) (condition : Expression model) (following : Continuation model)
      (memory : ObjectAccessMemory.SemanticState model.characters) (selections : List IndexData) :
      Administrative (.flow .broken (.doBody body condition following) memory selections)
        (.flow .normal following memory selections)
  | breakFor (condition increment : Option (Expression model)) (body : Statement model)
      (following : Continuation model) (memory : ObjectAccessMemory.SemanticState model.characters)
      (selections : List IndexData) :
      Administrative (.flow .broken (.forBody condition increment body following) memory selections)
        (.flow .normal following memory selections)

inductive Restart : Flow → Prop where
  | normal : Restart .normal
  | continued : Restart .continued

inductive Iteration : SemanticConfiguration model → Loop → SemanticConfiguration model → Prop where
  | whileLoop (flow : Flow) (restart : Restart flow) (condition : Expression model) (body : Statement model)
      (following : Continuation model) (memory : ObjectAccessMemory.SemanticState model.characters)
      (selections : List IndexData) :
      Iteration (.flow flow (.whileBody condition body following) memory selections) .whileLoop
        (.expression condition (sourceInitial condition memory) (.whileCondition condition body following) selections)
  | doLoop (flow : Flow) (restart : Restart flow) (body : Statement model) (condition : Expression model)
      (following : Continuation model) (memory : ObjectAccessMemory.SemanticState model.characters)
      (selections : List IndexData) :
      Iteration (.flow flow (.doBody body condition following) memory selections) .doLoop
        (.expression condition (sourceInitial condition memory) (.doCondition body condition following) selections)
  | forLoop (flow : Flow) (restart : Restart flow) (condition increment : Option (Expression model))
      (body : Statement model) (following : Continuation model)
      (memory : ObjectAccessMemory.SemanticState model.characters) (selections : List IndexData)
      (target : SemanticConfiguration model)
      (begun : BeginIncrement condition increment body following memory selections target) :
      Iteration (.flow flow (.forBody condition increment body following) memory selections) .forLoop target

inductive BoundaryTarget (after : AfterExpression model) (value : IntegerScalar.Value model.parameters)
    (memory : ObjectAccessMemory.SemanticState model.characters) (selections : List IndexData) :
    SemanticConfiguration model → Prop where
  | discard (following : Continuation model) (same : after = .discard following) :
      BoundaryTarget after value memory selections (.flow .normal following memory selections)
  | conditional (yes no : Statement model) (following : Continuation model) (selected : Bool)
      (same : after = .conditional yes no following) (test : Truth value selected) :
      BoundaryTarget after value memory selections (.statement (if selected then yes else no) following memory selections)
  | whileCondition (condition : Expression model) (body : Statement model) (following : Continuation model)
      (selected : Bool) (same : after = .whileCondition condition body following) (test : Truth value selected) :
      BoundaryTarget after value memory selections (if selected then
        .statement body (.whileBody condition body following) memory selections else .flow .normal following memory selections)
  | doCondition (body : Statement model) (condition : Expression model) (following : Continuation model)
      (selected : Bool) (same : after = .doCondition body condition following) (test : Truth value selected) :
      BoundaryTarget after value memory selections (if selected then
        .statement body (.doBody body condition following) memory selections else .flow .normal following memory selections)
  | forInitial (condition increment : Option (Expression model)) (body : Statement model)
      (following : Continuation model) (same : after = .forInitial condition increment body following)
      (target : SemanticConfiguration model) (begun : BeginFor condition increment body following memory selections target) :
      BoundaryTarget after value memory selections target
  | forCondition (condition increment : Option (Expression model)) (body : Statement model)
      (following : Continuation model) (selected : Bool) (same : after = .forCondition condition increment body following)
      (test : Truth value selected) :
      BoundaryTarget after value memory selections (if selected then
        .statement body (.forBody condition increment body following) memory selections else .flow .normal following memory selections)
  | forIncrement (condition increment : Option (Expression model)) (body : Statement model)
      (following : Continuation model) (same : after = .forIncrement condition increment body following)
      (target : SemanticConfiguration model) (begun : BeginFor condition increment body following memory selections target) :
      BoundaryTarget after value memory selections target
  | returnValue (same : after = .returnValue) :
      BoundaryTarget after value memory selections (.returned (some value) memory selections)

inductive Step (policy : SignedConversionPolicy) :
    SemanticConfiguration model → Option (Event model) → SemanticConfiguration model → Prop where
  | administrative (before after : SemanticConfiguration model) (stepped : Administrative before after) :
      Step policy before none after
  | iteration (before after : SemanticConfiguration model) (kind : Loop) (stepped : Iteration before kind after) :
      Step policy before (some (.iteration kind)) after
  | occurrence (expression : Expression model) (before after : ExpressionEventExecution.SemanticState (Index expression) model)
      (continuation : AfterExpression model) (data : IndexData) (rest : List IndexData)
      (index : Index expression) (outcome : Outcome model) (decoded : decodeIndex expression data = some index)
      (advanced : ExpressionSourceExecution.Advance policy expression before index outcome after) :
      Step policy (.expression expression before continuation (data :: rest))
        (some (.occurrence expression (encodeIndex expression index) outcome)) (.expression expression after continuation rest)
  | boundary (expression : Expression model) (saved : ExpressionEventExecution.SemanticState (Index expression) model)
      (continuation : AfterExpression model) (selections : List IndexData)
      (value : IntegerScalar.Value model.parameters) (completed : CompleteExpression expression saved value)
      (target : SemanticConfiguration model) (continued : BoundaryTarget continuation value saved.memory selections target) :
      Step policy (.expression expression saved continuation selections)
        (some (.boundary continuation.boundary expression value)) target

theorem boundary_has_drained_expression (policy : SignedConversionPolicy) (expression : Expression model)
    (saved : ExpressionEventExecution.SemanticState (Index expression) model) (continuation : AfterExpression model)
    (selections : List IndexData) (kind : Boundary) (source : Expression model)
    (value : IntegerScalar.Value model.parameters) (target : SemanticConfiguration model)
    (stepped : Step policy (.expression expression saved continuation selections)
      (some (.boundary kind source value)) target) : saved.pending = [] := by
  cases stepped with
  | boundary _ _ _ _ _ completed _ _ => exact completed.pending

end Mettapedia.Languages.C11.StatementSemantics
