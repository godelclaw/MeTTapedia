import Mettapedia.Languages.C11.StatementSemantics

/-!
# Executable statement and full-expression control

The executable component selects source occurrences through the checked
expression executor. Structural control has a separate transition account;
loop restarts and completed full expressions are explicit source boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.StatementExecution

open IntegerMemoryModel LocatedExpressions ExpressionEvents LocatedStatements
open LocatedExpressionData (IndexData encodeIndex decodeIndex)
open StatementSemantics

variable {model : Model}

def beginFor (condition increment : Option (Expression model)) (body : Statement model)
    (following : Continuation model) (memory : ObjectAccessMemory.State model.characters)
    (selections : List IndexData) : Configuration model :=
  match condition with
  | some operand => .expression operand (ExpressionEventExecution.initialState (compile operand) memory)
      (.forCondition condition increment body following) selections
  | none => .statement body (.forBody condition increment body following) memory selections

theorem beginFor_sound (condition increment : Option (Expression model)) (body : Statement model)
    (following : Continuation model) (memory : ObjectAccessMemory.State model.characters)
    (selections : List IndexData) : BeginFor condition increment body following
      (ObjectAccessMemory.represent memory) selections (represent (beginFor condition increment body following memory selections)) := by
  cases condition with
  | none => exact .omitted rfl
  | some operand => exact .condition operand rfl

theorem beginFor_complete (condition increment : Option (Expression model)) (body : Statement model)
    (following : Continuation model) (memory : ObjectAccessMemory.State model.characters)
    (selections : List IndexData) (target : SemanticConfiguration model)
    (begun : BeginFor condition increment body following (ObjectAccessMemory.represent memory) selections target) :
    represent (beginFor condition increment body following memory selections) = target := by
  cases begun with
  | condition operand present => simp only [beginFor, present, represent, initial_represents]
  | omitted absent => simp only [beginFor, absent, represent]

def beginIncrement (condition increment : Option (Expression model)) (body : Statement model)
    (following : Continuation model) (memory : ObjectAccessMemory.State model.characters)
    (selections : List IndexData) : Configuration model :=
  match increment with
  | some operand => .expression operand (ExpressionEventExecution.initialState (compile operand) memory)
      (.forIncrement condition increment body following) selections
  | none => beginFor condition increment body following memory selections

theorem beginIncrement_sound (condition increment : Option (Expression model)) (body : Statement model)
    (following : Continuation model) (memory : ObjectAccessMemory.State model.characters)
    (selections : List IndexData) : BeginIncrement condition increment body following
      (ObjectAccessMemory.represent memory) selections (represent (beginIncrement condition increment body following memory selections)) := by
  cases increment with
  | none => exact .omitted _ rfl (beginFor_sound _ _ _ _ _ _)
  | some operand => exact .increment operand rfl

theorem beginIncrement_complete (condition increment : Option (Expression model)) (body : Statement model)
    (following : Continuation model) (memory : ObjectAccessMemory.State model.characters)
    (selections : List IndexData) (target : SemanticConfiguration model)
    (begun : BeginIncrement condition increment body following (ObjectAccessMemory.represent memory) selections target) :
    represent (beginIncrement condition increment body following memory selections) = target := by
  cases begun with
  | increment operand present => simp only [beginIncrement, present, represent, initial_represents]
  | omitted target absent begun =>
      cases absent
      simp only [beginIncrement]
      exact beginFor_complete _ _ _ _ _ _ _ begun

def afterExpression (after : AfterExpression model) (value : IntegerScalar.Value model.parameters)
    (memory : ObjectAccessMemory.State model.characters) (selections : List IndexData) : Configuration model :=
  match after with
  | .discard following => .flow .normal following memory selections
  | .conditional yes no following => .statement (if truth value then yes else no) following memory selections
  | .whileCondition condition body following => if truth value then
      .statement body (.whileBody condition body following) memory selections else .flow .normal following memory selections
  | .doCondition body condition following => if truth value then
      .statement body (.doBody body condition following) memory selections else .flow .normal following memory selections
  | .forInitial condition increment body following | .forIncrement condition increment body following =>
      beginFor condition increment body following memory selections
  | .forCondition condition increment body following => if truth value then
      .statement body (.forBody condition increment body following) memory selections else .flow .normal following memory selections
  | .returnValue => .returned (some value) memory selections

theorem afterExpression_sound (after : AfterExpression model) (value : IntegerScalar.Value model.parameters)
    (memory : ObjectAccessMemory.State model.characters) (selections : List IndexData) :
    BoundaryTarget after value (ObjectAccessMemory.represent memory) selections
      (represent (afterExpression after value memory selections)) := by
  cases after with
  | discard following => exact .discard following rfl
  | conditional yes no following => exact .conditional yes no following (truth value) rfl ((truth_iff _ _).mp rfl)
  | whileCondition condition body following =>
      cases selected : truth value <;>
        simpa [afterExpression, selected, represent] using
          (BoundaryTarget.whileCondition (memory := ObjectAccessMemory.represent memory) (selections := selections)
            condition body following _ rfl ((truth_iff _ _).mp selected))
  | doCondition body condition following =>
      cases selected : truth value <;>
        simpa [afterExpression, selected, represent] using
          (BoundaryTarget.doCondition (memory := ObjectAccessMemory.represent memory) (selections := selections)
            body condition following _ rfl ((truth_iff _ _).mp selected))
  | forInitial condition increment body following =>
      exact .forInitial condition increment body following rfl _ (beginFor_sound _ _ _ _ _ _)
  | forCondition condition increment body following =>
      cases selected : truth value <;>
        simpa [afterExpression, selected, represent] using
          (BoundaryTarget.forCondition (memory := ObjectAccessMemory.represent memory) (selections := selections)
            condition increment body following _ rfl ((truth_iff _ _).mp selected))
  | forIncrement condition increment body following =>
      exact .forIncrement condition increment body following rfl _ (beginFor_sound _ _ _ _ _ _)
  | returnValue => exact .returnValue rfl

theorem afterExpression_complete (after : AfterExpression model) (value : IntegerScalar.Value model.parameters)
    (memory : ObjectAccessMemory.State model.characters) (selections : List IndexData)
    (target : SemanticConfiguration model)
    (continued : BoundaryTarget after value (ObjectAccessMemory.represent memory) selections target) :
    represent (afterExpression after value memory selections) = target := by
  cases continued with
  | discard following same => cases same; rfl
  | conditional yes no following selected same test =>
      cases same
      simp only [afterExpression, (truth_iff _ _).mpr test, represent]
  | whileCondition condition body following selected same test =>
      cases same
      cases selected <;> simp only [afterExpression, (truth_iff _ _).mpr test, Bool.false_eq_true,
        ↓reduceIte, represent]
  | doCondition body condition following selected same test =>
      cases same
      cases selected <;> simp only [afterExpression, (truth_iff _ _).mpr test, Bool.false_eq_true,
        ↓reduceIte, represent]
  | forInitial condition increment body following same target begun =>
      cases same
      exact beginFor_complete _ _ _ _ _ _ _ begun
  | forCondition condition increment body following selected same test =>
      cases same
      cases selected <;> simp only [afterExpression, (truth_iff _ _).mpr test, Bool.false_eq_true,
        ↓reduceIte, represent]
  | forIncrement condition increment body following same target begun =>
      cases same
      exact beginFor_complete _ _ _ _ _ _ _ begun
  | returnValue same => cases same; rfl

def controlStep : Configuration model → Option (Option (Event model) × Configuration model)
  | .statement statement following memory selections => match statement with
      | .empty => some (none, .flow .normal following memory selections)
      | .expression operand => some (none, .expression operand
          (ExpressionEventExecution.initialState (compile operand) memory) (.discard following) selections)
      | .sequence first second => some (none, .statement first (.sequence second following) memory selections)
      | .block [] => some (none, .flow .normal following memory selections)
      | .block (first :: rest) => some (none, .statement first (.block rest following) memory selections)
      | .conditional condition yes no => some (none, .expression condition
          (ExpressionEventExecution.initialState (compile condition) memory) (.conditional yes no following) selections)
      | .whileLoop condition body => some (none, .expression condition
          (ExpressionEventExecution.initialState (compile condition) memory) (.whileCondition condition body following) selections)
      | .doLoop body condition => some (none, .statement body (.doBody body condition following) memory selections)
      | .forLoop (some operand) condition increment body => some (none, .expression operand
          (ExpressionEventExecution.initialState (compile operand) memory) (.forInitial condition increment body following) selections)
      | .forLoop none condition increment body => some (none, beginFor condition increment body following memory selections)
      | .breakLoop => some (none, .flow .broken following memory selections)
      | .continueLoop => some (none, .flow .continued following memory selections)
      | .returnValue none => some (none, .returned none memory selections)
      | .returnValue (some operand) => some (none, .expression operand
          (ExpressionEventExecution.initialState (compile operand) memory) .returnValue selections)
  | .flow flow following memory selections => match following with
      | .stop => none
      | .sequence statement outer => match flow with
          | .normal => some (none, .statement statement outer memory selections)
          | .broken => some (none, .flow .broken outer memory selections)
          | .continued => some (none, .flow .continued outer memory selections)
      | .block statements outer => match flow with
          | .broken => some (none, .flow .broken outer memory selections)
          | .continued => some (none, .flow .continued outer memory selections)
          | .normal => match statements with
              | [] => some (none, .flow .normal outer memory selections)
              | first :: rest => some (none, .statement first (.block rest outer) memory selections)
      | .whileBody condition body outer => match flow with
          | .broken => some (none, .flow .normal outer memory selections)
          | .normal | .continued => some (some (.iteration .whileLoop), .expression condition
              (ExpressionEventExecution.initialState (compile condition) memory) (.whileCondition condition body outer) selections)
      | .doBody body condition outer => match flow with
          | .broken => some (none, .flow .normal outer memory selections)
          | .normal | .continued => some (some (.iteration .doLoop), .expression condition
              (ExpressionEventExecution.initialState (compile condition) memory) (.doCondition body condition outer) selections)
      | .forBody condition increment body outer => match flow with
          | .broken => some (none, .flow .normal outer memory selections)
          | .normal | .continued => some (some (.iteration .forLoop), beginIncrement condition increment body outer memory selections)
  | .expression _ _ _ _ | .returned _ _ _ => none

theorem controlStep_sound (before after : Configuration model) (event : Option (Event model))
    (computed : controlStep before = some (event, after)) (policy : SignedConversionPolicy) :
    Step policy (represent before) event (represent after) := by
  cases before with
  | statement statement following memory selections =>
      cases statement with
      | empty => cases computed; exact .administrative _ _ (.empty _ _ _)
      | expression operand => cases computed; exact .administrative _ _ (.expression _ _ _ _)
      | sequence first second => cases computed; exact .administrative _ _ (.sequence _ _ _ _ _)
      | block statements =>
          cases statements with
          | nil => cases computed; exact .administrative _ _ (.blockEmpty _ _ _)
          | cons first rest => cases computed; exact .administrative _ _ (.blockCons _ _ _ _ _)
      | conditional condition yes no => cases computed; exact .administrative _ _ (.conditional _ _ _ _ _ _)
      | whileLoop condition body => cases computed; exact .administrative _ _ (.whileLoop _ _ _ _ _)
      | doLoop body condition => cases computed; exact .administrative _ _ (.doLoop _ _ _ _ _)
      | forLoop initial condition increment body =>
          cases initial with
          | some operand => cases computed; exact .administrative _ _ (.forInitial _ _ _ _ _ _ _)
          | none => cases computed; exact .administrative _ _ (.forOmitted _ _ _ _ _ _ _ (beginFor_sound _ _ _ _ _ _))
      | breakLoop => cases computed; exact .administrative _ _ (.breakLoop _ _ _)
      | continueLoop => cases computed; exact .administrative _ _ (.continueLoop _ _ _)
      | returnValue value =>
          cases value with
          | none => cases computed; exact .administrative _ _ (.returnEmpty _ _ _)
          | some operand => cases computed; exact .administrative _ _ (.returnValue _ _ _ _)
  | flow flow following memory selections =>
      cases following with
      | stop => cases computed
      | sequence statement outer =>
          cases flow with
          | normal => cases computed; exact .administrative _ _ (.normalSequence _ _ _ _)
          | broken => cases computed; exact .administrative _ _ (.brokenSequence _ _ _ _)
          | continued => cases computed; exact .administrative _ _ (.continuedSequence _ _ _ _)
      | block statements outer =>
          cases flow with
          | broken => cases computed; exact .administrative _ _ (.brokenBlock _ _ _ _)
          | continued => cases computed; exact .administrative _ _ (.continuedBlock _ _ _ _)
          | normal =>
              cases statements with
              | nil => cases computed; exact .administrative _ _ (.normalBlockEmpty _ _ _)
              | cons first rest => cases computed; exact .administrative _ _ (.normalBlockCons _ _ _ _ _)
      | whileBody condition body outer =>
          cases flow with
          | broken => cases computed; exact .administrative _ _ (.breakWhile _ _ _ _ _)
          | normal => cases computed; exact .iteration _ _ _ (.whileLoop _ .normal _ _ _ _ _)
          | continued => cases computed; exact .iteration _ _ _ (.whileLoop _ .continued _ _ _ _ _)
      | doBody body condition outer =>
          cases flow with
          | broken => cases computed; exact .administrative _ _ (.breakDo _ _ _ _ _)
          | normal => cases computed; exact .iteration _ _ _ (.doLoop _ .normal _ _ _ _ _)
          | continued => cases computed; exact .iteration _ _ _ (.doLoop _ .continued _ _ _ _ _)
      | forBody condition increment body outer =>
          cases flow with
          | broken => cases computed; exact .administrative _ _ (.breakFor _ _ _ _ _ _)
          | normal => cases computed; exact .iteration _ _ _ (.forLoop _ .normal _ _ _ _ _ _ _ (beginIncrement_sound _ _ _ _ _ _))
          | continued => cases computed; exact .iteration _ _ _ (.forLoop _ .continued _ _ _ _ _ _ _ (beginIncrement_sound _ _ _ _ _ _))
  | expression _ _ _ _ | returned _ _ _ => cases computed

theorem administrative_complete (before : Configuration model) (after : SemanticConfiguration model)
    (stepped : Administrative (represent before) after) :
    ∃ saved, controlStep before = some (none, saved) ∧ represent saved = after := by
  cases before with
  | statement statement following memory selections =>
      cases stepped with
      | empty | expression | sequence | blockEmpty | blockCons | conditional | whileLoop | doLoop |
          forInitial | breakLoop | continueLoop | returnEmpty | returnValue => exact ⟨_, rfl, rfl⟩
      | forOmitted condition increment body following memory selections target begun =>
          exact ⟨_, rfl, beginFor_complete _ _ _ _ _ _ _ begun⟩
  | flow flow following memory selections =>
      cases stepped <;> exact ⟨_, rfl, rfl⟩
  | expression _ _ _ _ | returned _ _ _ => cases stepped

theorem iteration_complete (before : Configuration model) (kind : Loop) (after : SemanticConfiguration model)
    (stepped : Iteration (represent before) kind after) :
    ∃ saved, controlStep before = some (some (.iteration kind), saved) ∧ represent saved = after := by
  cases before with
  | statement _ _ _ _ | expression _ _ _ _ | returned _ _ _ => cases stepped
  | flow flow following memory selections =>
      cases stepped with
      | whileLoop _ restart => cases restart <;> exact ⟨_, rfl, rfl⟩
      | doLoop _ restart => cases restart <;> exact ⟨_, rfl, rfl⟩
      | forLoop _ restart condition increment body following memory selections target begun =>
          cases restart <;> exact ⟨_, rfl, beginIncrement_complete _ _ _ _ _ _ _ begun⟩

def finishedExpression? (expression : Expression model)
    (saved : ExpressionEventExecution.State (Index expression) model) : Option (IntegerScalar.Value model.parameters) :=
  if ExpressionEventExecution.admissible (compile expression) &&
      ExpressionEventExecution.partitionCheck (compile expression) saved.pending saved.cache then
    match saved.halted, saved.pending with
    | none, [] => lookupScalar saved.cache (LocatedExpressions.result expression)
    | _, _ => none
  else none

theorem finishedExpression_iff (expression : Expression model)
    (saved : ExpressionEventExecution.State (Index expression) model) (value : IntegerScalar.Value model.parameters) :
    finishedExpression? expression saved = some value ↔
      CompleteExpression expression (ExpressionEventExecution.represent saved) value := by
  constructor
  · intro computed
    unfold finishedExpression? at computed
    split at computed
    · rename_i permitted
      obtain ⟨clean, partition⟩ := Bool.and_eq_true_iff.mp permitted
      have independent : ¬ ExpressionSourceExecution.Undefined expression :=
        fun undefined => (ExpressionEventExecution.admissible_iff _).mp clean
          ((ExpressionSourceExecution.compiled_conflict_iff _).mpr undefined)
      cases halted : saved.halted with
      | some stopped => simp only [halted] at computed; cases computed
      | none =>
          cases pending : saved.pending with
          | cons first rest => simp only [halted, pending] at computed; cases computed
          | nil => exact ⟨(ExpressionEventExecution.partitionCheck_iff _ _ _).mp partition,
              pending, halted, independent, by
                change lookupScalar saved.cache (LocatedExpressions.result expression) = some value
                simpa only [halted, pending] using computed⟩
    · cases computed
  · intro completed
    have clean : ExpressionEventExecution.admissible (compile expression) = true :=
      (ExpressionEventExecution.admissible_iff _).mpr (fun undefined => completed.clean
        ((ExpressionSourceExecution.compiled_conflict_iff _).mp undefined))
    have partition : ExpressionEventExecution.partitionCheck (compile expression) saved.pending saved.cache = true :=
      (ExpressionEventExecution.partitionCheck_iff _ _ _).mpr completed.partition
    have permitted : (ExpressionEventExecution.admissible (compile expression) &&
      ExpressionEventExecution.partitionCheck (compile expression) saved.pending saved.cache) = true :=
      Bool.and_eq_true_iff.mpr ⟨clean, partition⟩
    have pending : saved.pending = [] := completed.pending
    have continuing : saved.halted = none := completed.continuing
    unfold finishedExpression?
    rw [if_pos permitted]
    simp only [pending, continuing]
    exact completed.result

def execute (policy : SignedConversionPolicy) (configuration : Configuration model) :
    Option (Option (Event model) × Configuration model) :=
  match configuration with
  | .expression expression saved continuation selections =>
      match finishedExpression? expression saved with
      | some value => some (some (.boundary continuation.boundary expression value),
          afterExpression continuation value saved.memory selections)
      | none => match selections with
          | [] => none
          | data :: rest => do
              let index ← decodeIndex expression data
              let (outcome, following) ← ExpressionEventExecution.execute policy (compile expression) saved index
              some (some (.occurrence expression (encodeIndex expression index) outcome),
                .expression expression following continuation rest)
  | _ => controlStep configuration

theorem advanced_not_finished (policy : SignedConversionPolicy) (expression : Expression model)
    (before : ExpressionEventExecution.State (Index expression) model)
    (after : ExpressionEventExecution.SemanticState (Index expression) model)
    (index : Index expression) (outcome : Outcome model)
    (advanced : ExpressionSourceExecution.Advance policy expression
      (ExpressionEventExecution.represent before) index outcome after) :
    finishedExpression? expression before = none := by
  have nonempty : before.pending ≠ [] := by
    intro empty
    cases advanced with
    | execute _ _ _ _ _ _ _ ready _ _ _ _ _ =>
        have present : index ∈ before.pending := ready.1
        simp only [empty, List.not_mem_nil] at present
  cases finished : finishedExpression? expression before with
  | none => rfl
  | some value => exact False.elim (nonempty ((finishedExpression_iff _ _ _).mp finished).pending)

theorem execute_sound (policy : SignedConversionPolicy) (before after : Configuration model)
    (event : Option (Event model)) (computed : execute policy before = some (event, after)) :
    Step policy (represent before) event (represent after) := by
  cases before with
  | expression expression saved continuation selections =>
      cases finished : finishedExpression? expression saved with
      | some value =>
          simp only [execute, finished] at computed
          cases computed
          exact .boundary _ _ _ _ _ ((finishedExpression_iff _ _ _).mp finished) _
            (afterExpression_sound _ _ _ _)
      | none =>
          cases selections with
          | nil => simp only [execute, finished] at computed; cases computed
          | cons data rest =>
              cases decoded : decodeIndex expression data with
              | none => simp only [execute, finished, decoded, bind, Option.bind_none] at computed; cases computed
              | some index =>
                  cases advanced : ExpressionEventExecution.execute policy (compile expression) saved index with
                  | none => simp only [execute, finished, decoded, advanced, bind, Option.bind_some, Option.bind_none] at computed; cases computed
                  | some result =>
                      rcases result with ⟨outcome, following⟩
                      simp only [execute, finished, decoded, advanced, bind, Option.bind_some] at computed
                      cases computed
                      exact .occurrence _ _ _ _ _ _ _ _ decoded
                        (ExpressionSourceExecution.execute_sound _ _ _ _ _ _ advanced)
  | statement _ _ _ _ | flow _ _ _ _ | returned _ _ _ =>
      exact controlStep_sound _ _ _ (by simpa only [execute] using computed) policy

theorem execute_complete (policy : SignedConversionPolicy) (before : Configuration model)
    (after : SemanticConfiguration model) (event : Option (Event model))
    (stepped : Step policy (represent before) event after) :
    ∃ saved, execute policy before = some (event, saved) ∧ represent saved = after := by
  cases before with
  | statement statement following memory selections =>
      cases stepped with
      | administrative _ _ administrative =>
          exact administrative_complete _ _ administrative
      | iteration _ _ _ iteration => cases iteration
  | flow flow following memory selections =>
      cases stepped with
      | administrative _ _ administrative => exact administrative_complete _ _ administrative
      | iteration _ _ kind iteration => exact iteration_complete _ _ _ iteration
  | returned _ _ _ =>
      cases stepped with
      | administrative _ _ administrative => cases administrative
      | iteration _ _ _ iteration => cases iteration
  | expression expression saved continuation selections =>
      cases stepped with
      | administrative _ _ administrative => cases administrative
      | iteration _ _ _ iteration => cases iteration
      | occurrence =>
          rename_i data rest outcome after index decoded advanced
          obtain ⟨following, computed, represented⟩ := ExpressionSourceExecution.execute_complete
            policy expression saved after index outcome advanced
          refine ⟨.expression expression following continuation rest, ?_, ?_⟩
          · simp only [execute, advanced_not_finished _ _ _ _ _ _ advanced, decoded,
              computed, bind, Option.bind_some]
          · simp only [represent, represented]
      | boundary _ _ _ _ value completed target continued =>
          refine ⟨afterExpression continuation value saved.memory selections, ?_, ?_⟩
          · simp only [execute, (finishedExpression_iff _ _ _).mpr completed]
          · exact afterExpression_complete _ _ _ _ _ continued

theorem execute_iff (policy : SignedConversionPolicy) (before : Configuration model)
    (after : SemanticConfiguration model) (event : Option (Event model)) :
    (∃ saved, execute policy before = some (event, saved) ∧ represent saved = after) ↔
      Step policy (represent before) event after := by
  constructor
  · rintro ⟨saved, computed, rfl⟩
    exact execute_sound _ _ _ _ computed
  · exact execute_complete _ _ _ _

theorem controlStep_administrative_decreases (before after : Configuration model)
    (computed : controlStep before = some (none, after)) : rank after < rank before := by
  cases before with
  | expression _ _ _ _ | returned _ _ _ => cases computed
  | statement statement following memory selections =>
      cases statement with
      | block statements =>
          cases statements <;> simp only [controlStep] at computed <;> cases computed <;>
            (simp only [rank, Continuation.rank, Statement.block.sizeOf_spec,
              List.nil.sizeOf_spec, List.cons.sizeOf_spec]; omega)
      | forLoop initial condition increment body =>
          cases initial <;> cases condition <;> simp only [controlStep, beginFor] at computed <;>
            cases computed <;> (simp only [rank, Continuation.rank, Statement.forLoop.sizeOf_spec]; omega)
      | returnValue value =>
          cases value <;> simp only [controlStep] at computed <;> cases computed <;>
            simp [rank]
      | empty | expression | sequence | conditional | whileLoop | doLoop | breakLoop | continueLoop =>
          simp only [controlStep] at computed
          cases computed
          simp [rank, Continuation.rank] <;> omega
  | flow flow following memory selections =>
      cases following with
      | block statements outer =>
          cases statements <;> cases flow <;> simp only [controlStep] at computed <;>
            cases computed <;> (simp only [rank, Continuation.rank,
              List.nil.sizeOf_spec, List.cons.sizeOf_spec]; omega)
      | stop | sequence | whileBody | doBody | forBody =>
          cases flow <;> simp only [controlStep] at computed <;> cases computed <;>
            simp [rank, Continuation.rank] <;> omega

theorem execute_administrative_decreases (policy : SignedConversionPolicy)
    (before after : Configuration model) (computed : execute policy before = some (none, after)) :
    rank after < rank before := by
  cases before with
  | expression expression saved continuation selections =>
      cases finished : finishedExpression? expression saved with
      | some value => simp only [execute, finished] at computed; cases computed
      | none =>
          cases selections with
          | nil => simp only [execute, finished] at computed; cases computed
          | cons data rest =>
              cases decoded : decodeIndex expression data with
              | none => simp only [execute, finished, decoded, bind, Option.bind_none] at computed; cases computed
              | some index =>
                  cases advanced : ExpressionEventExecution.execute policy (compile expression) saved index with
                  | none => simp only [execute, finished, decoded, advanced, bind, Option.bind_some, Option.bind_none] at computed; cases computed
                  | some result =>
                      rcases result with ⟨outcome, following⟩
                      simp only [execute, finished, decoded, advanced, bind, Option.bind_some] at computed
                      cases computed
  | statement _ _ _ _ | flow _ _ _ _ | returned _ _ _ =>
      exact controlStep_administrative_decreases _ _ (by simpa only [execute] using computed)

end Mettapedia.Languages.C11.StatementExecution
