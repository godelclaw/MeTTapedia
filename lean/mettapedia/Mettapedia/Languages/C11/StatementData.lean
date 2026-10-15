import Mettapedia.Languages.C11.StatementHistory

/-!
# Lossless packets for structured C11 statement execution

The data representation retains arbitrary nested statement syntax, every
continuation and full-expression boundary, concrete byte/catalog memory,
pending occurrences, cached outcomes and the unused scheduling suffix.
Successful decoding establishes structural representation only. It does not
grant execution history, ownership, current-world or publication authority.

Loop-iteration receipts are operational observations for this step interface.
They are neither C11 external effects nor compiled instruction costs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.StatementData

open IntegerMemoryModel LocatedExpressions LocatedStatements
open LocatedExpressionData

variable {model : Model}

mutual
inductive Syntax where
  | empty
  | expression (operand : ExpressionData)
  | sequence (first second : Syntax)
  | block (body : StatementsData)
  | conditional (condition : ExpressionData) (yes no : Syntax)
  | whileLoop (condition : ExpressionData) (body : Syntax)
  | doLoop (body : Syntax) (condition : ExpressionData)
  | forLoop (initial condition increment : Option ExpressionData) (body : Syntax)
  | breakLoop
  | continueLoop
  | returnValue (value : Option ExpressionData)
  deriving DecidableEq, Repr

inductive StatementsData where
  | nil
  | cons (statement : Syntax) (following : StatementsData)
  deriving DecidableEq, Repr
end

def encodeOptional {Source Data : Type} (encode : Source → Data) : Option Source → Option Data
  | none => none
  | some source => some (encode source)

def decodeOptional {Source Data : Type} (decode : Data → Option Source) : Option Data → Option (Option Source)
  | none => some none
  | some data => (decode data).map some

theorem decodeOptional_encode {Source Data : Type} (encode : Source → Data) (decode : Data → Option Source)
    (inverse : ∀ source, decode (encode source) = some source) (source : Option Source) :
    decodeOptional decode (encodeOptional encode source) = some source := by
  cases source <;> simp only [encodeOptional, decodeOptional, inverse, Option.map_some]

theorem encodeOptional_decode {Source Data : Type} (encode : Source → Data) (decode : Data → Option Source)
    (inverse : ∀ data source, decode data = some source → encode source = data)
    (data : Option Data) (source : Option Source) (decoded : decodeOptional decode data = some source) :
    encodeOptional encode source = data := by
  cases data with
  | none => cases decoded; rfl
  | some data =>
      obtain ⟨source, found, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact congrArg some (inverse _ _ found)

mutual
def encodeStatement : Statement model → Syntax
  | .empty => .empty
  | .expression operand => .expression (encodeExpression operand)
  | .sequence first second => .sequence (encodeStatement first) (encodeStatement second)
  | .block body => .block (encodeStatements body)
  | .conditional condition yes no => .conditional (encodeExpression condition) (encodeStatement yes) (encodeStatement no)
  | .whileLoop condition body => .whileLoop (encodeExpression condition) (encodeStatement body)
  | .doLoop body condition => .doLoop (encodeStatement body) (encodeExpression condition)
  | .forLoop initial condition increment body => .forLoop
      (encodeOptional encodeExpression initial) (encodeOptional encodeExpression condition)
      (encodeOptional encodeExpression increment) (encodeStatement body)
  | .breakLoop => .breakLoop
  | .continueLoop => .continueLoop
  | .returnValue value => .returnValue (encodeOptional encodeExpression value)
termination_by structural statement => statement

def encodeStatements : List (Statement model) → StatementsData
  | [] => .nil
  | statement :: rest => .cons (encodeStatement statement) (encodeStatements rest)
termination_by structural statements => statements
end

mutual
def decodeStatement (model : Model) : Syntax → Option (Statement model)
  | .empty => some .empty
  | .expression operand => (decodeExpression model operand).map Statement.expression
  | .sequence first second => do some (.sequence (← decodeStatement model first) (← decodeStatement model second))
  | .block body => (decodeStatements model body).map Statement.block
  | .conditional condition yes no => do
      some (.conditional (← decodeExpression model condition) (← decodeStatement model yes) (← decodeStatement model no))
  | .whileLoop condition body => do some (.whileLoop (← decodeExpression model condition) (← decodeStatement model body))
  | .doLoop body condition => do some (.doLoop (← decodeStatement model body) (← decodeExpression model condition))
  | .forLoop initial condition increment body => do some (.forLoop
      (← decodeOptional (decodeExpression model) initial) (← decodeOptional (decodeExpression model) condition)
      (← decodeOptional (decodeExpression model) increment) (← decodeStatement model body))
  | .breakLoop => some .breakLoop
  | .continueLoop => some .continueLoop
  | .returnValue value => (decodeOptional (decodeExpression model) value).map Statement.returnValue
termination_by structural statement => statement

def decodeStatements (model : Model) : StatementsData → Option (List (Statement model))
  | .nil => some []
  | .cons statement rest => do some ((← decodeStatement model statement) :: (← decodeStatements model rest))
termination_by structural statements => statements
end

mutual
theorem decodeStatement_encode (model : Model) (statement : Statement model) :
    decodeStatement model (encodeStatement statement) = some statement := by
  cases statement <;> simp only [encodeStatement, decodeStatement, decodeExpression_encode,
    decodeStatement_encode, decodeStatements_encode, decodeOptional_encode encodeExpression (decodeExpression model) (decodeExpression_encode model),
    Option.map_some, bind, Option.bind_some]
termination_by structural statement

theorem decodeStatements_encode (model : Model) (statements : List (Statement model)) :
    decodeStatements model (encodeStatements statements) = some statements := by
  cases statements <;> simp only [encodeStatements, decodeStatements, decodeStatement_encode,
    decodeStatements_encode, bind, Option.bind_some]
termination_by structural statements
end

mutual
theorem encodeStatement_decode (model : Model) (data : Syntax) (statement : Statement model)
    (decoded : decodeStatement model data = some statement) : encodeStatement statement = data := by
  cases data with
  | empty | breakLoop | continueLoop => cases decoded; rfl
  | expression operand =>
      obtain ⟨source, found, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact congrArg Syntax.expression (encodeExpression_decode _ _ _ found)
  | block body =>
      obtain ⟨statements, found, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact congrArg Syntax.block (encodeStatements_decode _ _ _ found)
  | sequence first second =>
      simp only [decodeStatement, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨left, leftRead, right, rightRead, rfl⟩ := decoded
      simp only [encodeStatement, encodeStatement_decode _ _ _ leftRead, encodeStatement_decode _ _ _ rightRead]
  | conditional condition yes no =>
      simp only [decodeStatement, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨test, testRead, first, firstRead, second, secondRead, rfl⟩ := decoded
      simp only [encodeStatement, encodeExpression_decode _ _ _ testRead,
        encodeStatement_decode _ _ _ firstRead, encodeStatement_decode _ _ _ secondRead]
  | whileLoop condition body =>
      simp only [decodeStatement, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨test, testRead, source, sourceRead, rfl⟩ := decoded
      simp only [encodeStatement, encodeExpression_decode _ _ _ testRead, encodeStatement_decode _ _ _ sourceRead]
  | doLoop body condition =>
      simp only [decodeStatement, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨source, sourceRead, test, testRead, rfl⟩ := decoded
      simp only [encodeStatement, encodeStatement_decode _ _ _ sourceRead, encodeExpression_decode _ _ _ testRead]
  | forLoop initial condition increment body =>
      simp only [decodeStatement, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨start, startRead, test, testRead, update, updateRead, source, sourceRead, rfl⟩ := decoded
      simp only [encodeStatement, encodeOptional_decode _ _ (encodeExpression_decode model) _ _ startRead,
        encodeOptional_decode _ _ (encodeExpression_decode model) _ _ testRead,
        encodeOptional_decode _ _ (encodeExpression_decode model) _ _ updateRead,
        encodeStatement_decode _ _ _ sourceRead]
  | returnValue value =>
      obtain ⟨source, found, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact congrArg Syntax.returnValue
        (encodeOptional_decode _ _ (encodeExpression_decode model) _ _ found)
termination_by structural data

theorem encodeStatements_decode (model : Model) (data : StatementsData) (statements : List (Statement model))
    (decoded : decodeStatements model data = some statements) : encodeStatements statements = data := by
  cases data with
  | nil => cases decoded; rfl
  | cons data rest =>
      simp only [decodeStatements, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨source, sourceRead, following, followingRead, rfl⟩ := decoded
      simp only [encodeStatements, encodeStatement_decode _ _ _ sourceRead, encodeStatements_decode _ _ _ followingRead]
termination_by structural data
end

inductive ContinuationData where
  | stop
  | sequence (following : Syntax) (outer : ContinuationData)
  | block (following : StatementsData) (outer : ContinuationData)
  | whileBody (condition : ExpressionData) (body : Syntax) (outer : ContinuationData)
  | doBody (body : Syntax) (condition : ExpressionData) (outer : ContinuationData)
  | forBody (condition increment : Option ExpressionData) (body : Syntax) (outer : ContinuationData)
  deriving DecidableEq, Repr

def encodeContinuation : Continuation model → ContinuationData
  | .stop => .stop
  | .sequence following outer => .sequence (encodeStatement following) (encodeContinuation outer)
  | .block following outer => .block (encodeStatements following) (encodeContinuation outer)
  | .whileBody condition body outer => .whileBody (encodeExpression condition) (encodeStatement body) (encodeContinuation outer)
  | .doBody body condition outer => .doBody (encodeStatement body) (encodeExpression condition) (encodeContinuation outer)
  | .forBody condition increment body outer => .forBody (encodeOptional encodeExpression condition)
      (encodeOptional encodeExpression increment) (encodeStatement body) (encodeContinuation outer)

def decodeContinuation (model : Model) : ContinuationData → Option (Continuation model)
  | .stop => some .stop
  | .sequence following outer => do some (.sequence (← decodeStatement model following) (← decodeContinuation model outer))
  | .block following outer => do some (.block (← decodeStatements model following) (← decodeContinuation model outer))
  | .whileBody condition body outer => do some (.whileBody
      (← decodeExpression model condition) (← decodeStatement model body) (← decodeContinuation model outer))
  | .doBody body condition outer => do some (.doBody
      (← decodeStatement model body) (← decodeExpression model condition) (← decodeContinuation model outer))
  | .forBody condition increment body outer => do some (.forBody
      (← decodeOptional (decodeExpression model) condition) (← decodeOptional (decodeExpression model) increment)
      (← decodeStatement model body) (← decodeContinuation model outer))

theorem decodeContinuation_encode (model : Model) (continuation : Continuation model) :
    decodeContinuation model (encodeContinuation continuation) = some continuation := by
  induction continuation <;> simp_all only [encodeContinuation, decodeContinuation, decodeStatement_encode,
    decodeStatements_encode, decodeExpression_encode, decodeOptional_encode encodeExpression (decodeExpression model) (decodeExpression_encode model),
    bind, Option.bind_some]

theorem encodeContinuation_decode (model : Model) (data : ContinuationData) (continuation : Continuation model)
    (decoded : decodeContinuation model data = some continuation) : encodeContinuation continuation = data := by
  induction data generalizing continuation with
  | stop => cases decoded; rfl
  | sequence following outer ih =>
      simp only [decodeContinuation, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨source, sourceRead, rest, restRead, rfl⟩ := decoded
      simp only [encodeContinuation, encodeStatement_decode _ _ _ sourceRead, ih _ restRead]
  | block following outer ih =>
      simp only [decodeContinuation, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨source, sourceRead, rest, restRead, rfl⟩ := decoded
      simp only [encodeContinuation, encodeStatements_decode _ _ _ sourceRead, ih _ restRead]
  | whileBody condition body outer ih =>
      simp only [decodeContinuation, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨test, testRead, source, sourceRead, rest, restRead, rfl⟩ := decoded
      simp only [encodeContinuation, encodeExpression_decode _ _ _ testRead, encodeStatement_decode _ _ _ sourceRead, ih _ restRead]
  | doBody body condition outer ih =>
      simp only [decodeContinuation, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨source, sourceRead, test, testRead, rest, restRead, rfl⟩ := decoded
      simp only [encodeContinuation, encodeStatement_decode _ _ _ sourceRead, encodeExpression_decode _ _ _ testRead, ih _ restRead]
  | forBody condition increment body outer ih =>
      simp only [decodeContinuation, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨test, testRead, update, updateRead, source, sourceRead, rest, restRead, rfl⟩ := decoded
      simp only [encodeContinuation, encodeOptional_decode _ _ (encodeExpression_decode model) _ _ testRead,
        encodeOptional_decode _ _ (encodeExpression_decode model) _ _ updateRead,
        encodeStatement_decode _ _ _ sourceRead, ih _ restRead]

inductive AfterExpressionData where
  | discard (following : ContinuationData)
  | conditional (yes no : Syntax) (following : ContinuationData)
  | whileCondition (condition : ExpressionData) (body : Syntax) (following : ContinuationData)
  | doCondition (body : Syntax) (condition : ExpressionData) (following : ContinuationData)
  | forInitial (condition increment : Option ExpressionData) (body : Syntax) (following : ContinuationData)
  | forCondition (condition increment : Option ExpressionData) (body : Syntax) (following : ContinuationData)
  | forIncrement (condition increment : Option ExpressionData) (body : Syntax) (following : ContinuationData)
  | returnValue
  deriving DecidableEq, Repr

def encodeAfterExpression : AfterExpression model → AfterExpressionData
  | .discard following => .discard (encodeContinuation following)
  | .conditional yes no following => .conditional (encodeStatement yes) (encodeStatement no) (encodeContinuation following)
  | .whileCondition condition body following => .whileCondition
      (encodeExpression condition) (encodeStatement body) (encodeContinuation following)
  | .doCondition body condition following => .doCondition
      (encodeStatement body) (encodeExpression condition) (encodeContinuation following)
  | .forInitial condition increment body following => .forInitial (encodeOptional encodeExpression condition)
      (encodeOptional encodeExpression increment) (encodeStatement body) (encodeContinuation following)
  | .forCondition condition increment body following => .forCondition (encodeOptional encodeExpression condition)
      (encodeOptional encodeExpression increment) (encodeStatement body) (encodeContinuation following)
  | .forIncrement condition increment body following => .forIncrement (encodeOptional encodeExpression condition)
      (encodeOptional encodeExpression increment) (encodeStatement body) (encodeContinuation following)
  | .returnValue => .returnValue

def decodeAfterExpression (model : Model) : AfterExpressionData → Option (AfterExpression model)
  | .discard following => (decodeContinuation model following).map AfterExpression.discard
  | .conditional yes no following => do some (.conditional
      (← decodeStatement model yes) (← decodeStatement model no) (← decodeContinuation model following))
  | .whileCondition condition body following => do some (.whileCondition
      (← decodeExpression model condition) (← decodeStatement model body) (← decodeContinuation model following))
  | .doCondition body condition following => do some (.doCondition
      (← decodeStatement model body) (← decodeExpression model condition) (← decodeContinuation model following))
  | .forInitial condition increment body following => do some (.forInitial
      (← decodeOptional (decodeExpression model) condition) (← decodeOptional (decodeExpression model) increment)
      (← decodeStatement model body) (← decodeContinuation model following))
  | .forCondition condition increment body following => do some (.forCondition
      (← decodeOptional (decodeExpression model) condition) (← decodeOptional (decodeExpression model) increment)
      (← decodeStatement model body) (← decodeContinuation model following))
  | .forIncrement condition increment body following => do some (.forIncrement
      (← decodeOptional (decodeExpression model) condition) (← decodeOptional (decodeExpression model) increment)
      (← decodeStatement model body) (← decodeContinuation model following))
  | .returnValue => some .returnValue

theorem decodeAfterExpression_encode (model : Model) (following : AfterExpression model) :
    decodeAfterExpression model (encodeAfterExpression following) = some following := by
  cases following <;> simp only [encodeAfterExpression, decodeAfterExpression, decodeContinuation_encode,
    decodeStatement_encode, decodeExpression_encode, decodeOptional_encode encodeExpression (decodeExpression model) (decodeExpression_encode model), Option.map_some, bind, Option.bind_some]

theorem encodeAfterExpression_decode (model : Model) (data : AfterExpressionData) (following : AfterExpression model)
    (decoded : decodeAfterExpression model data = some following) : encodeAfterExpression following = data := by
  cases data with
  | returnValue => cases decoded; rfl
  | discard continuation =>
      obtain ⟨source, found, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact congrArg AfterExpressionData.discard (encodeContinuation_decode _ _ _ found)
  | conditional yes no continuation =>
      simp only [decodeAfterExpression, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨first, firstRead, second, secondRead, rest, restRead, rfl⟩ := decoded
      simp only [encodeAfterExpression, encodeStatement_decode _ _ _ firstRead,
        encodeStatement_decode _ _ _ secondRead, encodeContinuation_decode _ _ _ restRead]
  | whileCondition condition body continuation =>
      simp only [decodeAfterExpression, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨test, testRead, source, sourceRead, rest, restRead, rfl⟩ := decoded
      simp only [encodeAfterExpression, encodeExpression_decode _ _ _ testRead,
        encodeStatement_decode _ _ _ sourceRead, encodeContinuation_decode _ _ _ restRead]
  | doCondition body condition continuation =>
      simp only [decodeAfterExpression, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨source, sourceRead, test, testRead, rest, restRead, rfl⟩ := decoded
      simp only [encodeAfterExpression, encodeStatement_decode _ _ _ sourceRead,
        encodeExpression_decode _ _ _ testRead, encodeContinuation_decode _ _ _ restRead]
  | forInitial condition increment body continuation
  | forCondition condition increment body continuation
  | forIncrement condition increment body continuation =>
      simp only [decodeAfterExpression, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨test, testRead, update, updateRead, source, sourceRead, rest, restRead, rfl⟩ := decoded
      simp only [encodeAfterExpression, encodeOptional_decode _ _ (encodeExpression_decode model) _ _ testRead,
        encodeOptional_decode _ _ (encodeExpression_decode model) _ _ updateRead,
        encodeStatement_decode _ _ _ sourceRead, encodeContinuation_decode _ _ _ restRead]

inductive ConfigurationData where
  | statement (statement : Syntax) (continuation : ContinuationData) (memory : MemoryData) (selections : List IndexData)
  | flow (flow : Flow) (continuation : ContinuationData) (memory : MemoryData) (selections : List IndexData)
  | expression (expression : ExpressionData) (saved : StateData) (following : AfterExpressionData) (selections : List IndexData)
  | returned (value : Option ScalarData) (memory : MemoryData) (selections : List IndexData)
  deriving DecidableEq, Repr

def encodeConfiguration : Configuration model → ConfigurationData
  | .statement statement continuation memory selections => .statement
      (encodeStatement statement) (encodeContinuation continuation) (encodeMemory memory) selections
  | .flow flow continuation memory selections => .flow flow (encodeContinuation continuation) (encodeMemory memory) selections
  | .expression expression saved following selections => .expression
      (encodeExpression expression) (encodeState expression saved) (encodeAfterExpression following) selections
  | .returned value memory selections => .returned (encodeOptional encodeScalar value) (encodeMemory memory) selections

def decodeConfiguration (model : Model) : ConfigurationData → Option (Configuration model)
  | .statement statement continuation memory selections => do some (.statement
      (← decodeStatement model statement) (← decodeContinuation model continuation) (← decodeMemory model memory) selections)
  | .flow flow continuation memory selections => do some (.flow flow
      (← decodeContinuation model continuation) (← decodeMemory model memory) selections)
  | .expression expression saved following selections => do
      let source ← decodeExpression model expression
      some (.expression source (← decodeState source saved) (← decodeAfterExpression model following) selections)
  | .returned value memory selections => do some (.returned
      (← decodeOptional (decodeScalar model) value) (← decodeMemory model memory) selections)

theorem decodeConfiguration_encode (model : Model) (configuration : Configuration model) :
    decodeConfiguration model (encodeConfiguration configuration) = some configuration := by
  cases configuration <;> simp only [encodeConfiguration, decodeConfiguration, decodeStatement_encode,
    decodeContinuation_encode, decodeMemory_encode, decodeExpression_encode, decodeState_encode,
    decodeAfterExpression_encode, decodeOptional_encode encodeScalar (decodeScalar model) (decodeScalar_encode model), bind, Option.bind_some]

theorem encodeConfiguration_decode (model : Model) (data : ConfigurationData) (configuration : Configuration model)
    (decoded : decodeConfiguration model data = some configuration) : encodeConfiguration configuration = data := by
  cases data with
  | statement statement continuation memory selections =>
      simp only [decodeConfiguration, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨source, sourceRead, rest, restRead, storage, storageRead, rfl⟩ := decoded
      simp only [encodeConfiguration, encodeStatement_decode _ _ _ sourceRead,
        encodeContinuation_decode _ _ _ restRead, encodeMemory_decode _ _ _ storageRead]
  | flow flow continuation memory selections =>
      simp only [decodeConfiguration, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨rest, restRead, storage, storageRead, rfl⟩ := decoded
      simp only [encodeConfiguration, encodeContinuation_decode _ _ _ restRead, encodeMemory_decode _ _ _ storageRead]
  | expression expression saved following selections =>
      simp only [decodeConfiguration, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨source, sourceRead, state, stateRead, rest, restRead, rfl⟩ := decoded
      simp only [encodeConfiguration, encodeExpression_decode _ _ _ sourceRead,
        encodeState_decode _ _ _ stateRead, encodeAfterExpression_decode _ _ _ restRead]
  | returned value memory selections =>
      simp only [decodeConfiguration, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨result, resultRead, storage, storageRead, rfl⟩ := decoded
      simp only [encodeConfiguration, encodeOptional_decode _ _ (encodeScalar_decode model) _ _ resultRead,
        encodeMemory_decode _ _ _ storageRead]

theorem encodeConfiguration_injective (model : Model) : Function.Injective (@encodeConfiguration model) := by
  intro first second same
  have decoded := congrArg (decodeConfiguration model) same
  rw [decodeConfiguration_encode, decodeConfiguration_encode] at decoded
  exact Option.some.inj decoded

end Mettapedia.Languages.C11.StatementData
