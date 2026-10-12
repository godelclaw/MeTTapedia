import Mettapedia.Languages.C11.CestaLocatedExpressions
import Mettapedia.Languages.C11.StatementHistory

/-!
# Cesta statement syntax into retained C11 control

The reader follows the existing CStmt constructors, including the separate
selection, iteration and jump wrappers and ordered block-item list. Expression
formation uses the checked Cesta integer-expression adapter. Statement and
block depth are unrestricted. Declarations, labels, switch and goto require
additional control and lifetime components and are not silently erased.

The ordinary parser and selection of a canonical parse remain separate from
this elaboration of a selected canonical statement tree.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.CestaStatements

open Mettapedia.GSLT.Parsing.CanonicalGrammar (CanonicalTerm)
open Mettapedia.GSLT.Parsing.SortedCanonicalSExprCodec
open IntegerMemoryModel LocatedExpressions LocatedStatements

def readOptional (model : Model) (environment : ScopedLvalues.Environment) :
    CanonicalTerm → Option (Option (Expression model))
  | .node "NoFullExpression" [] => some none
  | .node "SomeFullExpression" [operand] =>
      (CestaLocatedExpressions.readTerm model environment operand).map some
  | _ => none

inductive OptionalReading (model : Model) (environment : ScopedLvalues.Environment) :
    CanonicalTerm → Option (Expression model) → Prop where
  | omitted : OptionalReading model environment (.node "NoFullExpression" []) none
  | present (term : CanonicalTerm) (expression : Expression model)
      (reading : CestaLocatedExpressions.TermReading model environment term expression) :
      OptionalReading model environment (.node "SomeFullExpression" [term]) (some expression)

theorem readOptional_iff (model : Model) (environment : ScopedLvalues.Environment)
    (term : CanonicalTerm) (expression : Option (Expression model)) :
    readOptional model environment term = some expression ↔ OptionalReading model environment term expression := by
  constructor
  · intro parsed
    unfold readOptional at parsed
    split at parsed
    · cases parsed; exact .omitted
    · rename_i operand
      obtain ⟨selected, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
      exact .present _ _ (CestaLocatedExpressions.readTerm_sound _ _ _ _ found)
    · contradiction
  · intro reading
    cases reading with
    | omitted => rfl
    | present term expression reading =>
        simp only [readOptional, CestaLocatedExpressions.readTerm_complete _ _ _ _ reading, Option.map_some]

def optionalStatement {model : Model} : Option (Expression model) → Statement model
  | none => .empty
  | some expression => .expression expression

mutual
def readStatement (model : Model) (environment : ScopedLvalues.Environment) : CanonicalTerm → Option (Statement model)
  | .node "CompoundStatement" [.node "Block" [.seq items]] =>
      (readItems model environment items).map Statement.block
  | .node "ExpressionStatement" [optional] => (readOptional model environment optional).map optionalStatement
  | .node "SelectionStatement" [.node "If" [condition, yes]] => do
      some (.conditional (← CestaLocatedExpressions.readTerm model environment condition)
        (← readStatement model environment yes) .empty)
  | .node "SelectionStatement" [.node "IfElse" [condition, yes, no]] => do
      some (.conditional (← CestaLocatedExpressions.readTerm model environment condition)
        (← readStatement model environment yes) (← readStatement model environment no))
  | .node "IterationStatement" [.node "While" [condition, body]] => do
      some (.whileLoop (← CestaLocatedExpressions.readTerm model environment condition)
        (← readStatement model environment body))
  | .node "IterationStatement" [.node "DoWhile" [body, condition]] => do
      some (.doLoop (← readStatement model environment body)
        (← CestaLocatedExpressions.readTerm model environment condition))
  | .node "IterationStatement" [.node "For" [initial, condition, increment, body]] => do
      some (.forLoop (← readOptional model environment initial) (← readOptional model environment condition)
        (← readOptional model environment increment) (← readStatement model environment body))
  | .node "JumpStatement" [.node "Continue" []] => some .continueLoop
  | .node "JumpStatement" [.node "Break" []] => some .breakLoop
  | .node "JumpStatement" [.node "Return" [optional]] =>
      (readOptional model environment optional).map Statement.returnValue
  | _ => none
termination_by term => sizeOf term

def readItems (model : Model) (environment : ScopedLvalues.Environment) :
    List CanonicalTerm → Option (List (Statement model))
  | [] => some []
  | .node "BlockStatement" [term] :: rest => do
      let statement ← readStatement model environment term
      let statements ← readItems model environment rest
      some (statement :: statements)
  | _ => none
termination_by items => sizeOf items
end

mutual
inductive Reading (model : Model) (environment : ScopedLvalues.Environment) :
    CanonicalTerm → Statement model → Prop where
  | compound (items : List CanonicalTerm) (statements : List (Statement model))
      (children : ItemsReading model environment items statements) :
      Reading model environment (.node "CompoundStatement" [.node "Block" [.seq items]]) (.block statements)
  | expression (optional : CanonicalTerm) (expression : Option (Expression model))
      (operand : OptionalReading model environment optional expression) :
      Reading model environment (.node "ExpressionStatement" [optional]) (optionalStatement expression)
  | conditional (condition yes : CanonicalTerm) (test : Expression model) (body : Statement model)
      (conditionReading : CestaLocatedExpressions.TermReading model environment condition test)
      (bodyReading : Reading model environment yes body) :
      Reading model environment (.node "SelectionStatement" [.node "If" [condition, yes]]) (.conditional test body .empty)
  | conditionalElse (condition yes no : CanonicalTerm) (test : Expression model) (first second : Statement model)
      (conditionReading : CestaLocatedExpressions.TermReading model environment condition test)
      (yesReading : Reading model environment yes first) (noReading : Reading model environment no second) :
      Reading model environment (.node "SelectionStatement" [.node "IfElse" [condition, yes, no]])
        (.conditional test first second)
  | whileLoop (condition body : CanonicalTerm) (test : Expression model) (statement : Statement model)
      (conditionReading : CestaLocatedExpressions.TermReading model environment condition test)
      (bodyReading : Reading model environment body statement) :
      Reading model environment (.node "IterationStatement" [.node "While" [condition, body]]) (.whileLoop test statement)
  | doLoop (body condition : CanonicalTerm) (statement : Statement model) (test : Expression model)
      (bodyReading : Reading model environment body statement)
      (conditionReading : CestaLocatedExpressions.TermReading model environment condition test) :
      Reading model environment (.node "IterationStatement" [.node "DoWhile" [body, condition]]) (.doLoop statement test)
  | forLoop (initial condition increment body : CanonicalTerm) (start test update : Option (Expression model))
      (statement : Statement model) (initialReading : OptionalReading model environment initial start)
      (conditionReading : OptionalReading model environment condition test)
      (incrementReading : OptionalReading model environment increment update)
      (bodyReading : Reading model environment body statement) :
      Reading model environment (.node "IterationStatement" [.node "For" [initial, condition, increment, body]])
        (.forLoop start test update statement)
  | continueLoop : Reading model environment (.node "JumpStatement" [.node "Continue" []]) .continueLoop
  | breakLoop : Reading model environment (.node "JumpStatement" [.node "Break" []]) .breakLoop
  | returnValue (optional : CanonicalTerm) (expression : Option (Expression model))
      (operand : OptionalReading model environment optional expression) :
      Reading model environment (.node "JumpStatement" [.node "Return" [optional]]) (.returnValue expression)

inductive ItemsReading (model : Model) (environment : ScopedLvalues.Environment) :
    List CanonicalTerm → List (Statement model) → Prop where
  | nil : ItemsReading model environment [] []
  | cons (term : CanonicalTerm) (rest : List CanonicalTerm) (statement : Statement model)
      (statements : List (Statement model)) (head : Reading model environment term statement)
      (tail : ItemsReading model environment rest statements) :
      ItemsReading model environment (.node "BlockStatement" [term] :: rest) (statement :: statements)
end

mutual
theorem readStatement_sound (model : Model) (environment : ScopedLvalues.Environment)
    (term : CanonicalTerm) (statement : Statement model) (parsed : readStatement model environment term = some statement) :
    Reading model environment term statement := by
  unfold readStatement at parsed
  split at parsed
  · rename_i items
    obtain ⟨statements, read, rfl⟩ := Option.map_eq_some_iff.mp parsed
    exact .compound _ _ (readItems_sound _ _ _ _ read)
  · rename_i optional
    obtain ⟨expression, read, rfl⟩ := Option.map_eq_some_iff.mp parsed
    exact .expression _ _ ((readOptional_iff _ _ _ _).mp read)
  · rename_i condition yes
    simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨test, testRead, body, bodyRead, rfl⟩ := parsed
    exact .conditional _ _ _ _ (CestaLocatedExpressions.readTerm_sound _ _ _ _ testRead)
      (readStatement_sound _ _ _ _ bodyRead)
  · rename_i condition yes no
    simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨test, testRead, first, firstRead, second, secondRead, rfl⟩ := parsed
    exact .conditionalElse _ _ _ _ _ _ (CestaLocatedExpressions.readTerm_sound _ _ _ _ testRead)
      (readStatement_sound _ _ _ _ firstRead) (readStatement_sound _ _ _ _ secondRead)
  · rename_i condition body
    simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨test, testRead, statement, bodyRead, rfl⟩ := parsed
    exact .whileLoop _ _ _ _ (CestaLocatedExpressions.readTerm_sound _ _ _ _ testRead)
      (readStatement_sound _ _ _ _ bodyRead)
  · rename_i body condition
    simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨statement, bodyRead, test, testRead, rfl⟩ := parsed
    exact .doLoop _ _ _ _ (readStatement_sound _ _ _ _ bodyRead)
      (CestaLocatedExpressions.readTerm_sound _ _ _ _ testRead)
  · rename_i initial condition increment body
    simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨start, startRead, test, testRead, update, updateRead, statement, bodyRead, rfl⟩ := parsed
    exact .forLoop _ _ _ _ _ _ _ _ ((readOptional_iff _ _ _ _).mp startRead)
      ((readOptional_iff _ _ _ _).mp testRead) ((readOptional_iff _ _ _ _).mp updateRead)
      (readStatement_sound _ _ _ _ bodyRead)
  · cases parsed; exact .continueLoop
  · cases parsed; exact .breakLoop
  · rename_i optional
    obtain ⟨expression, read, rfl⟩ := Option.map_eq_some_iff.mp parsed
    exact .returnValue _ _ ((readOptional_iff _ _ _ _).mp read)
  · contradiction
termination_by sizeOf term

theorem readItems_sound (model : Model) (environment : ScopedLvalues.Environment)
    (items : List CanonicalTerm) (statements : List (Statement model))
    (parsed : readItems model environment items = some statements) : ItemsReading model environment items statements := by
  unfold readItems at parsed
  split at parsed
  · cases parsed; exact .nil
  · rename_i term rest
    simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨statement, head, statements, tail, rfl⟩ := parsed
    exact .cons _ _ _ _ (readStatement_sound _ _ _ _ head) (readItems_sound _ _ _ _ tail)
  · contradiction
termination_by sizeOf items
end

mutual
theorem readStatement_complete (model : Model) (environment : ScopedLvalues.Environment)
    (term : CanonicalTerm) (statement : Statement model) (reading : Reading model environment term statement) :
    readStatement model environment term = some statement := by
  cases reading with
  | compound items statements children =>
      simp only [readStatement, readItems_complete _ _ _ _ children, Option.map_some]
  | expression optional expression operand =>
      simp only [readStatement, (readOptional_iff _ _ _ _).mpr operand, Option.map_some]
  | conditional condition yes test body conditionReading bodyReading =>
      simp only [readStatement, CestaLocatedExpressions.readTerm_complete _ _ _ _ conditionReading,
        readStatement_complete _ _ _ _ bodyReading, bind, Option.bind_some]
  | conditionalElse condition yes no test first second conditionReading yesReading noReading =>
      simp only [readStatement, CestaLocatedExpressions.readTerm_complete _ _ _ _ conditionReading,
        readStatement_complete _ _ _ _ yesReading, readStatement_complete _ _ _ _ noReading, bind, Option.bind_some]
  | whileLoop condition body test statement conditionReading bodyReading =>
      simp only [readStatement, CestaLocatedExpressions.readTerm_complete _ _ _ _ conditionReading,
        readStatement_complete _ _ _ _ bodyReading, bind, Option.bind_some]
  | doLoop body condition statement test bodyReading conditionReading =>
      simp only [readStatement, readStatement_complete _ _ _ _ bodyReading,
        CestaLocatedExpressions.readTerm_complete _ _ _ _ conditionReading, bind, Option.bind_some]
  | forLoop initial condition increment body start test update statement initialReading conditionReading incrementReading bodyReading =>
      simp only [readStatement, (readOptional_iff _ _ _ _).mpr initialReading,
        (readOptional_iff _ _ _ _).mpr conditionReading, (readOptional_iff _ _ _ _).mpr incrementReading,
        readStatement_complete _ _ _ _ bodyReading, bind, Option.bind_some]
  | continueLoop | breakLoop => simp only [readStatement]
  | returnValue optional expression operand =>
      simp only [readStatement, (readOptional_iff _ _ _ _).mpr operand, Option.map_some]
termination_by sizeOf term

theorem readItems_complete (model : Model) (environment : ScopedLvalues.Environment)
    (items : List CanonicalTerm) (statements : List (Statement model))
    (reading : ItemsReading model environment items statements) : readItems model environment items = some statements := by
  cases reading with
  | nil => simp only [readItems]
  | cons term rest statement statements head tail =>
      simp only [readItems, readStatement_complete _ _ _ _ head,
        readItems_complete _ _ _ _ tail, bind, Option.bind_some]
termination_by sizeOf items
end

theorem readStatement_iff (model : Model) (environment : ScopedLvalues.Environment)
    (term : CanonicalTerm) (statement : Statement model) :
    readStatement model environment term = some statement ↔ Reading model environment term statement :=
  ⟨readStatement_sound _ _ _ _, readStatement_complete _ _ _ _⟩

abbrev Wire := CestaLocatedExpressions.Wire

def read (schema : Schema) (codecProfile : Notation) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) : Option (Statement model) := do
  let term ← decode? schema codecProfile "Statement" wire
  readStatement model environment term

def WireReading (schema : Schema) (codecProfile : Notation) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (statement : Statement model) : Prop :=
  ∃ term, Sorted schema codecProfile "Statement" term ∧
    encode? schema codecProfile "Statement" term = some wire ∧ Reading model environment term statement

theorem read_sound (schema : Schema) (codecProfile : Notation) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (statement : Statement model)
    (parsed : read schema codecProfile model environment wire = some statement) :
    WireReading schema codecProfile model environment wire statement := by
  obtain ⟨term, decoded, formed⟩ := Option.bind_eq_some_iff.mp parsed
  exact ⟨term, decode_sorted _ _ _ _ _ decoded, encode_decoded _ _ _ _ _ decoded,
    readStatement_sound _ _ _ _ formed⟩

theorem read_complete (schema : Schema) (codecProfile : Notation) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (statement : Statement model)
    (formed : WireReading schema codecProfile model environment wire statement) :
    read schema codecProfile model environment wire = some statement := by
  obtain ⟨term, _, encoded, reading⟩ := formed
  simp only [read, decode_encoded _ _ _ _ _ encoded, readStatement_complete _ _ _ _ reading,
    bind, Option.bind_some]

theorem read_iff (schema : Schema) (codecProfile : Notation) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (statement : Statement model) :
    read schema codecProfile model environment wire = some statement ↔
      WireReading schema codecProfile model environment wire statement :=
  ⟨read_sound _ _ _ _ _ _, read_complete _ _ _ _ _ _⟩

end Mettapedia.Languages.C11.CestaStatements
