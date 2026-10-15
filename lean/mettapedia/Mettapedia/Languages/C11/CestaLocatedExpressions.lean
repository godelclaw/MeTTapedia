import Mettapedia.Languages.C11.CestaExpressionElaboration
import Mettapedia.Languages.C11.LocatedExpressionData

/-!
# Selected Cesta expressions into located source syntax

The canonical CExpr constructors are elaborated into the existing located
integer-expression syntax. Identifier destinations are resolved through the
retained scoped environment. Assignment and update operands must be integer
identifier lvalues. The sorted codec validates constructor declarations,
ordered arguments and lexical spellings before elaboration.

This boundary starts at a selected canonical tree. The byte parser, native
lexical implementation, full C declaration elaboration and non-integer
expression forms require their own correspondence. No native compiler or
external-memory authority is inferred from successful syntax admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.CestaLocatedExpressions

open Mettapedia.GSLT.Parsing.CanonicalGrammar (CanonicalTerm)
open Mettapedia.GSLT.Parsing.SortedCanonicalSExprCodec
open ObjectAccessMemory IntegerMemoryModel LocatedExpressions CestaExpressionElaboration

def binaryHead : IntegerBinaryOperator → String
  | .add => "Add"
  | .subtract => "Subtract"
  | .multiply => "Multiply"
  | .divide => "Divide"
  | .remainder => "Remainder"

def binaryOperator? : String → Option IntegerBinaryOperator
  | "Add" => some .add
  | "Subtract" => some .subtract
  | "Multiply" => some .multiply
  | "Divide" => some .divide
  | "Remainder" => some .remainder
  | _ => none

inductive BinaryHead : String → IntegerBinaryOperator → Prop where
  | arithmetic (operator : IntegerBinaryOperator) : BinaryHead (binaryHead operator) operator

theorem binaryOperator_complete (name : String) (operator : IntegerBinaryOperator)
    (head : BinaryHead name operator) : binaryOperator? name = some operator := by
  cases head with
  | arithmetic operator => cases operator <;> rfl

theorem binaryOperator_sound (name : String) (operator : IntegerBinaryOperator)
    (parsed : binaryOperator? name = some operator) : BinaryHead name operator := by
  unfold binaryOperator? at parsed
  split at parsed <;> first
    | contradiction
    | (cases parsed; first
        | exact .arithmetic .add
        | exact .arithmetic .subtract
        | exact .arithmetic .multiply
        | exact .arithmetic .divide
        | exact .arithmetic .remainder)

def updateFlags? : String → Option (Bool × Bool)
  | "PreIncrement" => some (true, true)
  | "PreDecrement" => some (false, true)
  | "PostIncrement" => some (true, false)
  | "PostDecrement" => some (false, false)
  | _ => none

inductive UpdateHead : String → Bool → Bool → Prop where
  | preIncrement : UpdateHead "PreIncrement" true true
  | preDecrement : UpdateHead "PreDecrement" false true
  | postIncrement : UpdateHead "PostIncrement" true false
  | postDecrement : UpdateHead "PostDecrement" false false

theorem updateFlags_sound (name : String) (increment isPrefix : Bool)
    (parsed : updateFlags? name = some (increment, isPrefix)) : UpdateHead name increment isPrefix := by
  unfold updateFlags? at parsed
  split at parsed <;> first
    | contradiction
    | (cases parsed; constructor)

theorem updateFlags_complete (name : String) (increment isPrefix : Bool)
    (head : UpdateHead name increment isPrefix) : updateFlags? name = some (increment, isPrefix) := by
  cases head <;> rfl

def lvalue? (environment : ScopedLvalues.Environment) : CanonicalTerm → Option Destination
  | .node "Var" [.text name] => namedDestination? environment name
  | _ => none

inductive LvalueReading (environment : ScopedLvalues.Environment) : CanonicalTerm → Destination → Prop where
  | identifier (name : String) (selected : Destination) (bound : NamedDestination environment name selected) :
      LvalueReading environment (.node "Var" [.text name]) selected

theorem lvalue_sound (environment : ScopedLvalues.Environment) (term : CanonicalTerm) (selected : Destination)
    (parsed : lvalue? environment term = some selected) : LvalueReading environment term selected := by
  unfold lvalue? at parsed
  split at parsed
  · exact .identifier _ _ (namedDestination_sound _ _ _ parsed)
  · contradiction

theorem lvalue_complete (environment : ScopedLvalues.Environment) (term : CanonicalTerm) (selected : Destination)
    (reading : LvalueReading environment term selected) : lvalue? environment term = some selected := by
  cases reading with
  | identifier name selected bound => exact namedDestination_complete environment name selected bound

def readTerm (model : Model) (environment : ScopedLvalues.Environment) :
    CanonicalTerm → Option (Expression model)
  | .node "Var" [.text name] => (namedDestination? environment name).map Expression.load
  | .node "IntConst" [.text spelling] => (literal? model spelling).map Expression.value
  | .node "Cast" [typeTerm, operand] => do
      some (.cast (← typeName? typeTerm) (← readTerm model environment operand))
  | .node "Assign" [left, operand] => do
      some (.assignment (← lvalue? environment left) (← readTerm model environment operand))
  | .node "Comma" [first, second] => do
      some (.comma (← readTerm model environment first) (← readTerm model environment second))
  | .node name [operand] => do
      let flags ← updateFlags? name
      let selected ← lvalue? environment operand
      some (.update selected flags.1 flags.2)
  | .node name [first, second] => do
      let operator ← binaryOperator? name
      some (.arithmetic operator (← readTerm model environment first) (← readTerm model environment second))
  | _ => none
termination_by term => sizeOf term

inductive TermReading (model : Model) (environment : ScopedLvalues.Environment) :
    CanonicalTerm → Expression model → Prop where
  | identifier (name : String) (selected : Destination) (bound : NamedDestination environment name selected) :
      TermReading model environment (.node "Var" [.text name]) (.load selected)
  | literal (spelling : String) (scalar : IntegerScalar.Value model.parameters) (reading : Literal model spelling scalar) :
      TermReading model environment (.node "IntConst" [.text spelling]) (.value scalar)
  | arithmetic (name : String) (operator : IntegerBinaryOperator) (first second : CanonicalTerm)
      (left right : Expression model) (head : BinaryHead name operator)
      (firstReading : TermReading model environment first left)
      (secondReading : TermReading model environment second right) :
      TermReading model environment (.node name [first, second]) (.arithmetic operator left right)
  | cast (typeTerm operand : CanonicalTerm) (type : IntegerType IntegerExtension) (expression : Expression model)
      (typed : TypeNameReading typeTerm type) (child : TermReading model environment operand expression) :
      TermReading model environment (.node "Cast" [typeTerm, operand]) (.cast type expression)
  | assignment (left operand : CanonicalTerm) (selected : Destination) (expression : Expression model)
      (lvalue : LvalueReading environment left selected) (child : TermReading model environment operand expression) :
      TermReading model environment (.node "Assign" [left, operand]) (.assignment selected expression)
  | update (name : String) (operand : CanonicalTerm) (selected : Destination) (increment isPrefix : Bool)
      (head : UpdateHead name increment isPrefix) (lvalue : LvalueReading environment operand selected) :
      TermReading model environment (.node name [operand]) (.update selected increment isPrefix)
  | comma (first second : CanonicalTerm) (left right : Expression model)
      (firstReading : TermReading model environment first left)
      (secondReading : TermReading model environment second right) :
      TermReading model environment (.node "Comma" [first, second]) (.comma left right)

theorem readTerm_complete (model : Model) (environment : ScopedLvalues.Environment)
    (term : CanonicalTerm) (expression : Expression model) (reading : TermReading model environment term expression) :
    readTerm model environment term = some expression := by
  induction reading with
  | identifier name selected bound =>
      simp only [readTerm, namedDestination_complete _ _ _ bound, Option.map_some]
  | literal spelling scalar reading =>
      simp only [readTerm, literal_complete _ _ _ reading, Option.map_some]
  | arithmetic name operator first second left right head _ _ firstIH secondIH =>
      cases head with
      | arithmetic operator =>
          cases operator <;> simp [binaryHead, readTerm, binaryOperator?, firstIH, secondIH]
  | cast typeTerm operand type expression typed _ ih =>
      simp only [readTerm, typeName_complete _ _ typed, ih, bind, Option.bind_some]
  | assignment left operand selected expression lvalue _ ih =>
      simp only [readTerm, lvalue_complete _ _ _ lvalue, ih, bind, Option.bind_some]
  | update name operand selected increment isPrefix head lvalue =>
      cases head <;> simp [readTerm, updateFlags?, lvalue_complete _ _ _ lvalue]
  | comma first second left right _ _ firstIH secondIH =>
      simp only [readTerm, firstIH, secondIH, bind, Option.bind_some]

theorem readTerm_sound (model : Model) (environment : ScopedLvalues.Environment)
    (term : CanonicalTerm) (expression : Expression model)
    (parsed : readTerm model environment term = some expression) : TermReading model environment term expression := by
  induction term using readTerm.induct generalizing expression with
  | case1 name =>
      rw [readTerm] at parsed
      obtain ⟨selected, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
      exact .identifier name selected (namedDestination_sound _ _ _ found)
  | case2 spelling =>
      rw [readTerm] at parsed
      obtain ⟨scalar, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
      exact .literal spelling scalar (literal_sound _ _ _ found)
  | case3 typeTerm operand ih =>
      simp only [readTerm, bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨type, typed, child, childParsed, rfl⟩ := parsed
      exact .cast _ _ _ _ (typeName_sound _ _ typed) (ih _ childParsed)
  | case4 left operand ih =>
      simp only [readTerm, bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨selected, found, child, childParsed, rfl⟩ := parsed
      exact .assignment _ _ _ _ (lvalue_sound _ _ _ found) (ih _ childParsed)
  | case5 first second firstIH secondIH =>
      simp only [readTerm, bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨left, leftParsed, right, rightParsed, rfl⟩ := parsed
      exact .comma _ _ _ _ (firstIH _ leftParsed) (secondIH _ rightParsed)
  | case6 name operand notVariable notLiteral =>
      rw [readTerm] at parsed <;> try assumption
      simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨⟨increment, isPrefix⟩, flags, selected, found, rfl⟩ := parsed
      exact .update _ _ _ _ _ (updateFlags_sound _ _ _ flags) (lvalue_sound _ _ _ found)
  | case7 name first second notCast notAssignment notComma firstIH secondIH =>
      rw [readTerm] at parsed <;> try assumption
      simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨operator, operatorParsed, left, leftParsed, right, rightParsed, rfl⟩ := parsed
      exact .arithmetic _ _ _ _ _ _ (binaryOperator_sound _ _ operatorParsed)
        (firstIH _ leftParsed) (secondIH _ rightParsed)
  | case8 term notVariable notLiteral notCast notAssignment notComma notUnary notBinary =>
      rw [readTerm] at parsed <;> try assumption
      contradiction

theorem readTerm_iff (model : Model) (environment : ScopedLvalues.Environment)
    (term : CanonicalTerm) (expression : Expression model) :
    readTerm model environment term = some expression ↔ TermReading model environment term expression :=
  ⟨readTerm_sound model environment term expression, readTerm_complete model environment term expression⟩

theorem TermReading.functional {model : Model} {environment : ScopedLvalues.Environment}
    {term : CanonicalTerm} {first second : Expression model}
    (left : TermReading model environment term first) (right : TermReading model environment term second) :
    first = second := Option.some.inj
  ((readTerm_complete model environment term first left).symm.trans
    (readTerm_complete model environment term second right))

abbrev Wire := CestaObjectAccess.Wire

def read (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) : Option (Expression model) := do
  let term ← decode? schema codecProfile sort wire
  readTerm model environment term

def Reading (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (expression : Expression model) : Prop :=
  ∃ term, Sorted schema codecProfile sort term ∧ encode? schema codecProfile sort term = some wire ∧
    TermReading model environment term expression

theorem read_sound (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (expression : Expression model)
    (parsed : read schema codecProfile sort model environment wire = some expression) :
    Reading schema codecProfile sort model environment wire expression := by
  obtain ⟨term, decoded, elaborated⟩ := Option.bind_eq_some_iff.mp parsed
  exact ⟨term, decode_sorted _ _ _ _ _ decoded, encode_decoded _ _ _ _ _ decoded,
    readTerm_sound _ _ _ _ elaborated⟩

theorem read_complete (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (expression : Expression model)
    (reading : Reading schema codecProfile sort model environment wire expression) :
    read schema codecProfile sort model environment wire = some expression := by
  obtain ⟨term, _, encoded, elaborated⟩ := reading
  simp only [read, decode_encoded _ _ _ _ _ encoded,
    readTerm_complete _ _ _ _ elaborated, bind, Option.bind_some]

theorem read_iff (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (expression : Expression model) :
    read schema codecProfile sort model environment wire = some expression ↔
      Reading schema codecProfile sort model environment wire expression :=
  ⟨read_sound schema codecProfile sort model environment wire expression,
    read_complete schema codecProfile sort model environment wire expression⟩

theorem represent_sorted_expression (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (term : CanonicalTerm) (expression : Expression model)
    (sorted : Sorted schema codecProfile sort term) (elaborated : TermReading model environment term expression) :
    ∃ wire, encode? schema codecProfile sort term = some wire ∧
      read schema codecProfile sort model environment wire = some expression := by
  obtain ⟨wire, encoded⟩ := encode_sorted sorted
  exact ⟨wire, encoded, read_complete _ _ _ _ _ _ _ ⟨term, sorted, encoded, elaborated⟩⟩

/-- The admitted syntax is represented by the existing checked expression
packet. Its operation graph is subsequently reconstructed from that syntax. -/
def lower (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) : Option LocatedExpressionData.ExpressionData :=
  (read schema codecProfile sort model environment wire).map LocatedExpressionData.encodeExpression

theorem lower_iff (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (data : LocatedExpressionData.ExpressionData) :
    lower schema codecProfile sort model environment wire = some data ↔
      ∃ expression, Reading schema codecProfile sort model environment wire expression ∧
        LocatedExpressionData.encodeExpression expression = data := by
  simp only [lower, Option.map_eq_some_iff, read_iff]

theorem lowered_expression_readback (schema : Schema) (codecProfile : Notation) (sort : String) (model : Model)
    (environment : ScopedLvalues.Environment) (wire : Wire) (data : LocatedExpressionData.ExpressionData)
    (lowered : lower schema codecProfile sort model environment wire = some data) :
    ∃ expression, Reading schema codecProfile sort model environment wire expression ∧
      LocatedExpressionData.decodeExpression model data = some expression := by
  obtain ⟨expression, reading, rfl⟩ := (lower_iff _ _ _ _ _ _ _).mp lowered
  exact ⟨expression, reading, LocatedExpressionData.decodeExpression_encode _ _⟩

end Mettapedia.Languages.C11.CestaLocatedExpressions
