import Mettapedia.Languages.C11.CestaIntegerDeclarations
import Mettapedia.Languages.C11.CestaLocatedExpressions
import Mettapedia.Languages.C11.FixedCoreStatements

/-!
# Cesta translation units into the fixed C core

Cesta's canonical C11 trees are read into fixed-core programs. The reader is a
static checker for the core fragment: every name is resolved through the
lexical scopes of the C source, every operand is classified as an integer or as
a pointer to a declared integer type, and every call is checked against the
signature of the function or service it names. Each reading function is proved
equivalent to an independent inductive reading relation.

The C rules the translation implements:

* A block's declarations and statements may interleave. A declaration in the
  middle of a block becomes a nested core block that extends to the end of the
  C block. Without `goto`, no statement can reach an object before its
  declaration, so lifetimes and name resolution coincide; a second declaration
  of a name in the same C scope is refused, and a function's parameters share
  the scope of its outermost block.
* A declared object is in scope in its own initializer. Initializers, integer
  assignments and arguments bound to parameters convert as if by assignment;
  returned values and arguments to services are converted explicitly to the
  declared type.
* `E1[E2]` is `*(E1 + E2)`; `&*E` is `E` and `&E1[E2]` is `E1 + E2`, without
  dereferencing. An array name designates its first element. The integer
  constant `0` is the null pointer constant where a pointer is expected.
  Unary minus is subtraction from zero, which overflows exactly when negation
  does.
* `p = malloc(n * sizeof(T))` and `p = malloc(sizeof(T))` allocate `n`
  (respectively one) objects of the pointee type `T` of `p`; `free(p)` releases.
  These two names denote the standard library functions unless a local name
  hides them, and a program may not define them. Other functions that the
  program does not define are services of the host interface, which the reader
  takes as a parameter instead of elaborating header text.
* A `return` without a value is only accepted in a function returning `void`,
  and a `return` with a value only in one that does not. `break` and
  `continue` are only accepted inside a loop. Reaching the end of `main`
  returns `0` when `main` returns `int`.

Refused, rather than approximated: `for`, `do`/`while`, `switch`, `goto` and
labels; logical, bitwise, shift, increment and compound-assignment operators;
pointer subtraction and comparison; casts to pointer types; calls inside
expressions; array initializers; storage classes, qualifiers, typedefs and
structures; file-scope objects and prototypes. The byte count of an
allocation is read as an element count, so a count whose byte size wraps
around in `size_t` is outside the fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.CestaFixedCore

open Mettapedia.GSLT.Parsing.CanonicalGrammar (CanonicalTerm)
open IntegerMemoryModel FixedCore
open CestaExpressionElaboration (literal? Literal literal_sound literal_complete typeName? TypeNameReading
  typeName_sound typeName_complete)
open CestaIntegerDeclarations (specifiers? SpecifiersReading specifiers_sound specifiers_complete declarator?
  DeclaratorReading declarator_iff)
open CestaLocatedExpressions (binaryOperator? BinaryHead binaryOperator_sound binaryOperator_complete)

/-! ## Static types of names -/

/-- The declared type of a name in block scope. -/
inductive Kind where
  | integer (type : IntegerType IntegerExtension)
  | array (type : IntegerType IntegerExtension) (count : Nat)
  | pointer (type : IntegerType IntegerExtension)
  deriving DecidableEq, Repr

/-- The declared type of a parameter, an argument position or a result. -/
inductive Slot where
  | integer (type : IntegerType IntegerExtension)
  | pointer (type : IntegerType IntegerExtension)
  deriving DecidableEq, Repr

def Slot.kind : Slot → Kind
  | .integer type => .integer type
  | .pointer type => .pointer type

structure Signature where
  parameters : List Slot
  result : Option Slot
  deriving DecidableEq, Repr

/-- The C block scopes, innermost first. -/
abbrev Scopes := List (List (String × Kind))

def lookup : Scopes → String → Option Kind
  | [], _ => none
  | scope :: rest, name =>
      match scope.lookup name with
      | some kind => some kind
      | none => lookup rest name

/-- Declare a name in the innermost scope; a second declaration there is refused. -/
def declare (scopes : Scopes) (name : String) (kind : Kind) : Option Scopes :=
  match scopes with
  | [] => none
  | scope :: rest => if (scope.lookup name).isSome then none else some (((name, kind) :: scope) :: rest)

/-! ## Operands -/

/-- A pure core expression with its static class. -/
inductive Operand (model : Model) where
  | integer (expression : Expression model)
  | pointer (type : IntegerType IntegerExtension) (expression : Expression model)

variable {model : Model}

def Operand.integer? : Operand model → Option (Expression model)
  | .integer expression => some expression
  | .pointer _ _ => none

def Operand.pointer? : Operand model → Option (IntegerType IntegerExtension × Expression model)
  | .integer _ => none
  | .pointer type expression => some (type, expression)

theorem Operand.integer?_eq_some {operand : Operand model} {expression : Expression model} :
    operand.integer? = some expression ↔ operand = .integer expression := by
  cases operand <;> simp [Operand.integer?]

theorem Operand.pointer?_eq_some {operand : Operand model} {type : IntegerType IntegerExtension}
    {expression : Expression model} :
    operand.pointer? = some (type, expression) ↔ operand = .pointer type expression := by
  cases operand <;> simp [Operand.pointer?]

/-- What a declared name denotes as an operand. -/
def variableOperand (name : String) : Kind → Operand model
  | .integer _ => .integer (.read (.named name))
  | .array type _ => .pointer type (.addressOf (.named name))
  | .pointer type => .pointer type (.variable name)

def comparison? : String → Option IntegerOperators.Comparison
  | "Less" => some .less
  | "Greater" => some .greater
  | "LessEqual" => some .lessEqual
  | "GreaterEqual" => some .greaterEqual
  | "Equal" => some .equal
  | "NotEqual" => some .notEqual
  | _ => none

inductive ComparisonHead : String → IntegerOperators.Comparison → Prop where
  | less : ComparisonHead "Less" .less
  | greater : ComparisonHead "Greater" .greater
  | lessEqual : ComparisonHead "LessEqual" .lessEqual
  | greaterEqual : ComparisonHead "GreaterEqual" .greaterEqual
  | equal : ComparisonHead "Equal" .equal
  | notEqual : ComparisonHead "NotEqual" .notEqual

theorem comparison_iff (name : String) (operator : IntegerOperators.Comparison) :
    comparison? name = some operator ↔ ComparisonHead name operator := by
  constructor
  · intro parsed
    unfold comparison? at parsed
    split at parsed <;> first | contradiction | (cases parsed; constructor)
  · intro head
    cases head <;> rfl

theorem binaryOperator_none_of_comparison {name : String} {operator : IntegerOperators.Comparison}
    (head : ComparisonHead name operator) : binaryOperator? name = none := by
  cases head <;> rfl

/-- A binary operator applied to two classified operands. -/
def combine (name : String) : Operand model → Operand model → Option (Operand model)
  | .integer left, .integer right =>
      match binaryOperator? name with
      | some operator => some (.integer (.binary operator left right))
      | none => (comparison? name).map fun operator => .integer (.compare operator left right)
  | .pointer type pointer, .integer amount =>
      if name = "Add" then some (.pointer type (.offset pointer amount)) else none
  | .integer amount, .pointer type pointer =>
      if name = "Add" then some (.pointer type (.offset pointer amount)) else none
  | .pointer _ _, .pointer _ _ => none

inductive Combines : String → Operand model → Operand model → Operand model → Prop where
  | arithmetic (name : String) (operator : IntegerBinaryOperator) (left right : Expression model)
      (head : BinaryHead name operator) :
      Combines name (.integer left) (.integer right) (.integer (.binary operator left right))
  | comparison (name : String) (operator : IntegerOperators.Comparison) (left right : Expression model)
      (head : ComparisonHead name operator) :
      Combines name (.integer left) (.integer right) (.integer (.compare operator left right))
  | offset (type : IntegerType IntegerExtension) (pointer amount : Expression model) :
      Combines "Add" (.pointer type pointer) (.integer amount) (.pointer type (.offset pointer amount))
  | offsetCommuted (type : IntegerType IntegerExtension) (amount pointer : Expression model) :
      Combines "Add" (.integer amount) (.pointer type pointer) (.pointer type (.offset pointer amount))

theorem combine_iff (name : String) (left right result : Operand model) :
    combine name left right = some result ↔ Combines name left right result := by
  constructor
  · intro combined
    cases left <;> cases right <;> simp only [combine] at combined
    · split at combined
      · rename_i operator head
        cases combined
        exact .arithmetic _ _ _ _ (binaryOperator_sound _ _ head)
      · obtain ⟨operator, head, rfl⟩ := Option.map_eq_some_iff.mp combined
        exact .comparison _ _ _ _ ((comparison_iff _ _).mp head)
    · split at combined
      · rename_i isAdd
        subst isAdd
        cases combined
        exact .offsetCommuted _ _ _
      · contradiction
    · split at combined
      · rename_i isAdd
        subst isAdd
        cases combined
        exact .offset _ _ _
      · contradiction
    · contradiction
  · intro combines
    cases combines with
    | arithmetic name operator left right head =>
        simp only [combine, binaryOperator_complete _ _ head]
    | comparison name operator left right head =>
        simp only [combine, binaryOperator_none_of_comparison head, (comparison_iff _ _).mpr head, Option.map_some]
    | offset | offsetCommuted => simp only [combine, if_true]

theorem not_combines_pointers (name : String) (type other : IntegerType IntegerExtension)
    (left right : Expression model) (result : Operand model) :
    ¬ Combines name (.pointer type left) (.pointer other right) result := by
  intro combines
  cases combines

/-! ## Reading operands -/

section Operands

variable (model : Model) (scopes : Scopes)

def readOperand : CanonicalTerm → Option (Operand model)
  | .node "Var" [.text name] => (lookup scopes name).map (variableOperand name)
  | .node "IntConst" [.text spelling] => (literal? model spelling).map fun scalar => .integer (.constant scalar)
  | .node "Cast" [typeTerm, operand] => do
      let type ← typeName? typeTerm
      let expression ← (← readOperand operand).integer?
      some (.integer (.cast type expression))
  | .node "Negate" [operand] => do
      let zero ← literal? model "0"
      let expression ← (← readOperand operand).integer?
      some (.integer (.binary .subtract (.constant zero) expression))
  | .node "Subscript" [base, index] => do
      let target ← (← readOperand base).pointer?
      let amount ← (← readOperand index).integer?
      some (.integer (.read (.deref (.offset target.2 amount))))
  | .node "Indirection" [operand] => do
      let target ← (← readOperand operand).pointer?
      some (.integer (.read (.deref target.2)))
  | .node "AddressOf" [.node "Var" [.text name]] =>
      match lookup scopes name with
      | some (.integer type) => some (.pointer type (.addressOf (.named name)))
      | _ => none
  | .node "AddressOf" [.node "Subscript" [base, index]] => do
      let target ← (← readOperand base).pointer?
      let amount ← (← readOperand index).integer?
      some (.pointer target.1 (.offset target.2 amount))
  | .node "AddressOf" [.node "Indirection" [operand]] => do
      let target ← (← readOperand operand).pointer?
      some (.pointer target.1 target.2)
  | .node name [first, second] => do
      combine name (← readOperand first) (← readOperand second)
  | _ => none
termination_by term => sizeOf term

inductive OperandReading : CanonicalTerm → Operand model → Prop where
  | identifier (name : String) (kind : Kind) (bound : lookup scopes name = some kind) :
      OperandReading (.node "Var" [.text name]) (variableOperand name kind)
  | literal (spelling : String) (scalar : IntegerScalar.Value model.parameters)
      (reading : Literal model spelling scalar) :
      OperandReading (.node "IntConst" [.text spelling]) (.integer (.constant scalar))
  | cast (typeTerm operand : CanonicalTerm) (type : IntegerType IntegerExtension) (expression : Expression model)
      (typed : TypeNameReading typeTerm type) (child : OperandReading operand (.integer expression)) :
      OperandReading (.node "Cast" [typeTerm, operand]) (.integer (.cast type expression))
  | negate (operand : CanonicalTerm) (zero : IntegerScalar.Value model.parameters) (expression : Expression model)
      (zeroReading : Literal model "0" zero) (child : OperandReading operand (.integer expression)) :
      OperandReading (.node "Negate" [operand]) (.integer (.binary .subtract (.constant zero) expression))
  | subscript (base index : CanonicalTerm) (type : IntegerType IntegerExtension) (pointer amount : Expression model)
      (baseReading : OperandReading base (.pointer type pointer))
      (indexReading : OperandReading index (.integer amount)) :
      OperandReading (.node "Subscript" [base, index]) (.integer (.read (.deref (.offset pointer amount))))
  | indirection (operand : CanonicalTerm) (type : IntegerType IntegerExtension) (pointer : Expression model)
      (child : OperandReading operand (.pointer type pointer)) :
      OperandReading (.node "Indirection" [operand]) (.integer (.read (.deref pointer)))
  | addressOfVariable (name : String) (type : IntegerType IntegerExtension)
      (bound : lookup scopes name = some (.integer type)) :
      OperandReading (.node "AddressOf" [.node "Var" [.text name]]) (.pointer type (.addressOf (.named name)))
  | addressOfElement (base index : CanonicalTerm) (type : IntegerType IntegerExtension)
      (pointer amount : Expression model)
      (baseReading : OperandReading base (.pointer type pointer))
      (indexReading : OperandReading index (.integer amount)) :
      OperandReading (.node "AddressOf" [.node "Subscript" [base, index]]) (.pointer type (.offset pointer amount))
  | addressOfIndirection (operand : CanonicalTerm) (type : IntegerType IntegerExtension) (pointer : Expression model)
      (child : OperandReading operand (.pointer type pointer)) :
      OperandReading (.node "AddressOf" [.node "Indirection" [operand]]) (.pointer type pointer)
  | binary (name : String) (first second : CanonicalTerm) (left right result : Operand model)
      (firstReading : OperandReading first left) (secondReading : OperandReading second right)
      (combines : Combines name left right result) :
      OperandReading (.node name [first, second]) result

end Operands

theorem readOperand_sound (model : Model) (scopes : Scopes) (term : CanonicalTerm) (operand : Operand model)
    (parsed : readOperand model scopes term = some operand) : OperandReading model scopes term operand := by
  unfold readOperand at parsed
  split at parsed
  · obtain ⟨kind, bound, rfl⟩ := Option.map_eq_some_iff.mp parsed
    exact .identifier _ _ bound
  · obtain ⟨scalar, literal, rfl⟩ := Option.map_eq_some_iff.mp parsed
    exact .literal _ _ (literal_sound _ _ _ literal)
  · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨type, typed, child, childParsed, expression, integer, rfl⟩ := parsed
    rw [Operand.integer?_eq_some] at integer
    subst integer
    exact .cast _ _ _ _ (typeName_sound _ _ typed) (readOperand_sound _ _ _ _ childParsed)
  · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨zero, zeroParsed, child, childParsed, expression, integer, rfl⟩ := parsed
    rw [Operand.integer?_eq_some] at integer
    subst integer
    exact .negate _ _ _ (literal_sound _ _ _ zeroParsed) (readOperand_sound _ _ _ _ childParsed)
  · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨baseOperand, baseParsed, ⟨type, pointer⟩, isPointer, indexOperand, indexParsed, amount, integer, rfl⟩ :=
      parsed
    rw [Operand.pointer?_eq_some] at isPointer
    rw [Operand.integer?_eq_some] at integer
    subst isPointer integer
    exact .subscript _ _ _ _ _ (readOperand_sound _ _ _ _ baseParsed) (readOperand_sound _ _ _ _ indexParsed)
  · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨child, childParsed, ⟨type, pointer⟩, isPointer, rfl⟩ := parsed
    rw [Operand.pointer?_eq_some] at isPointer
    subst isPointer
    exact .indirection _ _ _ (readOperand_sound _ _ _ _ childParsed)
  · rename_i name
    split at parsed
    · rename_i type bound
      cases parsed
      exact .addressOfVariable _ _ bound
    · contradiction
  · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨baseOperand, baseParsed, ⟨type, pointer⟩, isPointer, indexOperand, indexParsed, amount, integer, rfl⟩ :=
      parsed
    rw [Operand.pointer?_eq_some] at isPointer
    rw [Operand.integer?_eq_some] at integer
    subst isPointer integer
    exact .addressOfElement _ _ _ _ _ (readOperand_sound _ _ _ _ baseParsed)
      (readOperand_sound _ _ _ _ indexParsed)
  · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨child, childParsed, ⟨type, pointer⟩, isPointer, rfl⟩ := parsed
    rw [Operand.pointer?_eq_some] at isPointer
    subst isPointer
    exact .addressOfIndirection _ _ _ (readOperand_sound _ _ _ _ childParsed)
  · simp only [bind, Option.bind_eq_some_iff] at parsed
    obtain ⟨left, leftParsed, right, rightParsed, combined⟩ := parsed
    exact .binary _ _ _ _ _ _ (readOperand_sound _ _ _ _ leftParsed) (readOperand_sound _ _ _ _ rightParsed)
      ((combine_iff _ _ _ _).mp combined)
  · contradiction
termination_by sizeOf term

theorem readOperand_complete (model : Model) (scopes : Scopes) (term : CanonicalTerm) (operand : Operand model)
    (reading : OperandReading model scopes term operand) : readOperand model scopes term = some operand := by
  induction reading with
  | identifier name kind bound => simp only [readOperand, bound, Option.map_some]
  | literal spelling scalar reading => simp only [readOperand, literal_complete _ _ _ reading, Option.map_some]
  | cast typeTerm operand type expression typed _ ih =>
      simp only [readOperand, typeName_complete _ _ typed, ih, Operand.integer?, bind, Option.bind_some]
  | negate operand zero expression zeroReading _ ih =>
      simp only [readOperand, literal_complete _ _ _ zeroReading, ih, Operand.integer?, bind, Option.bind_some]
  | subscript base index type pointer amount _ _ baseIH indexIH =>
      simp only [readOperand, baseIH, indexIH, Operand.integer?, Operand.pointer?, bind, Option.bind_some]
  | indirection operand type pointer _ ih =>
      simp only [readOperand, ih, Operand.pointer?, bind, Option.bind_some]
  | addressOfVariable name type bound => simp only [readOperand, bound]
  | addressOfElement base index type pointer amount _ _ baseIH indexIH =>
      simp only [readOperand, baseIH, indexIH, Operand.integer?, Operand.pointer?, bind, Option.bind_some]
  | addressOfIndirection operand type pointer _ ih =>
      simp only [readOperand, ih, Operand.pointer?, bind, Option.bind_some]
  | binary name first second left right result _ _ combines firstIH secondIH =>
      cases combines with
      | arithmetic name operator left right head =>
          cases head with
          | arithmetic operator =>
              cases operator <;>
                simp [readOperand, CestaLocatedExpressions.binaryHead, firstIH, secondIH, combine, binaryOperator?]
      | comparison name operator left right head =>
          cases head <;> simp [readOperand, firstIH, secondIH, combine, binaryOperator?, comparison?]
      | offset | offsetCommuted => simp [readOperand, firstIH, secondIH, combine]

theorem readOperand_iff (model : Model) (scopes : Scopes) (term : CanonicalTerm) (operand : Operand model) :
    readOperand model scopes term = some operand ↔ OperandReading model scopes term operand :=
  ⟨readOperand_sound model scopes term operand, readOperand_complete model scopes term operand⟩

theorem not_operandReading_call (model : Model) (scopes : Scopes) (children : List CanonicalTerm)
    (operand : Operand model) : ¬ OperandReading model scopes (.node "Call" children) operand := by
  intro reading
  generalize equation : CanonicalTerm.node "Call" children = term at reading
  cases reading with
  | binary name first second left right result _ _ combines =>
      simp only [CanonicalTerm.node.injEq] at equation
      obtain ⟨rfl, -⟩ := equation
      have combined := (combine_iff _ _ _ _).mpr combines
      cases left <;> cases right <;> simp [combine, binaryOperator?, comparison?] at combined
  | _ => simp at equation

theorem not_operandReading_zero_pointer (model : Model) (scopes : Scopes) (type : IntegerType IntegerExtension)
    (pointer : Expression model) :
    ¬ OperandReading model scopes (.node "IntConst" [.text "0"]) (.pointer type pointer) := by
  intro reading
  have computed := readOperand_complete _ _ _ _ reading
  simp [readOperand] at computed

/-! ## Pointer, value and released positions -/

section Positions

variable (model : Model) (scopes : Scopes)

/-- An operand where a pointer to `type` is expected. -/
def readPointer (type : IntegerType IntegerExtension) (term : CanonicalTerm) : Option (Expression model) :=
  match term with
  | .node "IntConst" [.text "0"] => some .null
  | _ => do
      let target ← (← readOperand model scopes term).pointer?
      if target.1 = type then some target.2 else none

inductive PointerReading (type : IntegerType IntegerExtension) : CanonicalTerm → Expression model → Prop where
  | null : PointerReading type (.node "IntConst" [.text "0"]) .null
  | pointer (term : CanonicalTerm) (pointer : Expression model)
      (reading : OperandReading model scopes term (.pointer type pointer)) : PointerReading type term pointer

/-- The argument of `free`: a pointer of any pointee type, or the null pointer constant. -/
def readReleased (term : CanonicalTerm) : Option (Expression model) :=
  match term with
  | .node "IntConst" [.text "0"] => some .null
  | _ => do
      let target ← (← readOperand model scopes term).pointer?
      some target.2

inductive ReleasedReading : CanonicalTerm → Expression model → Prop where
  | null : ReleasedReading (.node "IntConst" [.text "0"]) .null
  | pointer (term : CanonicalTerm) (type : IntegerType IntegerExtension) (pointer : Expression model)
      (reading : OperandReading model scopes term (.pointer type pointer)) : ReleasedReading term pointer

/-- A value converted to a declared slot: integers by an explicit conversion,
pointers by type agreement. -/
def readSlot : Slot → CanonicalTerm → Option (Expression model)
  | .integer type, term => do
      let expression ← (← readOperand model scopes term).integer?
      some (.cast type expression)
  | .pointer type, term => readPointer model scopes type term

inductive SlotReading : Slot → CanonicalTerm → Expression model → Prop where
  | integer (type : IntegerType IntegerExtension) (term : CanonicalTerm) (expression : Expression model)
      (reading : OperandReading model scopes term (.integer expression)) :
      SlotReading (.integer type) term (.cast type expression)
  | pointer (type : IntegerType IntegerExtension) (term : CanonicalTerm) (pointer : Expression model)
      (reading : PointerReading model scopes type term pointer) : SlotReading (.pointer type) term pointer

/-- An integer object designated by an assignment target. -/
def readPlace : CanonicalTerm → Option (Place model)
  | .node "Var" [.text name] =>
      match lookup scopes name with
      | some (.integer _) => some (.named name)
      | _ => none
  | .node "Subscript" [base, index] => do
      let target ← (← readOperand model scopes base).pointer?
      let amount ← (← readOperand model scopes index).integer?
      some (.deref (.offset target.2 amount))
  | .node "Indirection" [operand] => do
      let target ← (← readOperand model scopes operand).pointer?
      some (.deref target.2)
  | _ => none

inductive PlaceReading : CanonicalTerm → Place model → Prop where
  | named (name : String) (type : IntegerType IntegerExtension) (bound : lookup scopes name = some (.integer type)) :
      PlaceReading (.node "Var" [.text name]) (.named name)
  | element (base index : CanonicalTerm) (type : IntegerType IntegerExtension) (pointer amount : Expression model)
      (baseReading : OperandReading model scopes base (.pointer type pointer))
      (indexReading : OperandReading model scopes index (.integer amount)) :
      PlaceReading (.node "Subscript" [base, index]) (.deref (.offset pointer amount))
  | indirection (operand : CanonicalTerm) (type : IntegerType IntegerExtension) (pointer : Expression model)
      (reading : OperandReading model scopes operand (.pointer type pointer)) :
      PlaceReading (.node "Indirection" [operand]) (.deref pointer)

/-- The element count of an allocation of objects of type `type`. -/
def readCount (type : IntegerType IntegerExtension) : CanonicalTerm → Option (Expression model)
  | .node "SizeofType" [typeTerm] => do
      if (← typeName? typeTerm) = type then (literal? model "1").map .constant else none
  | .node "Multiply" [count, .node "SizeofType" [typeTerm]] => do
      if (← typeName? typeTerm) = type then (← readOperand model scopes count).integer? else none
  | _ => none

inductive CountReading (type : IntegerType IntegerExtension) : CanonicalTerm → Expression model → Prop where
  | single (typeTerm : CanonicalTerm) (one : IntegerScalar.Value model.parameters)
      (typed : TypeNameReading typeTerm type) (oneReading : Literal model "1" one) :
      CountReading type (.node "SizeofType" [typeTerm]) (.constant one)
  | multiple (count typeTerm : CanonicalTerm) (amount : Expression model) (typed : TypeNameReading typeTerm type)
      (countReading : OperandReading model scopes count (.integer amount)) :
      CountReading type (.node "Multiply" [count, .node "SizeofType" [typeTerm]]) amount

def readArguments : List Slot → List CanonicalTerm → Option (List (Expression model))
  | [], [] => some []
  | slot :: slots, term :: terms => do
      some ((← readSlot model scopes slot term) :: (← readArguments slots terms))
  | _, _ => none

inductive ArgumentsReading : List Slot → List CanonicalTerm → List (Expression model) → Prop where
  | nil : ArgumentsReading [] [] []
  | cons (slot : Slot) (slots : List Slot) (term : CanonicalTerm) (terms : List CanonicalTerm)
      (expression : Expression model) (expressions : List (Expression model))
      (head : SlotReading model scopes slot term expression) (tail : ArgumentsReading slots terms expressions) :
      ArgumentsReading (slot :: slots) (term :: terms) (expression :: expressions)

end Positions

theorem readPointer_iff (model : Model) (scopes : Scopes) (type : IntegerType IntegerExtension)
    (term : CanonicalTerm) (pointer : Expression model) :
    readPointer model scopes type term = some pointer ↔ PointerReading model scopes type term pointer := by
  constructor
  · intro parsed
    unfold readPointer at parsed
    split at parsed
    · cases parsed; exact .null
    · simp only [bind, Option.bind_eq_some_iff] at parsed
      obtain ⟨operand, operandParsed, ⟨actual, expression⟩, isPointer, agrees⟩ := parsed
      rw [Operand.pointer?_eq_some] at isPointer
      subst isPointer
      split at agrees
      · rename_i same
        cases same
        cases agrees
        exact .pointer _ _ (readOperand_sound _ _ _ _ operandParsed)
      · contradiction
  · intro reading
    cases reading with
    | null => rfl
    | pointer term pointer reading =>
        unfold readPointer
        split
        · exact absurd reading (not_operandReading_zero_pointer _ _ _ _)
        · simp only [readOperand_complete _ _ _ _ reading, Operand.pointer?, bind, Option.bind_some, if_true]

theorem readReleased_iff (model : Model) (scopes : Scopes) (term : CanonicalTerm) (pointer : Expression model) :
    readReleased model scopes term = some pointer ↔ ReleasedReading model scopes term pointer := by
  constructor
  · intro parsed
    unfold readReleased at parsed
    split at parsed
    · cases parsed; exact .null
    · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨operand, operandParsed, ⟨actual, expression⟩, isPointer, rfl⟩ := parsed
      rw [Operand.pointer?_eq_some] at isPointer
      subst isPointer
      exact .pointer _ _ _ (readOperand_sound _ _ _ _ operandParsed)
  · intro reading
    cases reading with
    | null => rfl
    | pointer term type pointer reading =>
        unfold readReleased
        split
        · exact absurd reading (not_operandReading_zero_pointer _ _ _ _)
        · simp only [readOperand_complete _ _ _ _ reading, Operand.pointer?, bind, Option.bind_some]

theorem readSlot_iff (model : Model) (scopes : Scopes) (slot : Slot) (term : CanonicalTerm)
    (expression : Expression model) :
    readSlot model scopes slot term = some expression ↔ SlotReading model scopes slot term expression := by
  cases slot with
  | integer type =>
      constructor
      · intro parsed
        simp only [readSlot, bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
        obtain ⟨operand, operandParsed, value, integer, rfl⟩ := parsed
        rw [Operand.integer?_eq_some] at integer
        subst integer
        exact .integer _ _ _ (readOperand_sound _ _ _ _ operandParsed)
      · intro reading
        cases reading with
        | integer type term expression reading =>
            simp only [readSlot, readOperand_complete _ _ _ _ reading, Operand.integer?, bind, Option.bind_some]
  | pointer type =>
      constructor
      · intro parsed
        exact .pointer _ _ _ ((readPointer_iff _ _ _ _ _).mp parsed)
      · intro reading
        cases reading with
        | pointer type term pointer reading => exact (readPointer_iff _ _ _ _ _).mpr reading

theorem readPlace_iff (model : Model) (scopes : Scopes) (term : CanonicalTerm) (place : Place model) :
    readPlace model scopes term = some place ↔ PlaceReading model scopes term place := by
  constructor
  · intro parsed
    unfold readPlace at parsed
    split at parsed
    · split at parsed
      · rename_i type bound
        cases parsed
        exact .named _ _ bound
      · contradiction
    · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨baseOperand, baseParsed, ⟨type, pointer⟩, isPointer, indexOperand, indexParsed, amount, integer, rfl⟩ :=
        parsed
      rw [Operand.pointer?_eq_some] at isPointer
      rw [Operand.integer?_eq_some] at integer
      subst isPointer integer
      exact .element _ _ _ _ _ (readOperand_sound _ _ _ _ baseParsed) (readOperand_sound _ _ _ _ indexParsed)
    · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨operand, operandParsed, ⟨type, pointer⟩, isPointer, rfl⟩ := parsed
      rw [Operand.pointer?_eq_some] at isPointer
      subst isPointer
      exact .indirection _ _ _ (readOperand_sound _ _ _ _ operandParsed)
    · contradiction
  · intro reading
    cases reading with
    | named name type bound => simp only [readPlace, bound]
    | element base index type pointer amount baseReading indexReading =>
        simp only [readPlace, readOperand_complete _ _ _ _ baseReading, readOperand_complete _ _ _ _ indexReading,
          Operand.pointer?, Operand.integer?, bind, Option.bind_some]
    | indirection operand type pointer reading =>
        simp only [readPlace, readOperand_complete _ _ _ _ reading, Operand.pointer?, bind, Option.bind_some]

theorem readCount_iff (model : Model) (scopes : Scopes) (type : IntegerType IntegerExtension)
    (term : CanonicalTerm) (count : Expression model) :
    readCount model scopes type term = some count ↔ CountReading model scopes type term count := by
  constructor
  · intro parsed
    unfold readCount at parsed
    split at parsed
    · simp only [bind, Option.bind_eq_some_iff] at parsed
      obtain ⟨actual, typed, selected⟩ := parsed
      split at selected
      · rename_i same
        subst same
        obtain ⟨one, oneParsed, rfl⟩ := Option.map_eq_some_iff.mp selected
        exact .single _ _ (typeName_sound _ _ typed) (literal_sound _ _ _ oneParsed)
      · contradiction
    · simp only [bind, Option.bind_eq_some_iff] at parsed
      obtain ⟨actual, typed, selected⟩ := parsed
      split at selected
      · rename_i same
        subst same
        obtain ⟨operand, operandParsed, integer⟩ := Option.bind_eq_some_iff.mp selected
        rw [Operand.integer?_eq_some] at integer
        subst integer
        exact .multiple _ _ _ (typeName_sound _ _ typed) (readOperand_sound _ _ _ _ operandParsed)
      · contradiction
    · contradiction
  · intro reading
    cases reading with
    | single typeTerm one typed oneReading =>
        simp only [readCount, typeName_complete _ _ typed, literal_complete _ _ _ oneReading, bind,
          Option.bind_some, if_true, Option.map_some]
    | multiple count typeTerm amount typed countReading =>
        simp only [readCount, typeName_complete _ _ typed, readOperand_complete _ _ _ _ countReading, bind,
          Option.bind_some, if_true, Operand.integer?]

theorem readArguments_iff (model : Model) (scopes : Scopes) (slots : List Slot) (terms : List CanonicalTerm)
    (expressions : List (Expression model)) :
    readArguments model scopes slots terms = some expressions ↔ ArgumentsReading model scopes slots terms expressions := by
  induction slots generalizing terms expressions with
  | nil =>
      cases terms with
      | nil =>
          constructor
          · intro parsed; cases parsed; exact .nil
          · intro reading; cases reading; rfl
      | cons term terms =>
          constructor
          · intro parsed; cases parsed
          · intro reading; cases reading
  | cons slot slots ih =>
      cases terms with
      | nil =>
          constructor
          · intro parsed; cases parsed
          · intro reading; cases reading
      | cons term terms =>
          constructor
          · intro parsed
            simp only [readArguments, bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
            obtain ⟨expression, head, rest, tail, rfl⟩ := parsed
            exact .cons _ _ _ _ _ _ ((readSlot_iff _ _ _ _ _).mp head) ((ih _ _).mp tail)
          · intro reading
            cases reading with
            | cons _ _ _ _ expression expressions head tail =>
                simp only [readArguments, (readSlot_iff _ _ _ _ _).mpr head, (ih _ _).mpr tail, bind,
                  Option.bind_some]

theorem not_pointerReading_call (model : Model) (scopes : Scopes) (type : IntegerType IntegerExtension)
    (children : List CanonicalTerm) (pointer : Expression model) :
    ¬ PointerReading model scopes type (.node "Call" children) pointer := by
  intro reading
  generalize equation : CanonicalTerm.node "Call" children = term at reading
  cases reading with
  | null => simp at equation
  | pointer _ _ reading =>
      subst equation
      exact not_operandReading_call _ _ _ _ reading

/-! ## Calls -/

/-- What the statements of one function body may refer to besides block-scope names. -/
structure Context where
  scopes : Scopes
  functions : List (String × Signature)
  services : List (String × Signature)
  result : Option Slot

def Context.enter (context : Context) : Context := { context with scopes := [] :: context.scopes }

/-- Whether a called function is defined by the program or offered by the host. -/
inductive Target where
  | program
  | service
  deriving DecidableEq, Repr

def callee? (context : Context) (name : String) : Option (Target × Signature) :=
  if lookup context.scopes name = none ∧ name ≠ "malloc" ∧ name ≠ "free" then
    match context.functions.lookup name with
    | some signature => some (.program, signature)
    | none => (context.services.lookup name).map fun signature => (.service, signature)
  else none

inductive Callee (context : Context) (name : String) : Target → Signature → Prop where
  | program (signature : Signature) (unbound : lookup context.scopes name = none) (notMalloc : name ≠ "malloc")
      (notFree : name ≠ "free") (defined : context.functions.lookup name = some signature) :
      Callee context name .program signature
  | service (signature : Signature) (unbound : lookup context.scopes name = none) (notMalloc : name ≠ "malloc")
      (notFree : name ≠ "free") (undefined : context.functions.lookup name = none)
      (offered : context.services.lookup name = some signature) :
      Callee context name .service signature

theorem callee_iff (context : Context) (name : String) (target : Target) (signature : Signature) :
    callee? context name = some (target, signature) ↔ Callee context name target signature := by
  constructor
  · intro found
    unfold callee? at found
    split at found
    · rename_i admitted
      obtain ⟨unbound, notMalloc, notFree⟩ := admitted
      split at found
      · rename_i defined
        cases found
        exact .program _ unbound notMalloc notFree defined
      · rename_i undefined
        obtain ⟨offered, provided, same⟩ := Option.map_eq_some_iff.mp found
        cases same
        exact .service _ unbound notMalloc notFree undefined provided
    · contradiction
  · intro callee
    cases callee with
    | program signature unbound notMalloc notFree defined =>
        simp only [callee?, unbound, ne_eq, notMalloc, not_false_eq_true, notFree, and_self, if_true, defined]
    | service signature unbound notMalloc notFree undefined offered =>
        simp only [callee?, unbound, ne_eq, notMalloc, not_false_eq_true, notFree, and_self, if_true, undefined,
          offered, Option.map_some]

theorem Callee.notMalloc {context : Context} {name : String} {target : Target} {signature : Signature}
    (callee : Callee context name target signature) : name ≠ "malloc" := by
  cases callee <;> assumption

theorem Callee.notFree {context : Context} {name : String} {target : Target} {signature : Signature}
    (callee : Callee context name target signature) : name ≠ "free" := by
  cases callee <;> assumption

/-- Whether a result of the called function's type may be delivered where it is used. -/
def accepts : Option Slot → Option Slot → Bool
  | none, _ => true
  | some (.integer _), some (.integer _) => true
  | some (.pointer expected), some (.pointer provided) => expected == provided
  | _, _ => false

inductive Accepts : Option Slot → Option Slot → Prop where
  | discarded (result : Option Slot) : Accepts none result
  | integer (target provided : IntegerType IntegerExtension) :
      Accepts (some (.integer target)) (some (.integer provided))
  | pointer (type : IntegerType IntegerExtension) : Accepts (some (.pointer type)) (some (.pointer type))

theorem accepts_iff (expected provided : Option Slot) : accepts expected provided = true ↔ Accepts expected provided := by
  constructor
  · intro accepted
    match expected, provided, accepted with
    | none, _, _ => exact .discarded _
    | some (.integer _), some (.integer _), _ => exact .integer _ _
    | some (.pointer expected), some (.pointer provided), same =>
        simp only [accepts, beq_iff_eq] at same
        subst same
        exact .pointer _
  · intro accepted
    cases accepted <;> simp [accepts]

def argumentTerms : CanonicalTerm → Option (List CanonicalTerm)
  | .node "NoArguments" [] => some []
  | .node "Arguments" [.seq terms] => some terms
  | _ => none

inductive ArgumentTerms : CanonicalTerm → List CanonicalTerm → Prop where
  | none : ArgumentTerms (.node "NoArguments" []) []
  | some (terms : List CanonicalTerm) : ArgumentTerms (.node "Arguments" [.seq terms]) terms

theorem argumentTerms_iff (term : CanonicalTerm) (terms : List CanonicalTerm) :
    argumentTerms term = some terms ↔ ArgumentTerms term terms := by
  constructor
  · intro listed
    unfold argumentTerms at listed
    split at listed
    · cases listed; exact .none
    · cases listed; exact .some _
    · contradiction
  · intro listed
    cases listed <;> rfl

def callStatement (result : Option String) (name : String) (arguments : List (Expression model)) :
    Target → Statement model
  | .program => .call result name arguments
  | .service => .external result name arguments

section Calls

variable (model : Model)

def readCall (context : Context) (result : Option String) (expected : Option Slot) (name : String)
    (arguments : CanonicalTerm) : Option (Statement model) := do
  let selected ← callee? context name
  if accepts expected selected.2.result then
    let terms ← argumentTerms arguments
    let values ← readArguments model context.scopes selected.2.parameters terms
    some (callStatement result name values selected.1)
  else none

inductive CallReading (context : Context) (result : Option String) (expected : Option Slot) (name : String)
    (arguments : CanonicalTerm) : Statement model → Prop where
  | call (target : Target) (signature : Signature) (terms : List CanonicalTerm) (values : List (Expression model))
      (callee : Callee context name target signature) (accepted : Accepts expected signature.result)
      (listed : ArgumentTerms arguments terms)
      (read : ArgumentsReading model context.scopes signature.parameters terms values) :
      CallReading context result expected name arguments (callStatement result name values target)

/-- A call whose result is assigned to a named variable, or an allocation. -/
def readCallInto (context : Context) (name callee : String) (arguments : CanonicalTerm) : Option (Statement model) :=
  match lookup context.scopes name with
  | some (.pointer type) =>
      if callee = "malloc" ∧ lookup context.scopes callee = none then
        match argumentTerms arguments with
        | some [count] => (readCount model context.scopes type count).map (.allocate name type)
        | _ => none
      else readCall model context (some name) (some (.pointer type)) callee arguments
  | some (.integer type) => readCall model context (some name) (some (.integer type)) callee arguments
  | _ => none

inductive IntoReading (context : Context) (name : String) : String → CanonicalTerm → Statement model → Prop where
  | allocate (arguments count : CanonicalTerm) (type : IntegerType IntegerExtension) (amount : Expression model)
      (bound : lookup context.scopes name = some (.pointer type)) (unbound : lookup context.scopes "malloc" = none)
      (listed : ArgumentTerms arguments [count]) (countReading : CountReading model context.scopes type count amount) :
      IntoReading context name "malloc" arguments (.allocate name type amount)
  | pointer (callee : String) (arguments : CanonicalTerm) (type : IntegerType IntegerExtension)
      (statement : Statement model) (bound : lookup context.scopes name = some (.pointer type))
      (call : CallReading model context (some name) (some (.pointer type)) callee arguments statement) :
      IntoReading context name callee arguments statement
  | integer (callee : String) (arguments : CanonicalTerm) (type : IntegerType IntegerExtension)
      (statement : Statement model) (bound : lookup context.scopes name = some (.integer type))
      (call : CallReading model context (some name) (some (.integer type)) callee arguments statement) :
      IntoReading context name callee arguments statement

def pointerVariable? (scopes : Scopes) : CanonicalTerm → Option (String × IntegerType IntegerExtension)
  | .node "Var" [.text name] =>
      match lookup scopes name with
      | some (.pointer type) => some (name, type)
      | _ => none
  | _ => none

/-- An expression statement with its single side effect. -/
def readEffect (context : Context) : CanonicalTerm → Option (Statement model)
  | .node "Assign" [.node "Var" [.text name], .node "Call" [.node "Var" [.text callee], arguments]] =>
      readCallInto model context name callee arguments
  | .node "Assign" [target, value] =>
      match pointerVariable? context.scopes target with
      | some selected => (readPointer model context.scopes selected.2 value).map (.setPointer selected.1)
      | none => do
          let place ← readPlace model context.scopes target
          let expression ← (← readOperand model context.scopes value).integer?
          some (.assign place expression)
  | .node "Call" [.node "Var" [.text callee], arguments] =>
      if callee = "free" ∧ lookup context.scopes callee = none then
        match argumentTerms arguments with
        | some [pointer] => (readReleased model context.scopes pointer).map .release
        | _ => none
      else readCall model context none none callee arguments
  | _ => none

inductive EffectReading (context : Context) : CanonicalTerm → Statement model → Prop where
  | into (name callee : String) (arguments : CanonicalTerm) (statement : Statement model)
      (reading : IntoReading model context name callee arguments statement) :
      EffectReading context (.node "Assign" [.node "Var" [.text name], .node "Call" [.node "Var" [.text callee], arguments]])
        statement
  | setPointer (name : String) (value : CanonicalTerm) (type : IntegerType IntegerExtension) (pointer : Expression model)
      (bound : lookup context.scopes name = some (.pointer type))
      (reading : PointerReading model context.scopes type value pointer) :
      EffectReading context (.node "Assign" [.node "Var" [.text name], value]) (.setPointer name pointer)
  | assign (target value : CanonicalTerm) (place : Place model) (expression : Expression model)
      (placeReading : PlaceReading model context.scopes target place)
      (valueReading : OperandReading model context.scopes value (.integer expression)) :
      EffectReading context (.node "Assign" [target, value]) (.assign place expression)
  | release (arguments pointer : CanonicalTerm) (released : Expression model)
      (unbound : lookup context.scopes "free" = none) (listed : ArgumentTerms arguments [pointer])
      (reading : ReleasedReading model context.scopes pointer released) :
      EffectReading context (.node "Call" [.node "Var" [.text "free"], arguments]) (.release released)
  | call (callee : String) (arguments : CanonicalTerm) (statement : Statement model)
      (reading : CallReading model context none none callee arguments statement) :
      EffectReading context (.node "Call" [.node "Var" [.text callee], arguments]) statement

end Calls

theorem readCall_iff (model : Model) (context : Context) (result : Option String) (expected : Option Slot)
    (name : String) (arguments : CanonicalTerm) (statement : Statement model) :
    readCall model context result expected name arguments = some statement ↔
      CallReading model context result expected name arguments statement := by
  constructor
  · intro parsed
    simp only [readCall, bind, Option.bind_eq_some_iff] at parsed
    obtain ⟨⟨target, signature⟩, found, rest⟩ := parsed
    split at rest
    · rename_i accepted
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at rest
      obtain ⟨terms, listed, values, read, rfl⟩ := rest
      exact .call _ _ _ _ ((callee_iff _ _ _ _).mp found) ((accepts_iff _ _).mp accepted)
        ((argumentTerms_iff _ _).mp listed) ((readArguments_iff _ _ _ _ _).mp read)
    · contradiction
  · intro reading
    cases reading with
    | call target signature terms values callee accepted listed read =>
        simp only [readCall, (callee_iff _ _ _ _).mpr callee, (accepts_iff _ _).mpr accepted,
          (argumentTerms_iff _ _).mpr listed, (readArguments_iff _ _ _ _ _).mpr read, bind, Option.bind_some, if_true]

theorem CallReading.notMalloc {model : Model} {context : Context} {result : Option String}
    {expected : Option Slot} {name : String} {arguments : CanonicalTerm} {statement : Statement model}
    (reading : CallReading model context result expected name arguments statement) : name ≠ "malloc" := by
  cases reading with
  | call _ _ _ _ callee => exact callee.notMalloc

theorem CallReading.notFree {model : Model} {context : Context} {result : Option String}
    {expected : Option Slot} {name : String} {arguments : CanonicalTerm} {statement : Statement model}
    (reading : CallReading model context result expected name arguments statement) : name ≠ "free" := by
  cases reading with
  | call _ _ _ _ callee => exact callee.notFree

theorem readCallInto_iff (model : Model) (context : Context) (name callee : String) (arguments : CanonicalTerm)
    (statement : Statement model) :
    readCallInto model context name callee arguments = some statement ↔
      IntoReading model context name callee arguments statement := by
  constructor
  · intro parsed
    unfold readCallInto at parsed
    split at parsed
    · rename_i type bound
      split at parsed
      · rename_i library
        obtain ⟨isMalloc, unbound⟩ := library
        subst isMalloc
        split at parsed
        · rename_i count listed
          obtain ⟨amount, counted, rfl⟩ := Option.map_eq_some_iff.mp parsed
          exact .allocate _ _ _ _ bound unbound ((argumentTerms_iff _ _).mp listed)
            ((readCount_iff _ _ _ _ _).mp counted)
        · contradiction
      · exact .pointer _ _ _ _ bound ((readCall_iff _ _ _ _ _ _ _).mp parsed)
    · rename_i type bound
      exact .integer _ _ _ _ bound ((readCall_iff _ _ _ _ _ _ _).mp parsed)
    · contradiction
  · intro reading
    cases reading with
    | allocate arguments count type amount bound unbound listed countReading =>
        simp only [readCallInto, bound, unbound, and_self, if_true, (argumentTerms_iff _ _).mpr listed,
          (readCount_iff _ _ _ _ _).mpr countReading, Option.map_some]
    | pointer callee arguments type statement bound call =>
        simp only [readCallInto, bound, call.notMalloc, false_and, if_false, (readCall_iff _ _ _ _ _ _ _).mpr call]
    | integer callee arguments type statement bound call =>
        simp only [readCallInto, bound, (readCall_iff _ _ _ _ _ _ _).mpr call]

theorem pointerVariable_none_of_place (model : Model) (scopes : Scopes) (term : CanonicalTerm) (place : Place model)
    (reading : PlaceReading model scopes term place) : pointerVariable? scopes term = none := by
  cases reading with
  | named name type bound => simp only [pointerVariable?, bound]
  | element => rfl
  | indirection => rfl

theorem readEffect_iff (model : Model) (context : Context) (term : CanonicalTerm) (statement : Statement model) :
    readEffect model context term = some statement ↔ EffectReading model context term statement := by
  constructor
  · intro parsed
    unfold readEffect at parsed
    split at parsed
    · exact .into _ _ _ _ ((readCallInto_iff _ _ _ _ _ _).mp parsed)
    · rename_i target value _
      split at parsed
      · rename_i selected found
        obtain ⟨pointer, pointerParsed, rfl⟩ := Option.map_eq_some_iff.mp parsed
        unfold pointerVariable? at found
        split at found
        · rename_i name
          split at found
          · rename_i type bound
            cases found
            exact .setPointer _ _ _ _ bound ((readPointer_iff _ _ _ _ _).mp pointerParsed)
          · contradiction
        · contradiction
      · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
        obtain ⟨place, placeParsed, operand, operandParsed, expression, integer, rfl⟩ := parsed
        rw [Operand.integer?_eq_some] at integer
        subst integer
        exact .assign _ _ _ _ ((readPlace_iff _ _ _ _).mp placeParsed) (readOperand_sound _ _ _ _ operandParsed)
    · rename_i callee arguments
      split at parsed
      · rename_i library
        obtain ⟨isFree, unbound⟩ := library
        subst isFree
        split at parsed
        · rename_i pointer listed
          obtain ⟨released, releasedParsed, rfl⟩ := Option.map_eq_some_iff.mp parsed
          exact .release _ _ _ unbound ((argumentTerms_iff _ _).mp listed) ((readReleased_iff _ _ _ _).mp releasedParsed)
        · contradiction
      · exact .call _ _ _ ((readCall_iff _ _ _ _ _ _ _).mp parsed)
    · contradiction
  · intro reading
    cases reading with
    | into name callee arguments statement reading =>
        simp only [readEffect, (readCallInto_iff _ _ _ _ _ _).mpr reading]
    | setPointer name value type pointer bound reading =>
        unfold readEffect
        split
        · rename_i callee arguments isCall
          cases isCall
          exact absurd reading (not_pointerReading_call _ _ _ _ _)
        · rename_i target other _ same
          simp only [CanonicalTerm.node.injEq, List.cons.injEq, and_true, true_and] at same
          obtain ⟨rfl, rfl⟩ := same
          simp only [pointerVariable?, bound, (readPointer_iff _ _ _ _ _).mpr reading, Option.map_some]
        · rename_i same
          simp at same
        · rename_i _ catchAll _
          exact (catchAll _ _ rfl).elim
    | assign target value place expression placeReading valueReading =>
        unfold readEffect
        split
        · rename_i name callee arguments same
          simp only [CanonicalTerm.node.injEq, List.cons.injEq, and_true, true_and] at same
          obtain ⟨rfl, rfl⟩ := same
          exact absurd valueReading (not_operandReading_call _ _ _ _)
        · rename_i target' value' _ same
          simp only [CanonicalTerm.node.injEq, List.cons.injEq, and_true, true_and] at same
          obtain ⟨rfl, rfl⟩ := same
          simp only [pointerVariable_none_of_place _ _ _ _ placeReading, (readPlace_iff _ _ _ _).mpr placeReading,
            readOperand_complete _ _ _ _ valueReading, Operand.integer?, bind, Option.bind_some]
        · rename_i same
          simp at same
        · rename_i _ catchAll _
          exact (catchAll _ _ rfl).elim
    | release arguments pointer released unbound listed reading =>
        simp only [readEffect, unbound, and_self, if_true, (argumentTerms_iff _ _).mpr listed,
          (readReleased_iff _ _ _ _).mpr reading, Option.map_some]
    | call callee arguments statement reading =>
        simp only [readEffect, reading.notFree, false_and, if_false, (readCall_iff _ _ _ _ _ _ _).mpr reading]

/-! ## Declarations -/

open IntegerObjectConstruction (Shape)

def shapeKind (type : IntegerType IntegerExtension) : Shape → Kind
  | .scalar => .integer type
  | .array count _ => .array type count

/-- The name of a pointer declarator `*name`. -/
def pointerName? : CanonicalTerm → Option String
  | .node "PointerDeclarator" [.node "Pointer" [.node "NoTypeQualifiers" []], .node "NameDeclarator" [.text name]] =>
      some name
  | _ => none

theorem pointerName_none_of_declarator (model : Model) (term : CanonicalTerm) (name : String) (shape : Shape)
    (reading : DeclaratorReading model term name shape) : pointerName? term = none := by
  cases reading
  rfl

section Declarations

variable (model : Model)

def readDeclarator (scopes : Scopes) (type : IntegerType IntegerExtension) :
    CanonicalTerm → Option (Declaration model × Scopes)
  | .node "InitDeclarator" [declarator] =>
      match pointerName? declarator with
      | some name => do
          let inner ← declare scopes name (.pointer type)
          some (.pointer name none, inner)
      | none => do
          let selected ← declarator? model declarator
          let inner ← declare scopes selected.1 (shapeKind type selected.2)
          some (.object ⟨selected.1, type, selected.2⟩ none, inner)
  | .node "InitDeclaratorValue" [declarator, .node "InitializerExpression" [value]] =>
      match pointerName? declarator with
      | some name => do
          let inner ← declare scopes name (.pointer type)
          let pointer ← readPointer model inner type value
          some (.pointer name (some pointer), inner)
      | none => do
          let selected ← declarator? model declarator
          match selected.2 with
          | .scalar => do
              let inner ← declare scopes selected.1 (.integer type)
              let expression ← (← readOperand model inner value).integer?
              some (.object ⟨selected.1, type, .scalar⟩ (some expression), inner)
          | .array _ _ => none
  | _ => none

def pointerDeclarator (name : String) : CanonicalTerm :=
  .node "PointerDeclarator" [.node "Pointer" [.node "NoTypeQualifiers" []], .node "NameDeclarator" [.text name]]

inductive InitReading (scopes : Scopes) (type : IntegerType IntegerExtension) :
    CanonicalTerm → Declaration model → Scopes → Prop where
  | pointer (name : String) (inner : Scopes) (declared : declare scopes name (.pointer type) = some inner) :
      InitReading scopes type (.node "InitDeclarator" [pointerDeclarator name]) (.pointer name none) inner
  | object (declarator : CanonicalTerm) (name : String) (shape : Shape) (inner : Scopes)
      (reading : DeclaratorReading model declarator name shape)
      (declared : declare scopes name (shapeKind type shape) = some inner) :
      InitReading scopes type (.node "InitDeclarator" [declarator]) (.object ⟨name, type, shape⟩ none) inner
  | pointerValue (name : String) (value : CanonicalTerm) (inner : Scopes) (pointer : Expression model)
      (declared : declare scopes name (.pointer type) = some inner)
      (reading : PointerReading model inner type value pointer) :
      InitReading scopes type
        (.node "InitDeclaratorValue" [pointerDeclarator name, .node "InitializerExpression" [value]])
        (.pointer name (some pointer)) inner
  | objectValue (declarator value : CanonicalTerm) (name : String) (inner : Scopes) (expression : Expression model)
      (reading : DeclaratorReading model declarator name .scalar)
      (declared : declare scopes name (.integer type) = some inner)
      (valueReading : OperandReading model inner value (.integer expression)) :
      InitReading scopes type (.node "InitDeclaratorValue" [declarator, .node "InitializerExpression" [value]])
        (.object ⟨name, type, .scalar⟩ (some expression)) inner

def readDeclarators (scopes : Scopes) (type : IntegerType IntegerExtension) :
    List CanonicalTerm → Option (List (Declaration model) × Scopes)
  | [] => some ([], scopes)
  | first :: rest => do
      let head ← readDeclarator model scopes type first
      let tail ← readDeclarators head.2 type rest
      some (head.1 :: tail.1, tail.2)

inductive DeclaratorsReading (type : IntegerType IntegerExtension) :
    Scopes → List CanonicalTerm → List (Declaration model) → Scopes → Prop where
  | nil (scopes : Scopes) : DeclaratorsReading type scopes [] [] scopes
  | cons (scopes : Scopes) (first : CanonicalTerm) (rest : List CanonicalTerm) (declaration : Declaration model)
      (declarations : List (Declaration model)) (inner final : Scopes)
      (head : InitReading model scopes type first declaration inner)
      (tail : DeclaratorsReading type inner rest declarations final) :
      DeclaratorsReading type scopes (first :: rest) (declaration :: declarations) final

end Declarations

theorem readDeclarator_iff (model : Model) (scopes : Scopes) (type : IntegerType IntegerExtension)
    (term : CanonicalTerm) (declaration : Declaration model) (inner : Scopes) :
    readDeclarator model scopes type term = some (declaration, inner) ↔
      InitReading model scopes type term declaration inner := by
  constructor
  · intro parsed
    unfold readDeclarator at parsed
    split at parsed
    · rename_i declarator
      split at parsed
      · rename_i name named
        unfold pointerName? at named
        split at named
        · cases named
          simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at parsed
          obtain ⟨scopesAfter, declared, rfl, rfl⟩ := parsed
          exact .pointer _ _ declared
        · contradiction
      · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at parsed
        obtain ⟨⟨name, shape⟩, selected, scopesAfter, declared, rfl, rfl⟩ := parsed
        exact .object _ _ _ _ ((declarator_iff _ _ _ _).mp selected) declared
    · rename_i declarator value
      split at parsed
      · rename_i name named
        unfold pointerName? at named
        split at named
        · cases named
          simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at parsed
          obtain ⟨scopesAfter, declared, pointer, pointerParsed, rfl, rfl⟩ := parsed
          exact .pointerValue _ _ _ _ declared ((readPointer_iff _ _ _ _ _).mp pointerParsed)
        · contradiction
      · simp only [bind, Option.bind_eq_some_iff] at parsed
        obtain ⟨⟨name, shape⟩, selected, rest⟩ := parsed
        cases shape with
        | scalar =>
            simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at rest
            obtain ⟨scopesAfter, declared, operand, operandParsed, expression, integer, rfl, rfl⟩ := rest
            rw [Operand.integer?_eq_some] at integer
            subst integer
            exact .objectValue _ _ _ _ _ ((declarator_iff _ _ _ _).mp selected) declared
              (readOperand_sound _ _ _ _ operandParsed)
        | array => cases rest
    · contradiction
  · intro reading
    cases reading with
    | pointer name inner declared =>
        simp only [readDeclarator, pointerDeclarator, pointerName?, declared, bind, Option.bind_some]
    | object declarator name shape inner reading declared =>
        simp only [readDeclarator, pointerName_none_of_declarator _ _ _ _ reading,
          (declarator_iff _ _ _ _).mpr reading, declared, bind, Option.bind_some]
    | pointerValue name value inner pointer declared reading =>
        simp only [readDeclarator, pointerDeclarator, pointerName?, declared, (readPointer_iff _ _ _ _ _).mpr reading,
          bind, Option.bind_some]
    | objectValue declarator value name inner expression reading declared valueReading =>
        simp only [readDeclarator, pointerName_none_of_declarator _ _ _ _ reading,
          (declarator_iff _ _ _ _).mpr reading, declared, readOperand_complete _ _ _ _ valueReading,
          Operand.integer?, bind, Option.bind_some]

theorem readDeclarators_iff (model : Model) (scopes : Scopes) (type : IntegerType IntegerExtension)
    (terms : List CanonicalTerm) (declarations : List (Declaration model)) (final : Scopes) :
    readDeclarators model scopes type terms = some (declarations, final) ↔
      DeclaratorsReading model type scopes terms declarations final := by
  induction terms generalizing scopes declarations final with
  | nil =>
      constructor
      · intro parsed
        simp only [readDeclarators, Option.some.injEq, Prod.mk.injEq] at parsed
        obtain ⟨rfl, rfl⟩ := parsed
        exact .nil _
      · intro reading
        cases reading
        rfl
  | cons first rest ih =>
      constructor
      · intro parsed
        simp only [readDeclarators, bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at parsed
        obtain ⟨⟨declaration, inner⟩, head, ⟨declarations', final'⟩, tail, rfl, rfl⟩ := parsed
        exact .cons _ _ _ _ _ _ _ ((readDeclarator_iff _ _ _ _ _ _).mp head) ((ih _ _ _).mp tail)
      · intro reading
        cases reading with
        | cons _ _ _ declaration declarations inner final head tail =>
            simp only [readDeclarators, (readDeclarator_iff _ _ _ _ _ _).mpr head, (ih _ _ _).mpr tail, bind,
              Option.bind_some]

/-! ## Statements and blocks -/

section Statements

variable (model : Model)

mutual
def readStatement (context : Context) (loop : Bool) : CanonicalTerm → Option (Statement model)
  | .node "CompoundStatement" [.node "Block" [.seq items]] => readItems context.enter loop items
  | .node "ExpressionStatement" [.node "NoFullExpression" []] => some .skip
  | .node "ExpressionStatement" [.node "SomeFullExpression" [effect]] => readEffect model context effect
  | .node "SelectionStatement" [.node "If" [condition, yes]] => do
      let test ← (← readOperand model context.scopes condition).integer?
      some (.conditional test (← readStatement context loop yes) .skip)
  | .node "SelectionStatement" [.node "IfElse" [condition, yes, no]] => do
      let test ← (← readOperand model context.scopes condition).integer?
      some (.conditional test (← readStatement context loop yes) (← readStatement context loop no))
  | .node "IterationStatement" [.node "While" [condition, body]] => do
      let test ← (← readOperand model context.scopes condition).integer?
      some (.whileLoop test (← readStatement context true body))
  | .node "JumpStatement" [.node "Break" []] => if loop then some .breakLoop else none
  | .node "JumpStatement" [.node "Continue" []] => if loop then some .continueLoop else none
  | .node "JumpStatement" [.node "Return" [.node "NoFullExpression" []]] =>
      match context.result with
      | none => some (.returnValue none)
      | some _ => none
  | .node "JumpStatement" [.node "Return" [.node "SomeFullExpression" [value]]] =>
      match context.result with
      | some slot => (readSlot model context.scopes slot value).map fun expression => .returnValue (some expression)
      | none => none
  | _ => none
termination_by term => sizeOf term

def readItems (context : Context) (loop : Bool) : List CanonicalTerm → Option (Statement model)
  | [] => some .skip
  | [.node "BlockStatement" [term]] => readStatement context loop term
  | .node "BlockStatement" [term] :: rest => do
      some (.sequence (← readStatement context loop term) (← readItems context loop rest))
  | .node "BlockDeclaration" [.node "Declaration" [specifiers, .node "InitDeclarators" [.seq (first :: others)]]] ::
      rest => do
      let type ← specifiers? specifiers
      let declared ← readDeclarators model context.scopes type (first :: others)
      some (.block declared.1 (← readItems { context with scopes := declared.2 } loop rest))
  | _ => none
termination_by items => sizeOf items
end

mutual
inductive StatementReading : Context → Bool → CanonicalTerm → Statement model → Prop where
  | compound (context : Context) (loop : Bool) (items : List CanonicalTerm) (statement : Statement model)
      (reading : ItemsReading context.enter loop items statement) :
      StatementReading context loop (.node "CompoundStatement" [.node "Block" [.seq items]]) statement
  | empty (context : Context) (loop : Bool) :
      StatementReading context loop (.node "ExpressionStatement" [.node "NoFullExpression" []]) .skip
  | effect (context : Context) (loop : Bool) (effect : CanonicalTerm) (statement : Statement model)
      (reading : EffectReading model context effect statement) :
      StatementReading context loop (.node "ExpressionStatement" [.node "SomeFullExpression" [effect]]) statement
  | conditional (context : Context) (loop : Bool) (condition yes : CanonicalTerm) (test : Expression model)
      (body : Statement model) (conditionReading : OperandReading model context.scopes condition (.integer test))
      (yesReading : StatementReading context loop yes body) :
      StatementReading context loop (.node "SelectionStatement" [.node "If" [condition, yes]])
        (.conditional test body .skip)
  | conditionalElse (context : Context) (loop : Bool) (condition yes no : CanonicalTerm) (test : Expression model)
      (first second : Statement model)
      (conditionReading : OperandReading model context.scopes condition (.integer test))
      (yesReading : StatementReading context loop yes first) (noReading : StatementReading context loop no second) :
      StatementReading context loop (.node "SelectionStatement" [.node "IfElse" [condition, yes, no]])
        (.conditional test first second)
  | whileLoop (context : Context) (loop : Bool) (condition body : CanonicalTerm) (test : Expression model)
      (statement : Statement model)
      (conditionReading : OperandReading model context.scopes condition (.integer test))
      (bodyReading : StatementReading context true body statement) :
      StatementReading context loop (.node "IterationStatement" [.node "While" [condition, body]])
        (.whileLoop test statement)
  | breakLoop (context : Context) :
      StatementReading context true (.node "JumpStatement" [.node "Break" []]) .breakLoop
  | continueLoop (context : Context) :
      StatementReading context true (.node "JumpStatement" [.node "Continue" []]) .continueLoop
  | returnNothing (context : Context) (loop : Bool) (noResult : context.result = none) :
      StatementReading context loop (.node "JumpStatement" [.node "Return" [.node "NoFullExpression" []]])
        (.returnValue none)
  | returnValue (context : Context) (loop : Bool) (slot : Slot) (value : CanonicalTerm) (expression : Expression model)
      (result : context.result = some slot) (reading : SlotReading model context.scopes slot value expression) :
      StatementReading context loop
        (.node "JumpStatement" [.node "Return" [.node "SomeFullExpression" [value]]]) (.returnValue (some expression))

inductive ItemsReading : Context → Bool → List CanonicalTerm → Statement model → Prop where
  | nil (context : Context) (loop : Bool) : ItemsReading context loop [] .skip
  | single (context : Context) (loop : Bool) (term : CanonicalTerm) (statement : Statement model)
      (reading : StatementReading context loop term statement) :
      ItemsReading context loop [.node "BlockStatement" [term]] statement
  | sequence (context : Context) (loop : Bool) (term : CanonicalTerm) (rest : List CanonicalTerm)
      (first second : Statement model) (nonempty : rest ≠ [])
      (head : StatementReading context loop term first) (tail : ItemsReading context loop rest second) :
      ItemsReading context loop (.node "BlockStatement" [term] :: rest) (.sequence first second)
  | declaration (context : Context) (loop : Bool) (specifiers first : CanonicalTerm)
      (others rest : List CanonicalTerm) (type : IntegerType IntegerExtension)
      (declarations : List (Declaration model)) (inner : Scopes) (body : Statement model)
      (typed : SpecifiersReading specifiers type)
      (declared : DeclaratorsReading model type context.scopes (first :: others) declarations inner)
      (tail : ItemsReading { context with scopes := inner } loop rest body) :
      ItemsReading context loop
        (.node "BlockDeclaration" [.node "Declaration" [specifiers, .node "InitDeclarators" [.seq (first :: others)]]] ::
          rest) (.block declarations body)
end

end Statements

mutual
theorem readStatement_sound (model : Model) (context : Context) (loop : Bool) (term : CanonicalTerm)
    (statement : Statement model) (parsed : readStatement model context loop term = some statement) :
    StatementReading model context loop term statement := by
  unfold readStatement at parsed
  split at parsed
  · exact .compound _ _ _ _ (readItems_sound _ _ _ _ _ parsed)
  · cases parsed; exact .empty _ _
  · exact .effect _ _ _ _ ((readEffect_iff _ _ _ _).mp parsed)
  · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨operand, operandParsed, test, integer, body, bodyParsed, rfl⟩ := parsed
    rw [Operand.integer?_eq_some] at integer
    subst integer
    exact .conditional _ _ _ _ _ _ (readOperand_sound _ _ _ _ operandParsed)
      (readStatement_sound _ _ _ _ _ bodyParsed)
  · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨operand, operandParsed, test, integer, first, firstParsed, second, secondParsed, rfl⟩ := parsed
    rw [Operand.integer?_eq_some] at integer
    subst integer
    exact .conditionalElse _ _ _ _ _ _ _ _ (readOperand_sound _ _ _ _ operandParsed)
      (readStatement_sound _ _ _ _ _ firstParsed) (readStatement_sound _ _ _ _ _ secondParsed)
  · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨operand, operandParsed, test, integer, body, bodyParsed, rfl⟩ := parsed
    rw [Operand.integer?_eq_some] at integer
    subst integer
    exact .whileLoop _ _ _ _ _ _ (readOperand_sound _ _ _ _ operandParsed)
      (readStatement_sound _ _ _ _ _ bodyParsed)
  · split at parsed
    · rename_i inLoop
      subst inLoop
      cases parsed
      exact .breakLoop _
    · contradiction
  · split at parsed
    · rename_i inLoop
      subst inLoop
      cases parsed
      exact .continueLoop _
    · contradiction
  · split at parsed
    · rename_i noResult
      cases parsed
      exact .returnNothing _ _ noResult
    · contradiction
  · split at parsed
    · rename_i slot result
      obtain ⟨expression, slotParsed, rfl⟩ := Option.map_eq_some_iff.mp parsed
      exact .returnValue _ _ _ _ _ result ((readSlot_iff _ _ _ _ _).mp slotParsed)
    · contradiction
  · contradiction
termination_by sizeOf term

theorem readItems_sound (model : Model) (context : Context) (loop : Bool) (items : List CanonicalTerm)
    (statement : Statement model) (parsed : readItems model context loop items = some statement) :
    ItemsReading model context loop items statement := by
  unfold readItems at parsed
  split at parsed
  · cases parsed; exact .nil _ _
  · exact .single _ _ _ _ (readStatement_sound _ _ _ _ _ parsed)
  · rename_i term rest notSingle
    simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨first, firstParsed, second, secondParsed, rfl⟩ := parsed
    have nonempty : rest ≠ [] := by
      rintro rfl
      simp_all
    exact .sequence _ _ _ _ _ _ nonempty (readStatement_sound _ _ _ _ _ firstParsed)
      (readItems_sound _ _ _ _ _ secondParsed)
  · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨type, typed, ⟨declarations, inner⟩, declared, body, bodyParsed, rfl⟩ := parsed
    exact .declaration _ _ _ _ _ _ _ _ _ _ (specifiers_sound _ _ typed)
      ((readDeclarators_iff _ _ _ _ _ _).mp declared) (readItems_sound _ _ _ _ _ bodyParsed)
  · contradiction
termination_by sizeOf items
end

mutual
theorem readStatement_complete (model : Model) (context : Context) (loop : Bool) (term : CanonicalTerm)
    (statement : Statement model) (reading : StatementReading model context loop term statement) :
    readStatement model context loop term = some statement := by
  cases reading with
  | compound context loop items statement reading =>
      simp only [readStatement, readItems_complete _ _ _ _ _ reading]
  | empty => simp only [readStatement]
  | effect context loop effect statement reading =>
      simp only [readStatement, (readEffect_iff _ _ _ _).mpr reading]
  | conditional context loop condition yes test body conditionReading yesReading =>
      simp only [readStatement, readOperand_complete _ _ _ _ conditionReading, Operand.integer?,
        readStatement_complete _ _ _ _ _ yesReading, bind, Option.bind_some]
  | conditionalElse context loop condition yes no test first second conditionReading yesReading noReading =>
      simp only [readStatement, readOperand_complete _ _ _ _ conditionReading, Operand.integer?,
        readStatement_complete _ _ _ _ _ yesReading, readStatement_complete _ _ _ _ _ noReading, bind,
        Option.bind_some]
  | whileLoop context loop condition body test statement conditionReading bodyReading =>
      simp only [readStatement, readOperand_complete _ _ _ _ conditionReading, Operand.integer?,
        readStatement_complete _ _ _ _ _ bodyReading, bind, Option.bind_some]
  | breakLoop | continueLoop => simp only [readStatement, if_true]
  | returnNothing context loop noResult => simp only [readStatement, noResult]
  | returnValue context loop slot value expression result reading =>
      simp only [readStatement, result, (readSlot_iff _ _ _ _ _).mpr reading, Option.map_some]
termination_by sizeOf term

theorem readItems_complete (model : Model) (context : Context) (loop : Bool) (items : List CanonicalTerm)
    (statement : Statement model) (reading : ItemsReading model context loop items statement) :
    readItems model context loop items = some statement := by
  cases reading with
  | nil => simp only [readItems]
  | single context loop term statement reading =>
      simp only [readItems, readStatement_complete _ _ _ _ _ reading]
  | sequence context loop term rest first second nonempty head tail =>
      cases rest with
      | nil => exact absurd rfl nonempty
      | cons next others =>
          simp only [readItems, readStatement_complete _ _ _ _ _ head, readItems_complete _ _ _ _ _ tail, bind,
            Option.bind_some]
  | declaration context loop specifiers first others rest type declarations inner body typed declared tail =>
      simp only [readItems, specifiers_complete _ _ typed, (readDeclarators_iff _ _ _ _ _ _).mpr declared,
        readItems_complete _ _ _ _ _ tail, bind, Option.bind_some]
termination_by sizeOf items
end

theorem readStatement_iff (model : Model) (context : Context) (loop : Bool) (term : CanonicalTerm)
    (statement : Statement model) :
    readStatement model context loop term = some statement ↔ StatementReading model context loop term statement :=
  ⟨readStatement_sound _ _ _ _ _, readStatement_complete _ _ _ _ _⟩

theorem readItems_iff (model : Model) (context : Context) (loop : Bool) (items : List CanonicalTerm)
    (statement : Statement model) :
    readItems model context loop items = some statement ↔ ItemsReading model context loop items statement :=
  ⟨readItems_sound _ _ _ _ _, readItems_complete _ _ _ _ _⟩

/-! ## Function definitions -/

def Slot.parameter (name : String) : Slot → Parameter
  | .integer type => .integer name type
  | .pointer _ => .pointer name

def parameter? : CanonicalTerm → Option (String × Slot)
  | .node "NamedParameter" [specifiers, .node "Declarator" [.node "NameDeclarator" [.text name]]] =>
      (specifiers? specifiers).map fun type => (name, .integer type)
  | .node "NamedParameter" [specifiers, .node "PointerDeclarator"
      [.node "Pointer" [.node "NoTypeQualifiers" []], .node "NameDeclarator" [.text name]]] =>
      (specifiers? specifiers).map fun type => (name, .pointer type)
  | _ => none

inductive ParameterReading : CanonicalTerm → String × Slot → Prop where
  | integer (specifiers : CanonicalTerm) (name : String) (type : IntegerType IntegerExtension)
      (typed : SpecifiersReading specifiers type) :
      ParameterReading (.node "NamedParameter" [specifiers, .node "Declarator" [.node "NameDeclarator" [.text name]]])
        (name, .integer type)
  | pointer (specifiers : CanonicalTerm) (name : String) (type : IntegerType IntegerExtension)
      (typed : SpecifiersReading specifiers type) :
      ParameterReading (.node "NamedParameter" [specifiers, pointerDeclarator name]) (name, .pointer type)

theorem parameter_iff (term : CanonicalTerm) (parameter : String × Slot) :
    parameter? term = some parameter ↔ ParameterReading term parameter := by
  constructor
  · intro parsed
    unfold parameter? at parsed
    split at parsed
    · obtain ⟨type, typed, rfl⟩ := Option.map_eq_some_iff.mp parsed
      exact .integer _ _ _ (specifiers_sound _ _ typed)
    · obtain ⟨type, typed, rfl⟩ := Option.map_eq_some_iff.mp parsed
      exact .pointer _ _ _ (specifiers_sound _ _ typed)
    · contradiction
  · intro reading
    cases reading with
    | integer specifiers name type typed => simp only [parameter?, specifiers_complete _ _ typed, Option.map_some]
    | pointer specifiers name type typed =>
        simp only [parameter?, pointerDeclarator, specifiers_complete _ _ typed, Option.map_some]

def parameters? : List CanonicalTerm → Option (List (String × Slot))
  | [] => some []
  | first :: rest => do some ((← parameter? first) :: (← parameters? rest))

theorem parameters_iff (terms : List CanonicalTerm) (parameters : List (String × Slot)) :
    parameters? terms = some parameters ↔ List.Forall₂ ParameterReading terms parameters := by
  induction terms generalizing parameters with
  | nil =>
      constructor
      · intro parsed; cases parsed; exact .nil
      · intro reading; cases reading; rfl
  | cons first rest ih =>
      constructor
      · intro parsed
        simp only [parameters?, bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
        obtain ⟨head, headParsed, tail, tailParsed, rfl⟩ := parsed
        exact .cons ((parameter_iff _ _).mp headParsed) ((ih _).mp tailParsed)
      · intro reading
        cases reading with
        | cons head tail =>
            simp only [parameters?, (parameter_iff _ _).mpr head, (ih _).mpr tail, bind, Option.bind_some]

/-- The term of the parameter list `(void)`. -/
def voidParameters : CanonicalTerm :=
  .node "ParameterTypes" [.seq [.node "AbstractParameter"
    [.node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []], .node "NoAbstractDeclarator" []]]]

def parameterList? : CanonicalTerm → Option (List (String × Slot))
  | .node "ParameterTypes" [.seq [.node "AbstractParameter"
      [.node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []], .node "NoAbstractDeclarator" []]]] => some []
  | .node "ParameterTypes" [.seq terms] => parameters? terms
  | _ => none

inductive ParameterListReading : CanonicalTerm → List (String × Slot) → Prop where
  | none : ParameterListReading voidParameters []
  | named (terms : List CanonicalTerm) (parameters : List (String × Slot))
      (reading : List.Forall₂ ParameterReading terms parameters) :
      ParameterListReading (.node "ParameterTypes" [.seq terms]) parameters

theorem parameterList_iff (term : CanonicalTerm) (parameters : List (String × Slot)) :
    parameterList? term = some parameters ↔ ParameterListReading term parameters := by
  constructor
  · intro parsed
    unfold parameterList? at parsed
    split at parsed
    · cases parsed; exact .none
    · exact .named _ _ ((parameters_iff _ _).mp parsed)
    · contradiction
  · intro reading
    cases reading with
    | none => rfl
    | named terms parameters reading =>
        have listed := (parameters_iff _ _).mpr reading
        unfold parameterList?
        split
        · rename_i same
          simp only [CanonicalTerm.node.injEq, List.cons.injEq, CanonicalTerm.seq.injEq, and_true,
            true_and] at same
          subst same
          simp [parameters?, parameter?] at listed
        · rename_i terms' same
          simp only [CanonicalTerm.node.injEq, List.cons.injEq, CanonicalTerm.seq.injEq, and_true,
            true_and] at same
          subst same
          exact listed
        · rename_i catchAll
          exact (catchAll _ rfl).elim

/-- The name, parameters and result type of a function definition. -/
structure Header where
  name : String
  parameters : List (String × Slot)
  result : Option Slot
  deriving DecidableEq, Repr

def Header.signature (header : Header) : Signature := ⟨header.parameters.map Prod.snd, header.result⟩

def Header.core (header : Header) : List Parameter :=
  header.parameters.map fun parameter => parameter.2.parameter parameter.1

def functionDeclarator (name : String) (parameters : CanonicalTerm) : CanonicalTerm :=
  .node "FunctionDeclarator" [.node "NameDeclarator" [.text name], parameters]

def voidSpecifiers : CanonicalTerm := .node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []]

def header? : CanonicalTerm → CanonicalTerm → Option Header
  | .node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []],
    .node "Declarator" [.node "FunctionDeclarator" [.node "NameDeclarator" [.text name], parameterTerm]] =>
      (parameterList? parameterTerm).map fun parameters => ⟨name, parameters, none⟩
  | specifiers, .node "Declarator" [.node "FunctionDeclarator" [.node "NameDeclarator" [.text name], parameterTerm]] => do
      let parameters ← parameterList? parameterTerm
      let type ← specifiers? specifiers
      some ⟨name, parameters, some (.integer type)⟩
  | specifiers, .node "PointerDeclarator" [.node "Pointer" [.node "NoTypeQualifiers" []],
      .node "FunctionDeclarator" [.node "NameDeclarator" [.text name], parameterTerm]] => do
      let parameters ← parameterList? parameterTerm
      let type ← specifiers? specifiers
      some ⟨name, parameters, some (.pointer type)⟩
  | _, _ => none

inductive HeaderReading : CanonicalTerm → CanonicalTerm → Header → Prop where
  | void (name : String) (parameterTerm : CanonicalTerm) (parameters : List (String × Slot))
      (listed : ParameterListReading parameterTerm parameters) :
      HeaderReading voidSpecifiers (.node "Declarator" [functionDeclarator name parameterTerm]) ⟨name, parameters, none⟩
  | integer (specifiers : CanonicalTerm) (name : String) (parameterTerm : CanonicalTerm)
      (parameters : List (String × Slot)) (type : IntegerType IntegerExtension)
      (listed : ParameterListReading parameterTerm parameters) (typed : SpecifiersReading specifiers type) :
      HeaderReading specifiers (.node "Declarator" [functionDeclarator name parameterTerm])
        ⟨name, parameters, some (.integer type)⟩
  | pointer (specifiers : CanonicalTerm) (name : String) (parameterTerm : CanonicalTerm)
      (parameters : List (String × Slot)) (type : IntegerType IntegerExtension)
      (listed : ParameterListReading parameterTerm parameters) (typed : SpecifiersReading specifiers type) :
      HeaderReading specifiers
        (.node "PointerDeclarator" [.node "Pointer" [.node "NoTypeQualifiers" []], functionDeclarator name parameterTerm])
        ⟨name, parameters, some (.pointer type)⟩

theorem header_iff (specifiers declarator : CanonicalTerm) (header : Header) :
    header? specifiers declarator = some header ↔ HeaderReading specifiers declarator header := by
  constructor
  · intro parsed
    unfold header? at parsed
    split at parsed
    · obtain ⟨parameters, listed, rfl⟩ := Option.map_eq_some_iff.mp parsed
      exact .void _ _ _ ((parameterList_iff _ _).mp listed)
    · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨parameters, listed, type, typed, rfl⟩ := parsed
      exact .integer _ _ _ _ _ ((parameterList_iff _ _).mp listed) (specifiers_sound _ _ typed)
    · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨parameters, listed, type, typed, rfl⟩ := parsed
      exact .pointer _ _ _ _ _ ((parameterList_iff _ _).mp listed) (specifiers_sound _ _ typed)
    · contradiction
  · intro reading
    cases reading with
    | void name parameterTerm parameters listed =>
        simp only [header?, voidSpecifiers, functionDeclarator, (parameterList_iff _ _).mpr listed, Option.map_some]
    | integer specifiers name parameterTerm parameters type listed typed =>
        have typedSome := specifiers_complete _ _ typed
        unfold header?
        split
        · simp [specifiers?] at typedSome
        · rename_i same
          simp only [functionDeclarator, CanonicalTerm.node.injEq, List.cons.injEq, CanonicalTerm.text.injEq,
            and_true, true_and] at same
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
          simp only [(parameterList_iff _ _).mpr listed, typedSome, bind, Option.bind_some]
        · rename_i same
          simp [functionDeclarator] at same
        · rename_i second _ _
          exact (second _ _ rfl).elim
    | pointer specifiers name parameterTerm parameters type listed typed =>
        simp only [header?, functionDeclarator, (parameterList_iff _ _).mpr listed, specifiers_complete _ _ typed,
          bind, Option.bind_some]

/-- Bind the parameters into the outermost scope of the body; a repeated name is refused. -/
def bindParameters : Scopes → List (String × Slot) → Option Scopes
  | scopes, [] => some scopes
  | scopes, parameter :: rest => do bindParameters (← declare scopes parameter.1 parameter.2.kind) rest

/-- Reaching the end of `main` returns `0` when `main` returns `int`. -/
def finish (model : Model) (header : Header) (body : Statement model) : Option (Statement model) :=
  if header.name = "main" ∧ header.result = some (.integer .int) then
    (literal? model "0").map fun zero => .sequence body (.returnValue (some (.constant zero)))
  else some body

inductive Finished (model : Model) (header : Header) (body : Statement model) : Statement model → Prop where
  | main (zero : IntegerScalar.Value model.parameters) (named : header.name = "main")
      (returnsInt : header.result = some (.integer .int)) (zeroReading : Literal model "0" zero) :
      Finished model header body (.sequence body (.returnValue (some (.constant zero))))
  | other (notMain : ¬ (header.name = "main" ∧ header.result = some (.integer .int))) : Finished model header body body

theorem finish_iff (model : Model) (header : Header) (body statement : Statement model) :
    finish model header body = some statement ↔ Finished model header body statement := by
  constructor
  · intro finished
    unfold finish at finished
    split at finished
    · rename_i isMain
      obtain ⟨zero, zeroParsed, rfl⟩ := Option.map_eq_some_iff.mp finished
      exact .main _ isMain.1 isMain.2 (literal_sound _ _ _ zeroParsed)
    · rename_i notMain
      cases finished
      exact .other notMain
  · intro finished
    cases finished with
    | main zero named returnsInt zeroReading =>
        simp only [finish, named, returnsInt, and_self, if_true, literal_complete _ _ _ zeroReading, Option.map_some]
    | other notMain => simp only [finish, notMain, if_false]

def definition? : CanonicalTerm → Option (Header × List CanonicalTerm)
  | .node "ExternalFunction" [.node "FunctionDefinition" [specifiers, declarator, .seq [], .node "Block" [.seq items]]] =>
      (header? specifiers declarator).map fun header => (header, items)
  | _ => none

inductive DefinitionReading : CanonicalTerm → Header × List CanonicalTerm → Prop where
  | definition (specifiers declarator : CanonicalTerm) (items : List CanonicalTerm) (header : Header)
      (reading : HeaderReading specifiers declarator header) :
      DefinitionReading
        (.node "ExternalFunction" [.node "FunctionDefinition" [specifiers, declarator, .seq [], .node "Block" [.seq items]]])
        (header, items)

theorem definition_iff (term : CanonicalTerm) (definition : Header × List CanonicalTerm) :
    definition? term = some definition ↔ DefinitionReading term definition := by
  constructor
  · intro parsed
    unfold definition? at parsed
    split at parsed
    · obtain ⟨header, headerParsed, rfl⟩ := Option.map_eq_some_iff.mp parsed
      exact .definition _ _ _ _ ((header_iff _ _ _).mp headerParsed)
    · contradiction
  · intro reading
    cases reading with
    | definition specifiers declarator items header reading =>
        simp only [definition?, (header_iff _ _ _).mpr reading, Option.map_some]

def definitions? : List CanonicalTerm → Option (List (Header × List CanonicalTerm))
  | [] => some []
  | first :: rest => do some ((← definition? first) :: (← definitions? rest))

theorem definitions_iff (terms : List CanonicalTerm) (definitions : List (Header × List CanonicalTerm)) :
    definitions? terms = some definitions ↔ List.Forall₂ DefinitionReading terms definitions := by
  induction terms generalizing definitions with
  | nil =>
      constructor
      · intro parsed; cases parsed; exact .nil
      · intro reading; cases reading; rfl
  | cons first rest ih =>
      constructor
      · intro parsed
        simp only [definitions?, bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
        obtain ⟨head, headParsed, tail, tailParsed, rfl⟩ := parsed
        exact .cons ((definition_iff _ _).mp headParsed) ((ih _).mp tailParsed)
      · intro reading
        cases reading with
        | cons head tail =>
            simp only [definitions?, (definition_iff _ _).mpr head, (ih _).mpr tail, bind, Option.bind_some]

section Functions

variable (model : Model) (functions services : List (String × Signature))

def readFunction (definition : Header × List CanonicalTerm) : Option (String × Function model) := do
  let scopes ← bindParameters [[]] definition.1.parameters
  let body ← readItems model ⟨scopes, functions, services, definition.1.result⟩ false definition.2
  let finished ← finish model definition.1 body
  some (definition.1.name, ⟨definition.1.core, finished⟩)

inductive FunctionReading : Header × List CanonicalTerm → String × Function model → Prop where
  | function (header : Header) (items : List CanonicalTerm) (scopes : Scopes) (body finished : Statement model)
      (bound : bindParameters [[]] header.parameters = some scopes)
      (bodyReading : ItemsReading model ⟨scopes, functions, services, header.result⟩ false items body)
      (finishing : Finished model header body finished) :
      FunctionReading (header, items) (header.name, ⟨header.core, finished⟩)

def readFunctions : List (Header × List CanonicalTerm) → Option (Program model)
  | [] => some []
  | first :: rest => do some ((← readFunction model functions services first) :: (← readFunctions rest))

end Functions

theorem readFunction_iff (model : Model) (functions services : List (String × Signature))
    (definition : Header × List CanonicalTerm) (function : String × Function model) :
    readFunction model functions services definition = some function ↔
      FunctionReading model functions services definition function := by
  constructor
  · intro parsed
    simp only [readFunction, bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨scopes, bound, body, bodyParsed, finished, finishing, rfl⟩ := parsed
    exact .function _ _ _ _ _ bound ((readItems_iff _ _ _ _ _).mp bodyParsed) ((finish_iff _ _ _ _).mp finishing)
  · intro reading
    cases reading with
    | function header items scopes body finished bound bodyReading finishing =>
        simp only [readFunction, bound, (readItems_iff _ _ _ _ _).mpr bodyReading, (finish_iff _ _ _ _).mpr finishing,
          bind, Option.bind_some]

theorem readFunctions_iff (model : Model) (functions services : List (String × Signature))
    (definitions : List (Header × List CanonicalTerm)) (program : Program model) :
    readFunctions model functions services definitions = some program ↔
      List.Forall₂ (FunctionReading model functions services) definitions program := by
  induction definitions generalizing program with
  | nil =>
      constructor
      · intro parsed; cases parsed; exact .nil
      · intro reading; cases reading; rfl
  | cons first rest ih =>
      constructor
      · intro parsed
        simp only [readFunctions, bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
        obtain ⟨head, headParsed, tail, tailParsed, rfl⟩ := parsed
        exact .cons ((readFunction_iff _ _ _ _ _).mp headParsed) ((ih _).mp tailParsed)
      · intro reading
        cases reading with
        | cons head tail =>
            simp only [readFunctions, (readFunction_iff _ _ _ _ _).mpr head, (ih _).mpr tail, bind, Option.bind_some]

/-! ## Translation units -/

def signatures (definitions : List (Header × List CanonicalTerm)) : List (String × Signature) :=
  definitions.map fun definition => (definition.1.name, definition.1.signature)

/-- Admissible function names: distinct, and not the reserved allocation functions. -/
def Admissible (definitions : List (Header × List CanonicalTerm)) : Prop :=
  (definitions.map fun definition => definition.1.name).Nodup ∧
    "malloc" ∉ definitions.map (fun definition => definition.1.name) ∧
    "free" ∉ definitions.map (fun definition => definition.1.name)

instance (definitions : List (Header × List CanonicalTerm)) : Decidable (Admissible definitions) := by
  unfold Admissible
  infer_instance

/-- Read a translation unit of function definitions against the host's services. -/
def readUnit (model : Model) (services : List (String × Signature)) : CanonicalTerm → Option (Program model)
  | .node "TranslationUnit" [.seq externals] => do
      let definitions ← definitions? externals
      if Admissible definitions then readFunctions model (signatures definitions) services definitions else none
  | _ => none

inductive UnitReading (model : Model) (services : List (String × Signature)) : CanonicalTerm → Program model → Prop where
  | unit (externals : List CanonicalTerm) (definitions : List (Header × List CanonicalTerm)) (program : Program model)
      (listed : List.Forall₂ DefinitionReading externals definitions) (admissible : Admissible definitions)
      (functions : List.Forall₂ (FunctionReading model (signatures definitions) services) definitions program) :
      UnitReading model services (.node "TranslationUnit" [.seq externals]) program

theorem readUnit_iff (model : Model) (services : List (String × Signature)) (term : CanonicalTerm)
    (program : Program model) : readUnit model services term = some program ↔ UnitReading model services term program := by
  constructor
  · intro parsed
    unfold readUnit at parsed
    split at parsed
    · simp only [bind, Option.bind_eq_some_iff] at parsed
      obtain ⟨definitions, listed, rest⟩ := parsed
      split at rest
      · rename_i admissible
        exact .unit _ _ _ ((definitions_iff _ _).mp listed) admissible ((readFunctions_iff _ _ _ _ _).mp rest)
      · contradiction
    · contradiction
  · intro reading
    cases reading with
    | unit externals definitions program listed admissible functions =>
        simp only [readUnit, (definitions_iff _ _).mpr listed, bind, Option.bind_some, if_pos admissible,
          (readFunctions_iff _ _ _ _ _).mpr functions]

end Mettapedia.Languages.C11.CestaFixedCore
