import Mettapedia.Languages.Datalog.Syntax
import Mettapedia.OSLF.MeTTaIL.Syntax
import Std.Data.String.ToNat
import Std.Data.String.ToInt

/-! Compact program data for the independent Datalog module. Primitive values
occupy atomic carrier leaves; names are identifier vectors. Numeric words are
canonical and preserve IEEE bits. Width admission remains `Value.fits64`.
The codec contains no source lexer, grammar, layout or character-tree encoding. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.Datalog.IRCodec

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)

def atom (text : String) : Pattern := .apply text []
def atom? : Pattern → Option String
  | .apply text [] => some text
  | _ => none

def vector {α : Type} (encode : α → Pattern) (values : List α) : Pattern :=
  .collection .vec (values.map encode) none

def vector? {α : Type} (decode : Pattern → Option α) : Pattern → Option (List α)
  | .collection .vec values none => values.mapM decode
  | _ => none

@[simp] theorem atom_roundtrip (text : String) : atom? (atom text) = some text := rfl

@[simp] theorem vector_roundtrip {α : Type} (encode : α → Pattern) (decode : Pattern → Option α)
    (exact : ∀ value, decode (encode value) = some value) (values : List α) :
    vector? decode (vector encode values) = some values := by
  simp only [vector,vector?]
  induction values with
  | nil => rfl
  | cons value values ih => simp [exact,ih]

def integer? (text : String) : Option Int := do
  let value ← text.toInt?
  if value.repr == text then some value else none

def natural? (text : String) : Option Nat := do
  let value ← text.toNat?
  if value.repr == text then some value else none

@[simp] theorem integer_roundtrip (value : Int) : integer? value.repr = some value := by simp [integer?]
@[simp] theorem natural_roundtrip (value : Nat) : natural? value.repr = some value := by simp [natural?]

def value : Value → Pattern
  | .symbol text => .apply "SymbolValue" [atom text]
  | .number number => .apply "IntegerValue" [atom number.repr]
  | .unsigned number => .apply "UnsignedValue" [atom number.repr]
  | .floating word => .apply "FloatValue" [atom word.toNat.repr]

def value? : Pattern → Option Value
  | .apply "SymbolValue" [payload] => Value.symbol <$> atom? payload
  | .apply "IntegerValue" [payload] => do return .number (← integer? (← atom? payload))
  | .apply "UnsignedValue" [payload] => do return .unsigned (← natural? (← atom? payload))
  | .apply "FloatValue" [payload] => do
    let word ← natural? (← atom? payload)
    if word < 2 ^ 64 then some (.floating (UInt64.ofNat word)) else none
  | _ => none

@[simp] theorem value_roundtrip (input : Value) : value? (value input) = some input := by
  cases input with
  | symbol text => simp [value,value?]
  | number number => simp [value,value?]
  | unsigned number => simp [value,value?]
  | floating word =>
    have bound : word.toNat < 18446744073709551616 := word.toNat_lt_size
    simp [value,value?,bound]

def qualifiedName (parts : QualifiedName) : Pattern := .apply "QualifiedName" [vector atom parts]
def qualifiedName? : Pattern → Option QualifiedName
  | .apply "QualifiedName" [parts] => vector? atom? parts
  | _ => none

@[simp] theorem qualifiedName_roundtrip (name : QualifiedName) : qualifiedName? (qualifiedName name) = some name := by
  simp only [qualifiedName,qualifiedName?]
  exact vector_roundtrip atom atom? atom_roundtrip name

def relation (name : QualifiedName) : Pattern := .apply "Relation" [qualifiedName name]
def relation? : Pattern → Option QualifiedName
  | .apply "Relation" [name] => qualifiedName? name
  | _ => none

@[simp] theorem relation_roundtrip (name : QualifiedName) : relation? (relation name) = some name := by
  simp [relation,relation?]

def argument : Argument → Pattern
  | .literal input => .apply "ValueArgument" [value input]
  | .var name => .apply "VariableArgument" [.apply "Variable" [atom name]]
  | .anonymous => .apply "AnonymousArgument" []

def argument? : Pattern → Option Argument
  | .apply "ValueArgument" [input] => Argument.literal <$> value? input
  | .apply "VariableArgument" [.apply "Variable" [name]] => Argument.var <$> atom? name
  | .apply "AnonymousArgument" [] => some .anonymous
  | _ => none

@[simp] theorem argument_roundtrip (input : Argument) : argument? (argument input) = some input := by
  cases input <;> simp [argument,argument?]

def tuple (arguments : List Argument) : Pattern := .apply "Tuple" [vector argument arguments]
def tuple? : Pattern → Option (List Argument)
  | .apply "Tuple" [arguments] => vector? argument? arguments
  | _ => none

@[simp] theorem tuple_roundtrip (arguments : List Argument) : tuple? (tuple arguments) = some arguments := by
  simp [tuple,tuple?]

def groundTuple (values : List Value) : Pattern := .apply "GroundTuple" [vector value values]
def groundTuple? : Pattern → Option (List Value)
  | .apply "GroundTuple" [values] => vector? value? values
  | _ => none

@[simp] theorem groundTuple_roundtrip (values : List Value) : groundTuple? (groundTuple values) = some values := by
  simp [groundTuple,groundTuple?]

def positiveAtom (input : Atom) : Pattern := .apply "PositiveAtom" [relation input.relation,tuple input.arguments]
def positiveAtom? : Pattern → Option Atom
  | .apply "PositiveAtom" [name,arguments] => do return ⟨← relation? name,← tuple? arguments⟩
  | _ => none

@[simp] theorem positiveAtom_roundtrip (input : Atom) : positiveAtom? (positiveAtom input) = some input := by
  cases input
  simp [positiveAtom,positiveAtom?]

def groundFact (input : GroundFact) : Pattern := .apply "GroundFact" [relation input.relation,groundTuple input.values]
def groundFact? : Pattern → Option GroundFact
  | .apply "GroundFact" [name,values] => do return ⟨← relation? name,← groundTuple? values⟩
  | _ => none

@[simp] theorem groundFact_roundtrip (input : GroundFact) : groundFact? (groundFact input) = some input := by
  cases input
  simp [groundFact,groundFact?]

def operator : ComparisonOperator → String
  | .equal => "Equal"
  | .different => "Different"
  | .less => "Less"
  | .lessEqual => "LessEqual"
  | .greater => "Greater"
  | .greaterEqual => "GreaterEqual"
def operator? : String → Option ComparisonOperator
  | "Equal" => some .equal
  | "Different" => some .different
  | "Less" => some .less
  | "LessEqual" => some .lessEqual
  | "Greater" => some .greater
  | "GreaterEqual" => some .greaterEqual
  | _ => none

@[simp] theorem operator_roundtrip (input : ComparisonOperator) : operator? (operator input) = some input := by
  cases input <;> rfl

def comparison (input : Comparison) : Pattern := .apply (operator input.operator)
  [argument input.left,argument input.right]
def comparison? : Pattern → Option Comparison
  | .apply tag [left,right] => do return ⟨← operator? tag,← argument? left,← argument? right⟩
  | _ => none

@[simp] theorem comparison_roundtrip (input : Comparison) : comparison? (comparison input) = some input := by
  cases input
  simp [comparison,comparison?]

def premise : Premise → Pattern
  | .atom input => positiveAtom input
  | .comparison input => .apply "Comparison" [comparison input]
def premise? (input : Pattern) : Option Premise :=
  match input with
  | .apply "Comparison" [input] => Premise.comparison <$> comparison? input
  | _ => Premise.atom <$> positiveAtom? input

@[simp] theorem premise_roundtrip (input : Premise) : premise? (premise input) = some input := by
  cases input with
  | atom input => cases input; simp [premise,premise?,positiveAtom,positiveAtom?]
  | comparison input => simp [premise,premise?]

def clause (input : Clause) : Pattern := .apply "Clause"
  [relation input.head.relation,tuple input.head.arguments,vector premise input.body]
def clause? : Pattern → Option Clause
  | .apply "Clause" [name,arguments,body] => do
    return ⟨⟨← relation? name,← tuple? arguments⟩,← vector? premise? body⟩
  | _ => none

@[simp] theorem clause_roundtrip (input : Clause) : clause? (clause input) = some input := by
  rcases input with ⟨⟨_,_⟩,_⟩
  simp [clause,clause?]

def attributeType : AttributeType → Pattern
  | .symbol => .apply "SymbolType" []
  | .number => .apply "NumberType" []
  | .unsigned => .apply "UnsignedType" []
  | .floating => .apply "FloatType" []
def attributeType? : Pattern → Option AttributeType
  | .apply "SymbolType" [] => some .symbol
  | .apply "NumberType" [] => some .number
  | .apply "UnsignedType" [] => some .unsigned
  | .apply "FloatType" [] => some .floating
  | _ => none

@[simp] theorem attributeType_roundtrip (input : AttributeType) : attributeType? (attributeType input) = some input := by
  cases input <;> rfl

def attributeData (input : Attribute) : Pattern := .apply "Attribute" [atom input.name,attributeType input.type]
def attributeData? : Pattern → Option Attribute
  | .apply "Attribute" [name,type] => do return ⟨← atom? name,← attributeType? type⟩
  | _ => none

@[simp] theorem attribute_roundtrip (input : Attribute) : attributeData? (attributeData input) = some input := by
  cases input
  simp [attributeData,attributeData?]

def declaration (input : RelationDeclaration) : Pattern :=
  .apply "RelationDeclaration" [relation input.name,vector attributeData input.attributes]
def declaration? : Pattern → Option RelationDeclaration
  | .apply "RelationDeclaration" [name,attributes] => do return ⟨← relation? name,← vector? attributeData? attributes⟩
  | _ => none

@[simp] theorem declaration_roundtrip (input : RelationDeclaration) : declaration? (declaration input) = some input := by
  cases input
  simp [declaration,declaration?]

def statement : Statement → Pattern
  | .declaration input => .apply "Declaration" [declaration input]
  | .fact input => groundFact input
  | .rule input => .apply "PositiveRule" [clause input]
  | .input name => .apply "InputRelation" [relation name]
  | .output name => .apply "OutputRelation" [relation name]
def statement? : Pattern → Option Statement
  | .apply "Declaration" [input] => Statement.declaration <$> declaration? input
  | .apply "PositiveRule" [input] => Statement.rule <$> clause? input
  | .apply "InputRelation" [name] => Statement.input <$> relation? name
  | .apply "OutputRelation" [name] => Statement.output <$> relation? name
  | input => Statement.fact <$> groundFact? input

@[simp] theorem statement_roundtrip (input : Statement) : statement? (statement input) = some input := by
  cases input with
  | declaration input => simp [statement,statement?]
  | fact input => cases input; simp [statement,statement?,groundFact,groundFact?]
  | rule input => simp [statement,statement?]
  | input name => simp [statement,statement?]
  | output name => simp [statement,statement?]

def program (input : Program) : Pattern := .apply "Program" [vector statement input.statements]
def program? : Pattern → Option Program
  | .apply "Program" [statements] => Program.mk <$> vector? statement? statements
  | _ => none

@[simp] theorem program_roundtrip (input : Program) : program? (program input) = some input := by
  cases input
  simp [program,program?]

theorem program_injective : Function.Injective program := by
  intro first second equal
  exact Option.some.inj ((program_roundtrip first).symm.trans
    ((congrArg program? equal).trans (program_roundtrip second)))

#print axioms value_roundtrip
#print axioms program_roundtrip
#print axioms program_injective

end Mettapedia.Languages.Datalog.IRCodec
