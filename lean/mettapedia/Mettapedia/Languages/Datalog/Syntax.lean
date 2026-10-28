import Mathlib.Data.List.Basic

/-! Canonical data for the positive, function-free Souffle core. Source
locations are separate from statement order and clause-local variable names.
Floating literals retain their IEEE word; comparison is a distinct policy. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog

inductive AttributeType where
  | symbol | number | unsigned | floating
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

inductive Value where
  | symbol (contents : String)
  | number (value : Int)
  | unsigned (value : Nat)
  | floating (word : UInt64)
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

def Value.type : Value → AttributeType
  | .symbol _ => .symbol
  | .number _ => .number
  | .unsigned _ => .unsigned
  | .floating _ => .floating

/-- Representation bounds of the pinned 64-bit domain; this is separate
from source-literal parsing and from numeric comparison. -/
def Value.fits64 : Value → Bool
  | .number value => decide (-(2 ^ 63 : Int) ≤ value ∧ value < 2 ^ 63)
  | .unsigned value => decide (value < 2 ^ 64)
  | _ => true

abbrev QualifiedName := List String
abbrev Assignment := String → Option Value

inductive Argument where
  | literal (value : Value)
  | var (name : String)
  | anonymous
  deriving Repr, DecidableEq, BEq

def Argument.vars : Argument → List String
  | .var name => [name]
  | _ => []

def Argument.isAnonymous : Argument → Bool
  | .anonymous => true
  | _ => false

@[simp] theorem Argument.not_anonymous_iff (argument : Argument) :
    argument.isAnonymous = false ↔ argument ≠ .anonymous := by
  cases argument <;> simp [isAnonymous]

def Argument.Matches (assignment : Assignment) : Argument → Value → Prop
  | .literal expected, actual => expected = actual
  | .var name, actual => assignment name = some actual
  | .anonymous, _ => True

structure Atom where
  relation : QualifiedName
  arguments : List Argument
  deriving Repr, DecidableEq, BEq

def Atom.variables (atom : Atom) : List String := atom.arguments.flatMap Argument.vars

structure GroundFact where
  relation : QualifiedName
  values : List Value
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

def Atom.Matches (assignment : Assignment) (schema : Atom) (fact : GroundFact) : Prop :=
  schema.relation = fact.relation ∧ List.Forall₂ (Argument.Matches assignment) schema.arguments fact.values

inductive ComparisonOperator where
  | equal | different | less | lessEqual | greater | greaterEqual
  deriving Repr, DecidableEq, BEq

structure Comparison where
  operator : ComparisonOperator
  left : Argument
  right : Argument
  deriving Repr, DecidableEq, BEq

def Comparison.arguments (comparison : Comparison) : List Argument := [comparison.left,comparison.right]

inductive Premise where
  | atom (value : Atom)
  | comparison (value : Comparison)
  deriving Repr, DecidableEq, BEq

structure Clause where
  head : Atom
  body : List Premise
  deriving Repr, DecidableEq, BEq

def Clause.positiveAtoms (clause : Clause) : List Atom :=
  clause.body.filterMap fun premise => match premise with
    | .atom atom => some atom
    | _ => none

def Clause.requiredArguments (clause : Clause) : List Argument :=
  clause.head.arguments ++ clause.body.flatMap fun premise => match premise with
    | .comparison comparison => comparison.arguments
    | _ => []

def Clause.requiredVariables (clause : Clause) : List String :=
  clause.requiredArguments.flatMap Argument.vars

def Clause.providedVariables (clause : Clause) : List String :=
  clause.positiveAtoms.flatMap Atom.variables

structure Attribute where
  name : String
  type : AttributeType
  deriving Repr, DecidableEq, BEq

structure RelationDeclaration where
  name : QualifiedName
  attributes : List Attribute
  deriving Repr, DecidableEq, BEq

inductive Statement where
  | declaration (value : RelationDeclaration)
  | fact (value : GroundFact)
  | rule (value : Clause)
  | input (relation : QualifiedName)
  | output (relation : QualifiedName)
  deriving Repr, DecidableEq, BEq

structure Program where
  statements : List Statement
  deriving Repr, DecidableEq, BEq

/-- A finite one-step explanation identity. Validation replays and numeric
comparison evidence are not new keys; unfolded proof trees are separate. -/
structure DerivationKey where
  statementIndex : Nat
  grounding : List (String × Value)
  positivePremises : List GroundFact
  deriving Repr, DecidableEq, BEq

end Mettapedia.Languages.Datalog
