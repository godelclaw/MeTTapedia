import Mettapedia.Languages.Datalog.RangeRestriction
import Mathlib.Data.List.Forall2

/-! Source typing for the finite primitive domain. Relation declarations and
clause-local variable types are explicit inputs. The checker distinguishes
an undeclared relation or variable from a refuted comparison; it performs no
evaluation and makes no choice of numeric comparison interpretation. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.StaticTyping

abbrev Signature := QualifiedName → Option (List AttributeType)
abbrev VariableTypes := String → Option AttributeType

def ValueTyped (value : Value) (type : AttributeType) : Prop :=
  value.type = type ∧ value.fits64 = true

def ArgumentTyped (context : VariableTypes) : Argument → AttributeType → Prop
  | .literal value, type => ValueTyped value type
  | .var identifier, type => context identifier = some type
  | .anonymous, _ => True

def checkArgument (context : VariableTypes) : Argument → AttributeType → Bool
  | .literal value, type => decide (value.type = type) && value.fits64
  | .var identifier, type => decide (context identifier = some type)
  | .anonymous, _ => true

theorem checkArgument_iff (context : VariableTypes) (argument : Argument) (type : AttributeType) :
    checkArgument context argument type = true ↔ ArgumentTyped context argument type := by
  cases argument <;> simp [checkArgument, ArgumentTyped, ValueTyped]

def checkArguments (context : VariableTypes) : List Argument → List AttributeType → Bool
  | [], [] => true
  | argument :: arguments, type :: types =>
      checkArgument context argument type && checkArguments context arguments types
  | _, _ => false

theorem checkArguments_iff (context : VariableTypes) (arguments : List Argument)
    (types : List AttributeType) :
    checkArguments context arguments types = true ↔
      List.Forall₂ (ArgumentTyped context) arguments types := by
  induction arguments generalizing types with
  | nil => cases types <;> simp [checkArguments]
  | cons argument arguments ih =>
    cases types with
    | nil => simp [checkArguments]
    | cons type types => simp [checkArguments, checkArgument_iff, ih]

def AtomTyped (signature : Signature) (context : VariableTypes) (atom : Atom) : Prop :=
  ∃ types, signature atom.relation = some types ∧
    List.Forall₂ (ArgumentTyped context) atom.arguments types

def checkAtom (signature : Signature) (context : VariableTypes) (atom : Atom) : Bool :=
  match signature atom.relation with
  | none => false
  | some types => checkArguments context atom.arguments types

theorem checkAtom_iff (signature : Signature) (context : VariableTypes) (atom : Atom) :
    checkAtom signature context atom = true ↔ AtomTyped signature context atom := by
  cases found : signature atom.relation <;>
    simp [checkAtom, AtomTyped, found, checkArguments_iff]

def operandType? (context : VariableTypes) : Argument → Option AttributeType
  | .literal value => if value.fits64 then some value.type else none
  | .var identifier => context identifier
  | .anonymous => none

theorem operandType?_iff (context : VariableTypes) (argument : Argument) (type : AttributeType) :
    operandType? context argument = some type ↔
      argument ≠ .anonymous ∧ ArgumentTyped context argument type := by
  cases argument with
  | literal value =>
    by_cases fits : value.fits64 = true <;>
      simp [operandType?, ArgumentTyped, ValueTyped, fits, eq_comm]
  | var identifier => simp [operandType?, ArgumentTyped]
  | anonymous => simp [operandType?]

def ComparisonTyped (context : VariableTypes) (comparison : Comparison) : Prop :=
  comparison.left ≠ .anonymous ∧ comparison.right ≠ .anonymous ∧
    ∃ type, ArgumentTyped context comparison.left type ∧
      ArgumentTyped context comparison.right type

def checkComparison (context : VariableTypes) (comparison : Comparison) : Bool :=
  match operandType? context comparison.left, operandType? context comparison.right with
  | some first, some second => decide (first = second)
  | _, _ => false

theorem checkComparison_iff (context : VariableTypes) (comparison : Comparison) :
    checkComparison context comparison = true ↔ ComparisonTyped context comparison := by
  constructor
  · intro checked
    cases first : operandType? context comparison.left with
    | none => simp [checkComparison, first] at checked
    | some firstType =>
      cases second : operandType? context comparison.right with
      | none => simp [checkComparison, first, second] at checked
      | some secondType =>
        have same : firstType = secondType := by
          simpa [checkComparison, first, second] using checked
        subst secondType
        obtain ⟨leftNamed, leftTyped⟩ := (operandType?_iff _ _ _).mp first
        obtain ⟨rightNamed, rightTyped⟩ := (operandType?_iff _ _ _).mp second
        exact ⟨leftNamed, rightNamed, firstType, leftTyped, rightTyped⟩
  · rintro ⟨leftNamed, rightNamed, type, leftTyped, rightTyped⟩
    have first := (operandType?_iff _ _ _).mpr ⟨leftNamed, leftTyped⟩
    have second := (operandType?_iff _ _ _).mpr ⟨rightNamed, rightTyped⟩
    simp [checkComparison, first, second]

def PremiseTyped (signature : Signature) (context : VariableTypes) : Premise → Prop
  | .atom atom => AtomTyped signature context atom
  | .comparison comparison => ComparisonTyped context comparison

def checkPremise (signature : Signature) (context : VariableTypes) : Premise → Bool
  | .atom atom => checkAtom signature context atom
  | .comparison comparison => checkComparison context comparison

theorem checkPremise_iff (signature : Signature) (context : VariableTypes) (premise : Premise) :
    checkPremise signature context premise = true ↔ PremiseTyped signature context premise := by
  cases premise <;> simp [checkPremise, PremiseTyped, checkAtom_iff, checkComparison_iff]

def ClauseTyped (signature : Signature) (context : VariableTypes) (clause : Clause) : Prop :=
  clause.RangeRestricted ∧ AtomTyped signature context clause.head ∧
    ∀ premise ∈ clause.body, PremiseTyped signature context premise

def checkClause (signature : Signature) (context : VariableTypes) (clause : Clause) : Bool :=
  clause.checkRangeRestriction && checkAtom signature context clause.head &&
    clause.body.all (checkPremise signature context)

theorem checkClause_iff (signature : Signature) (context : VariableTypes) (clause : Clause) :
    checkClause signature context clause = true ↔ ClauseTyped signature context clause := by
  simp [checkClause, ClauseTyped, Clause.checkRangeRestriction_iff,
    checkAtom_iff, List.all_eq_true, checkPremise_iff, and_assoc]

def FactTyped (signature : Signature) (fact : GroundFact) : Prop :=
  ∃ types, signature fact.relation = some types ∧ List.Forall₂ ValueTyped fact.values types

def checkValues : List Value → List AttributeType → Bool
  | [], [] => true
  | value :: values, type :: types =>
      (decide (value.type = type) && value.fits64) && checkValues values types
  | _, _ => false

theorem checkValues_iff (values : List Value) (types : List AttributeType) :
    checkValues values types = true ↔ List.Forall₂ ValueTyped values types := by
  induction values generalizing types with
  | nil => cases types <;> simp [checkValues]
  | cons value values ih =>
    cases types with
    | nil => simp [checkValues]
    | cons type types => simp [checkValues, ValueTyped, ih, and_assoc]

def checkFact (signature : Signature) (fact : GroundFact) : Bool :=
  match signature fact.relation with
  | none => false
  | some types => checkValues fact.values types

theorem checkFact_iff (signature : Signature) (fact : GroundFact) :
    checkFact signature fact = true ↔ FactTyped signature fact := by
  cases found : signature fact.relation <;> simp [checkFact, FactTyped, found, checkValues_iff]

def AssignmentTyped (context : VariableTypes) (model : Assignment) : Prop :=
  ∀ identifier value type, model identifier = some value → context identifier = some type →
    ValueTyped value type

theorem matched_argument_typed (context : VariableTypes) (model : Assignment)
    (modelTyped : AssignmentTyped context model) {argument : Argument} {type : AttributeType}
    {value : Value} (named : argument ≠ .anonymous) (typed : ArgumentTyped context argument type)
    (matched : argument.Matches model value) : ValueTyped value type := by
  cases argument with
  | literal literal => exact matched ▸ typed
  | var identifier => exact modelTyped identifier value type matched typed
  | anonymous => exact False.elim (named rfl)

theorem matched_arguments_typed (context : VariableTypes) (model : Assignment)
    (modelTyped : AssignmentTyped context model) {arguments : List Argument} {types : List AttributeType}
    {values : List Value} (named : ∀ argument ∈ arguments, argument ≠ .anonymous)
    (typed : List.Forall₂ (ArgumentTyped context) arguments types)
    (matched : List.Forall₂ (Argument.Matches model) arguments values) :
    List.Forall₂ ValueTyped values types := by
  induction typed generalizing values with
  | nil => cases matched; exact .nil
  | @cons argument type arguments types first _ ih =>
    cases matched with
    | cons firstMatch later =>
      exact .cons (matched_argument_typed context model modelTyped
        (named argument List.mem_cons_self) first firstMatch)
        (ih (fun other inside => named other (List.mem_cons_of_mem _ inside)) later)

/-- A typed source clause cannot instantiate its head with values of a
different primitive type or outside the declared machine domain. -/
theorem matched_head_typed (signature : Signature) (context : VariableTypes) (clause : Clause)
    (typed : ClauseTyped signature context clause) (model : Assignment)
    (modelTyped : AssignmentTyped context model) (conclusion : GroundFact)
    (matched : clause.head.Matches model conclusion) : FactTyped signature conclusion := by
  obtain ⟨types, declared, headTyped⟩ := typed.2.1
  refine ⟨types, matched.1 ▸ declared, ?_⟩
  exact matched_arguments_typed context model modelTyped
    (fun argument inside => typed.1.1 argument (List.mem_append_left _ inside)) headTyped matched.2

#print axioms checkClause_iff
#print axioms checkFact_iff
#print axioms matched_head_typed

end Mettapedia.Languages.Datalog.StaticTyping
