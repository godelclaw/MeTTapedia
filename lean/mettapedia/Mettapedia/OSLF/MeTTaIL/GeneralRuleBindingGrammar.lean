import Mettapedia.OSLF.MeTTaIL.RuleBinding
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Grammar-derived contextual metavariable declarations

Omitted binding declarations are reconstructed from the authored grammar and
the exact occurrence addresses. Constructor parameters determine binder sorts;
explicit substitutions obtain their domain from the actual replacement; a
collection tail receives its collection type rather than its element type.
All occurrences of one metavariable must agree on both result and dependency
sorts. Missing or ambiguous grammar information remains unresolved.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

open Syntax RuleBinding
open Mettapedia.GSLT.LanguageDef.WellSorted

def unique? {α : Type} [DecidableEq α] (items : List α) : Option α :=
  match items.eraseDups with
  | [item] => some item
  | _ => none

def constructor? (language : LanguageDef) (label : String) : Option GrammarRule :=
  match language.terms.filter (fun declaration => declaration.label == label) with
  | [declaration] => some declaration
  | _ => none

def lookupType (context : List (String × TypeExpr)) (name : String) : Option TypeExpr :=
  unique? (context.filterMap fun entry => if entry.1 == name then some entry.2 else none)

def collectionElement? (language : LanguageDef) (kind : CollType)
    (expected : TypeExpr) : Option TypeExpr :=
  unique? ((match expected with
    | .collection actual element => if actual == kind then [element] else []
    | _ => []) ++ language.terms.filterMap fun declaration =>
      bareCollectionElementType? declaration kind expected)

/-- Infer only a uniquely determined grammar head. Binder nodes require their
expected arrow and are handled by the address traversal below. -/
def headType? (language : LanguageDef) (context : List (String × TypeExpr))
    (bound : List TypeExpr) : Pattern → Option TypeExpr
  | .fvar name => lookupType context name
  | .bvar index => bound[index]?
  | .apply label _ => (constructor? language label).map (fun declaration => .base declaration.category)
  | .collection kind _ _ => unique? (language.terms.filterMap fun declaration =>
      match bareCollectionElementType? declaration kind (.base declaration.category) with
      | some _ => some (.base declaration.category)
      | none => none)
  | .subst body replacement => do
      let domain ← headType? language context bound replacement
      headType? language context (domain :: bound) body
  | .lambda _ _ | .multiLambda _ _ _ => none

/-- Read the complete binder context and expected result sort at one actual
metavariable address. The terminal collection-tail address is distinguished
from an element address. -/
def contextAt? (language : LanguageDef) (context : List (String × TypeExpr))
    (bound : List TypeExpr) (expected : TypeExpr) (pattern : Pattern)
    (address : List Nat) : Option (List TypeExpr × TypeExpr) :=
  match pattern, address with
  | .fvar _, [] => some (bound, expected)
  | .apply label arguments, index :: rest => do
      let declaration ← constructor? language label
      guard (expected == .base declaration.category)
      guard (!usesBareCollection? declaration)
      let parameter ← declaration.params[index]?
      let argument ← arguments[index]?
      guard (matchesParameterRepresentation? parameter argument)
      let argumentType ← parameterType? parameter
      contextAt? language context bound argumentType argument rest
  | .lambda _ body, 0 :: rest =>
      match expected with
      | .arrow domain codomain => contextAt? language context (domain :: bound) codomain body rest
      | _ => none
  | .multiLambda arity _ body, 0 :: rest =>
      match expected with
      | .arrow (.multiBinder domain) codomain =>
          contextAt? language context (List.replicate arity domain ++ bound) codomain body rest
      | _ => none
  | .subst body replacement, 0 :: rest => do
      let domain ← headType? language context bound replacement
      contextAt? language context (domain :: bound) expected body rest
  | .subst _ replacement, 1 :: rest => do
      let domain ← headType? language context bound replacement
      contextAt? language context bound domain replacement rest
  | .collection kind elements tail, index :: rest => do
      let elementType ← collectionElement? language kind expected
      if index < elements.length then
        let element ← elements[index]?
        contextAt? language context bound elementType element rest
      else if index == elements.length && rest.isEmpty && tail.isSome then
        some (bound, .collection kind elementType)
      else none
  | _, _ => none
termination_by address.length

structure Address where
  name : String
  site : RulePatternSite
  path : List Nat
  deriving DecidableEq, Repr

mutual
  def addresses (site : RulePatternSite) (path : List Nat) : Pattern → List Address
    | .fvar name => [⟨name, site, path⟩]
    | .bvar _ => []
    | .apply _ arguments => argumentAddresses site path 0 arguments
    | .lambda _ body | .multiLambda _ _ body => addresses site (path ++ [0]) body
    | .subst body replacement => addresses site (path ++ [0]) body ++
        addresses site (path ++ [1]) replacement
    | .collection _ elements tail => argumentAddresses site path 0 elements ++
        (tail.toList.map fun name => ⟨name, site, path ++ [elements.length]⟩)
  termination_by pattern => sizeOf pattern

  def argumentAddresses (site : RulePatternSite) (path : List Nat) (index : Nat) :
      List Pattern → List Address
    | [] => []
    | pattern :: patterns => addresses site (path ++ [index]) pattern ++
        argumentAddresses site path (index + 1) patterns
  termination_by patterns => sizeOf patterns
end

structure Occurrence extends Address where
  bound : List TypeExpr
  result : TypeExpr
  deriving DecidableEq, Repr

def inspect (language : LanguageDef) (context : List (String × TypeExpr))
    (site : RulePatternSite) (bound : List TypeExpr) (expected : TypeExpr)
    (pattern : Pattern) : Option (List Occurrence) :=
  (addresses site [] pattern).mapM fun address => do
    let (localBound, result) ← contextAt? language context bound expected pattern address.path
    return {address with bound := localBound, result := result}

def implicitTypes (rule : RewriteRule) (occurrences : List Occurrence) :
    List (String × TypeExpr) :=
  (occurrences.map fun row => (row.name, row.result)).eraseDups.filter fun row =>
    !(rule.typeContext.any fun entry => entry.1 == row.1)

def consistent (context : List (String × TypeExpr)) (occurrences : List Occurrence) : Bool :=
  occurrences.all (fun row => lookupType context row.name == some row.result) &&
    occurrences.all (fun row => occurrences.all fun other =>
      row.name != other.name || row.bound == other.bound)

def dependencyRows (context : List (String × TypeExpr)) (occurrences : List Occurrence) :
    List (String × List TypeExpr) :=
  context.map fun entry =>
    (entry.1, (occurrences.find? fun row => row.name == entry.1).map Occurrence.bound |>.getD [])

def specification (context : List (String × TypeExpr)) (occurrences : List Occurrence) :
    RuleBindingSpec where
  dependencies := dependencyRows context occurrences
  occurrences := occurrences.map fun row =>
    ⟨row.name, row.site, row.path, (List.range row.bound.length).map Pattern.bvar⟩

def premiseOccurrences (language : LanguageDef) (context : List (String × TypeExpr))
    (index quantifiers : Nat) : Premise → Option (List Occurrence)
  | .freshness condition => do
      let expected ← headType? language context [] condition.term
      inspect language context (.premise index quantifiers 0) [] expected condition.term
  | .congruence source target => do
      let expected ← headType? language context [] source
      let sourceRows ← inspect language context (.premise index quantifiers 0) [] expected source
      let targetRows ← inspect language context (.premise index quantifiers 1) [] expected target
      return sourceRows ++ targetRows
  | .scopedStep step => do
      let sourceRows ← inspect language context (.premise index quantifiers 0)
        step.binders step.resultType step.source
      let targetRows ← inspect language context (.premise index quantifiers 1)
        step.binders step.resultType step.target
      return sourceRows ++ targetRows
  | .relationQuery _ arguments => do
      let rows ← (arguments.zipIdx).mapM fun (argument, position) => do
        let expected ← headType? language context [] argument
        inspect language context (.premise index quantifiers position) [] expected argument
      return rows.flatten
  | .forAll _ _ body => premiseOccurrences language context index (quantifiers + 1) body

structure Inference where
  extraTypes : List (String × TypeExpr)
  spec : RuleBindingSpec
  occurrences : List Occurrence
  deriving DecidableEq, Repr

def elaborate (rule : RewriteRule) (inference : Inference) : RewriteRule :=
  {rule with
    typeContext := rule.typeContext ++ inference.extraTypes
    bindings := some inference.spec}

def infer? (language : LanguageDef) (rule : RewriteRule) : Option Inference := do
  let expected ← headType? language rule.typeContext [] rule.left
  let leftRows ← inspect language rule.typeContext .left [] expected rule.left
  let rightRows ← inspect language rule.typeContext .right [] expected rule.right
  let sides := leftRows ++ rightRows
  let sideContext := rule.typeContext ++ implicitTypes rule sides
  let premises ← rule.premises.zipIdx.mapM fun (premise, index) =>
    premiseOccurrences language sideContext index 0 premise
  let occurrences := sides ++ premises.flatten
  let extra := implicitTypes rule occurrences
  let context := rule.typeContext ++ extra
  let result : Inference := ⟨extra, specification context occurrences, occurrences⟩
  if consistent context occurrences && admittedFor (elaborate rule result) result.spec &&
      dependencySortsDeclared language result.spec then some result else none

theorem elaborate_source (rule : RewriteRule) (inference : Inference) :
    (elaborate rule inference).name = rule.name ∧
      (elaborate rule inference).left = rule.left ∧
      (elaborate rule inference).right = rule.right ∧
      (elaborate rule inference).premises = rule.premises := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem infer_admitted {language : LanguageDef} {rule : RewriteRule} {result : Inference}
    (inferred : infer? language rule = some result) :
    admittedFor (elaborate rule result) result.spec = true ∧
      dependencySortsDeclared language result.spec = true := by
  simp only [infer?, Option.bind_eq_bind, Option.bind_eq_some_iff] at inferred
  obtain ⟨expected, _, left, _, right, _, premises, _, inferred⟩ := inferred
  split at inferred
  next accepted =>
    cases Option.some.inj inferred
    exact ⟨(Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted).1).2,
      (Bool.and_eq_true_iff.mp accepted).2⟩
  next => contradiction

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar
