import Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Typing

open Mettapedia.OSLF.Framework

/-!
# Declaration-derived admission of classifying source carriers

The finite typed catalogue classifies programs at root constructor results
and explicitly declared source variables. Arbitrary bare abstraction roots
may have infinitely many arrow carriers; they are not silently interpreted
as a complete empty catalogue. This executable admission exposes that
boundary and derives carrier coverage from the authored declarations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.SourceCarriers

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation.Occurrences

/-- Constructor results are finite classifying carriers only when their
actual authored result names are declared in the language's type signature.
A source variable instead reads its exact declared type expression. -/
def classifyingSource? (language : LanguageDef) (rule : RewriteRule) : Bool :=
  match rule.left with
  | .apply label _ =>
      (language.terms.filter fun constructor => constructor.label == label).all fun constructor =>
        language.types.any fun type => type.name == constructor.category
  | .fvar name => (ruleFree rule name).isSome
  | _ => false

inductive CarrierStatus where
  | unclassifiedSource
  | unsupportedRepresentation
  | illSortedSource
  | classified (carriers : List TypeExpr)
  deriving DecidableEq, Repr

def typedCarriers (language : LanguageDef) (rule : RewriteRule) : List TypeExpr :=
  (sourceCandidates language rule).filter fun carrier =>
    checkHasType language (ruleFree rule) [] rule.left carrier

/-- Unsupported source classification and a checked ill-sorted source are
distinct outcomes. Neither is a certified empty typed source family. -/
def carrierStatus (language : LanguageDef) (rule : RewriteRule) : CarrierStatus :=
  if classifyingSource? language rule then
    if isObjectPattern rule.left then
      let carriers := typedCarriers language rule
      if carriers.isEmpty then .illSortedSource else .classified carriers
    else .unsupportedRepresentation
  else .unclassifiedSource

private theorem variable_type_declared {rule : RewriteRule} {name : String} {carrier : TypeExpr}
    (typed : ruleFree rule name = some carrier) : carrier ∈ rule.typeContext.map Prod.snd := by
  unfold ruleFree at typed
  cases found : rule.typeContext.find? (fun entry => entry.1 == name) with
  | none => simp [found] at typed
  | some entry =>
      simp only [found, Option.map_some, Option.some.injEq] at typed
      exact List.mem_map.mpr ⟨entry, List.mem_of_find?_eq_some found, typed⟩

/-- Carrier membership is a theorem of the classifying root and its typing
derivation; callers do not supply a finite candidate-membership oracle. -/
theorem classified_type_candidate {language : LanguageDef} {rule : RewriteRule} {carrier : TypeExpr}
    (classified : classifyingSource? language rule = true)
    (typed : HasType language (ruleFree rule) [] rule.left carrier) :
    carrier ∈ sourceCandidates language rule := by
  cases left : rule.left with
  | fvar name =>
      rw [left] at typed
      cases typed with
      | fvar declared =>
          have member := variable_type_declared declared
          simp only [sourceCandidates, List.mem_eraseDups, List.mem_append]
          exact Or.inl (Or.inr member)
  | apply label arguments =>
      rw [left] at typed
      cases typed with
      | constructor declared ordinary argumentsTyped =>
          rename_i constructor
          have selected : constructor ∈ language.terms.filter
              (fun declaration => declaration.label == constructor.label) := by
            simp [declared]
          have classifications :
              (language.terms.filter fun declaration => declaration.label == constructor.label).all
                (fun declaration => language.types.any fun type => type.name == declaration.category) = true := by
            simpa only [classifyingSource?, left] using classified
          have resultDeclared := List.all_eq_true.mp classifications constructor selected
          obtain ⟨type, membership, same⟩ := List.any_eq_true.mp resultDeclared
          have actual : TypeExpr.base constructor.category ∈
              language.types.map (fun type => TypeExpr.base type.name) := by
            exact List.mem_map.mpr ⟨type, membership, congrArg TypeExpr.base (beq_iff_eq.mp same)⟩
          simp only [sourceCandidates, List.mem_eraseDups, List.mem_append]
          exact Or.inl (Or.inl actual)
  | bvar index => simp [classifyingSource?, left] at classified
  | lambda binder body => simp [classifyingSource?, left] at classified
  | multiLambda arity binders body => simp [classifyingSource?, left] at classified
  | subst body replacement => simp [classifyingSource?, left] at classified
  | collection kind elements rest => simp [classifyingSource?, left] at classified

theorem typed_carriers_sound {language : LanguageDef} {rule : RewriteRule} {carrier : TypeExpr}
    (member : carrier ∈ typedCarriers language rule) :
    HasType language (ruleFree rule) [] rule.left carrier :=
  checkHasType_sound (List.mem_filter.mp member).2

theorem typed_carriers_complete {language : LanguageDef} {rule : RewriteRule} {carrier : TypeExpr}
    (classified : classifyingSource? language rule = true)
    (typed : HasType language (ruleFree rule) [] rule.left carrier)
    (object : isObjectPattern rule.left = true) :
    carrier ∈ typedCarriers language rule :=
  List.mem_filter.mpr ⟨classified_type_candidate classified typed,
    checkHasType_complete_of_object typed object⟩

theorem carrier_status_complete {language : LanguageDef} {rule : RewriteRule} {carrier : TypeExpr}
    (classified : classifyingSource? language rule = true)
    (typed : HasType language (ruleFree rule) [] rule.left carrier)
    (object : isObjectPattern rule.left = true) :
    carrierStatus language rule = .classified (typedCarriers language rule) ∧
      carrier ∈ typedCarriers language rule := by
  have member := typed_carriers_complete classified typed object
  have nonempty : (typedCarriers language rule).isEmpty = false := by
    cases present : typedCarriers language rule with
    | nil => rw [present] at member; exact False.elim (List.not_mem_nil member)
    | cons first rest => rfl
  exact ⟨by simp [carrierStatus, classified, object, nonempty], member⟩

theorem carrier_status_sound {language : LanguageDef} {rule : RewriteRule} {carriers : List TypeExpr}
    (accepted : carrierStatus language rule = .classified carriers) :
    classifyingSource? language rule = true ∧ carriers ≠ [] ∧
      ∀ carrier ∈ carriers, HasType language (ruleFree rule) [] rule.left carrier := by
  unfold carrierStatus at accepted
  split at accepted
  · rename_i classified
    split at accepted
    · dsimp only at accepted
      split at accepted
      · contradiction
      · rename_i populated
        cases accepted
        refine ⟨classified, ?_, fun _ member => typed_carriers_sound member⟩
        intro empty
        rw [empty] at populated
        contradiction
    · contradiction
  · contradiction

theorem carrier_status_representation {language : LanguageDef} {rule : RewriteRule}
    {carriers : List TypeExpr}
    (accepted : carrierStatus language rule = .classified carriers) :
    isObjectPattern rule.left = true := by
  unfold carrierStatus at accepted
  split at accepted
  · split at accepted
    · assumption
    · contradiction
  · contradiction

end Mettapedia.OSLF.NativeTypes.Modal.SourceCarriers
