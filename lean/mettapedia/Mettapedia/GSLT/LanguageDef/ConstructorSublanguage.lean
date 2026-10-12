import Mettapedia.GSLT.LanguageDef.ConstructorSupport

/-!
# Typing in a sublanguage

A language whose constructor declarations are some of the declarations of
another language is a sublanguage of it. A pattern is typed in the
sublanguage exactly when it has a typing derivation in the whole language
that uses only the kept declarations.

Both directions are stated for a pair of declaration tables and a predicate
on labels, so no particular way of selecting declarations is built in. The
derivation, and not the raw pattern, is what is compared: a bare collection
constructor leaves no label in the pattern it types.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace WellSorted

mutual
  /-- A derivation that uses only allowed declarations is a derivation in
  every language that has those declarations. -/
  theorem HasTypeWithConstructors.toSublanguage
      {language sublanguage : LanguageDef} {allowed : String → Prop}
      {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (kept : ∀ rule ∈ language.terms, allowed rule.label → rule ∈ sublanguage.terms)
      (typed : HasTypeWithConstructors language allowed free bound pattern type) :
      HasType sublanguage free bound pattern type := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | constructor isAllowed membership notBare arguments =>
        exact .constructor (kept _ membership isAllowed) notBare (arguments.toSublanguage kept)
    | lambda body => exact .lambda (body.toSublanguage kept)
    | multiLambda body => exact .multiLambda (body.toSublanguage kept)
    | subst body replacement =>
        exact .subst (body.toSublanguage kept) (replacement.toSublanguage kept)
    | collection elements => exact .collection (elements.toSublanguage kept)
    | collectionConstructor isAllowed membership shape elements =>
        exact .collectionConstructor (kept _ membership isAllowed) shape
          (elements.toSublanguage kept)

  theorem ArgumentsHaveTypesWithConstructors.toSublanguage
      {language sublanguage : LanguageDef} {allowed : String → Prop}
      {free : FreeTypeContext} {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (kept : ∀ rule ∈ language.terms, allowed rule.label → rule ∈ sublanguage.terms)
      (typed : ArgumentsHaveTypesWithConstructors language allowed free bound arguments
        parameters) :
      ArgumentsHaveTypes sublanguage free bound arguments parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation parameterType argument arguments =>
        exact .cons representation parameterType (argument.toSublanguage kept)
          (arguments.toSublanguage kept)

  theorem ElementsHaveTypeWithConstructors.toSublanguage
      {language sublanguage : LanguageDef} {allowed : String → Prop}
      {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (kept : ∀ rule ∈ language.terms, allowed rule.label → rule ∈ sublanguage.terms)
      (typed : ElementsHaveTypeWithConstructors language allowed free bound elements
        elementType) :
      ElementsHaveType sublanguage free bound elements elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons element elements =>
        exact .cons (element.toSublanguage kept) (elements.toSublanguage kept)
end

mutual
  /-- A derivation in a language all of whose declarations are allowed
  declarations of another language is a derivation there that uses only
  allowed declarations. -/
  theorem HasType.ofSublanguage
      {language sublanguage : LanguageDef} {allowed : String → Prop}
      {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (selected : ∀ rule ∈ sublanguage.terms, rule ∈ language.terms ∧ allowed rule.label)
      (typed : HasType sublanguage free bound pattern type) :
      HasTypeWithConstructors language allowed free bound pattern type := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | constructor membership notBare arguments =>
        exact .constructor (selected _ membership).2 (selected _ membership).1 notBare
          (arguments.ofSublanguage selected)
    | lambda body => exact .lambda (body.ofSublanguage selected)
    | multiLambda body => exact .multiLambda (body.ofSublanguage selected)
    | subst body replacement =>
        exact .subst (body.ofSublanguage selected) (replacement.ofSublanguage selected)
    | collection elements => exact .collection (elements.ofSublanguage selected)
    | collectionConstructor membership shape elements =>
        exact .collectionConstructor (selected _ membership).2 (selected _ membership).1 shape
          (elements.ofSublanguage selected)

  theorem ArgumentsHaveTypes.ofSublanguage
      {language sublanguage : LanguageDef} {allowed : String → Prop}
      {free : FreeTypeContext} {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (selected : ∀ rule ∈ sublanguage.terms, rule ∈ language.terms ∧ allowed rule.label)
      (typed : ArgumentsHaveTypes sublanguage free bound arguments parameters) :
      ArgumentsHaveTypesWithConstructors language allowed free bound arguments parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation parameterType argument arguments =>
        exact .cons representation parameterType (argument.ofSublanguage selected)
          (arguments.ofSublanguage selected)

  theorem ElementsHaveType.ofSublanguage
      {language sublanguage : LanguageDef} {allowed : String → Prop}
      {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (selected : ∀ rule ∈ sublanguage.terms, rule ∈ language.terms ∧ allowed rule.label)
      (typed : ElementsHaveType sublanguage free bound elements elementType) :
      ElementsHaveTypeWithConstructors language allowed free bound elements elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons element elements =>
        exact .cons (element.ofSublanguage selected) (elements.ofSublanguage selected)
end

/-- Typing in a sublanguage is typing by the kept declarations. -/
theorem hasType_sublanguage_iff
    {language sublanguage : LanguageDef} {allowed : String → Prop}
    (terms : ∀ rule, rule ∈ sublanguage.terms ↔ rule ∈ language.terms ∧ allowed rule.label)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr} :
    HasType sublanguage free bound pattern type ↔
      HasTypeWithConstructors language allowed free bound pattern type :=
  ⟨HasType.ofSublanguage (fun rule membership => (terms rule).mp membership),
    HasTypeWithConstructors.toSublanguage
      (fun rule membership isAllowed => (terms rule).mpr ⟨membership, isAllowed⟩)⟩

end WellSorted

end Mettapedia.GSLT.LanguageDef
