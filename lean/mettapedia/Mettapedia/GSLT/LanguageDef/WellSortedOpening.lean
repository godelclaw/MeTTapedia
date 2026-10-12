import Mettapedia.GSLT.LanguageDef.WellSortedClosing

/-!
# Opening an outer bound slot into a declared free name

Every authored constructor and binder is preserved. The opened slot is
outside the existing bound context, so its replacement introduces a named
free occurrence without shifting or conflating the surviving bound indices.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

theorem matchesParameterRepresentation_openFVar_iff
    (parameter : TermParam) (pattern : Pattern) (index : Nat) (name : String) :
    MatchesParameterRepresentation parameter (openBVar index (.fvar name) pattern) ↔
      MatchesParameterRepresentation parameter pattern := by
  cases parameter with
  | simple => simp [MatchesParameterRepresentation]
  | abstractionNamed =>
      cases pattern <;> simp only [openBVar] <;> try rfl
      case bvar => split_ifs <;> rfl
      case lambda binder body => cases binder <;> simp only [MatchesParameterRepresentation]
  | multiAbstractionNamed =>
      cases pattern <;> simp only [openBVar] <;> try rfl
      case bvar => split_ifs <;> rfl
      case multiLambda arity binders body => cases binders <;> simp only [MatchesParameterRepresentation]

mutual
  theorem HasType.openLast {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {binderType : TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language free (bound ++ [binderType]) pattern type)
      (name : String) (lookup : free name = some binderType) :
      HasType language free bound (openBVar bound.length (.fvar name) pattern) type := by
    cases typed with
    | bvar present =>
        rename_i index
        have small : index < bound.length + 1 := by
          have := (List.getElem?_eq_some_iff.mp present).choose
          simpa only [List.length_append, List.length_singleton] using this
        by_cases old : index < bound.length
        · have unequal : ¬ (index == bound.length) = true := by simp; omega
          simp only [openBVar, unequal]
          exact .bvar (by rw [List.getElem?_append_left old] at present; exact present)
        · have same : index = bound.length := by omega
          subst index
          have expected : binderType = type := by simpa using present
          subst type
          simp only [openBVar, beq_self_eq_true, ↓reduceIte]
          exact .fvar lookup
    | fvar present => simpa only [openBVar] using HasType.fvar present
    | constructor member ordinary argumentsTyped =>
        simpa only [openBVar] using HasType.constructor member ordinary
          (argumentsTyped.openLast name lookup)
    | @lambda _ binder body domain codomain bodyTyped =>
        have inContext : HasType language free ((domain :: bound) ++ [binderType]) body codomain := bodyTyped
        have opened : HasType language free (domain :: bound)
            (openBVar (bound.length + 1) (.fvar name) body) codomain := by
          convert inContext.openLast name lookup using 1
          rfl
        simpa only [openBVar] using HasType.lambda (binder := binder) opened
    | @multiLambda _ arity binders body domain codomain bodyTyped =>
        have inContext : HasType language free
            ((List.replicate arity domain ++ bound) ++ [binderType]) body codomain := by
          simpa only [List.append_assoc] using bodyTyped
        have opened : HasType language free (List.replicate arity domain ++ bound)
            (openBVar (bound.length + arity) (.fvar name) body) codomain := by
          simpa only [List.append_assoc, List.length_append, List.length_replicate, Nat.add_comm]
            using inContext.openLast name lookup
        simpa only [openBVar] using HasType.multiLambda (binders := binders) opened
    | @subst _ body replacement domain _ bodyTyped replacementTyped =>
        have opened : HasType language free (domain :: bound)
            (openBVar (bound.length + 1) (.fvar name) body) type := by
          have inContext : HasType language free ((domain :: bound) ++ [binderType]) body type := bodyTyped
          convert inContext.openLast name lookup using 1
          rfl
        simpa only [openBVar] using HasType.subst opened (replacementTyped.openLast name lookup)
    | collection elementsTyped =>
        simpa only [openBVar] using HasType.collection (elementsTyped.openLast name lookup)
    | collectionConstructor member shape elementsTyped =>
        simpa only [openBVar] using HasType.collectionConstructor member shape
          (elementsTyped.openLast name lookup)

  theorem ArgumentsHaveTypes.openLast {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {binderType : TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free (bound ++ [binderType]) arguments parameters)
      (name : String) (lookup : free name = some binderType) :
      ArgumentsHaveTypes language free bound
        (arguments.map (openBVar bound.length (.fvar name))) parameters := by
    cases typed with
    | nil => exact .nil
    | cons represented expected head tail =>
        exact .cons ((matchesParameterRepresentation_openFVar_iff _ _ _ _).mpr represented)
          expected (head.openLast name lookup) (tail.openLast name lookup)

  theorem ElementsHaveType.openLast {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {binderType : TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (typed : ElementsHaveType language free (bound ++ [binderType]) elements elementType)
      (name : String) (lookup : free name = some binderType) :
      ElementsHaveType language free bound
        (elements.map (openBVar bound.length (.fvar name))) elementType := by
    cases typed with
    | nil => exact .nil bound elementType
    | cons head tail => exact .cons (head.openLast name lookup) (tail.openLast name lookup)
end

end Mettapedia.GSLT.LanguageDef.WellSorted
