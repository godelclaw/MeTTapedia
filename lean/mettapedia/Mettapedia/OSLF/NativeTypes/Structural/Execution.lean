import Mettapedia.OSLF.NativeTypes.Structural.Semantics
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

open Mettapedia.OSLF.Framework

/-!
# Executable structural readouts of equation representatives

The parser-level root is checked against the exact constructor declaration,
including ordered types and binder representation. The readout can inspect the
representatives retained by the certified executor. A positive result has a
typed constructor witness. A negative result is conclusive only with equation
coverage and an object-carrier condition; unfinished search proves no absence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Structural

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Resolve an actual object representative to the introduction and ordered
arguments of one generated structural former. -/
def constructorArguments? (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (declaration : GrammarRule) : Pattern → Option (List Pattern)
  | .apply label arguments =>
      if label == declaration.label && !usesBareCollection? declaration &&
          checkArgumentsHaveTypes language free bound arguments declaration.params then
        some arguments
      else none
  | .collection kind elements rest =>
      match bareCollectionElementType? declaration kind (.base declaration.category) with
      | none => none
      | some elementType =>
          if rest.isNone && checkElementsHaveType language free bound elements elementType then
            some [.collection kind elements rest]
          else none
  | _ => none

theorem constructorArguments?_sound {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {declaration : GrammarRule} {term : Pattern} {arguments : List Pattern}
    (checked : constructorArguments? language free bound declaration term = some arguments) :
    ∃ value : ConstructorValue language free bound declaration,
      value.pattern = term ∧ value.arguments = arguments := by
  cases term with
  | apply label actual =>
      simp only [constructorArguments?] at checked
      split at checked
      next accepted =>
        simp only [Bool.and_eq_true, beq_iff_eq] at accepted
        have ordinary : ¬ UsesBareCollection declaration := by
          intro bare
          have trueFlag := (usesBareCollection?_eq_true_iff declaration).mpr bare
          have notFlag := accepted.1.2
          rw [trueFlag] at notFlag
          cases notFlag
        have typed : ArgumentsHaveTypes language free bound actual declaration.params :=
          checkArgumentsHaveTypes_sound_of
            (fun _ _ _ argumentChecked => checkHasType_sound argumentChecked) accepted.2
        have same : actual = arguments := Option.some.inj checked
        refine ⟨.ordinary actual ordinary typed, ?_, same⟩
        simp only [ConstructorValue.pattern, accepted.1.1]
      next rejected => cases checked
  | collection kind elements rest =>
      simp only [constructorArguments?] at checked
      cases element : bareCollectionElementType? declaration kind (.base declaration.category) with
      | none => simp [element] at checked
      | some elementType =>
          simp only [element] at checked
          split at checked
          next accepted =>
            simp only [Bool.and_eq_true] at accepted
            obtain ⟨_, parameterName, shape⟩ :=
              (bareCollectionElementType?_eq_some_iff _ _ _ _).mp element
            exact ⟨.collection parameterName kind elementType elements rest shape
              (checkElementsHaveType_sound accepted.2), rfl, Option.some.inj checked⟩
          next rejected => cases checked
  | bvar index => cases checked
  | fvar name => cases checked
  | lambda binder body => cases checked
  | multiLambda count binders body => cases checked
  | subst body replacement => cases checked

theorem constructorArguments?_complete {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {declaration : GrammarRule}
    (value : ConstructorValue language free bound declaration)
    (object : isObjectPattern value.pattern = true) :
    constructorArguments? language free bound declaration value.pattern = some value.arguments := by
  cases value with
  | ordinary arguments ordinary typed =>
      have bare : usesBareCollection? declaration = false := by
        apply Bool.eq_false_of_not_eq_true
        exact fun checked => ordinary ((usesBareCollection?_eq_true_iff declaration).mp checked)
      have checked := checkArgumentsHaveTypes_complete_of_objects typed object
      simp [constructorArguments?, ConstructorValue.pattern, ConstructorValue.arguments, bare, checked]
  | collection parameterName kind elementType elements rest shape typed =>
      have element : bareCollectionElementType? declaration kind (.base declaration.category) =
          some elementType := (bareCollectionElementType?_eq_some_iff _ _ _ _).mpr
            ⟨rfl, parameterName, shape⟩
      change (rest.isNone && isObjectPatternList elements) = true at object
      simp only [Bool.and_eq_true] at object
      have checked := checkElementsHaveType_complete_of_objects typed object.2
      simp [constructorArguments?, ConstructorValue.pattern, ConstructorValue.arguments,
        element, object.1, checked]

/-- Query the actual equation-representative list, retaining the declaration
index check. -/
def checkStructural (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (former : Former) (representatives : List Pattern) : Bool :=
  (language.terms[former.index]? == some former.declaration) &&
    representatives.any fun term => (constructorArguments? language free bound former.declaration term).isSome

theorem checkStructural_sound {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {former : Former} {representatives : List Pattern}
    {equation : Pattern → Pattern → Prop} {source : Pattern}
    (represented : ∀ term ∈ representatives, equation source term)
    (checked : checkStructural language free bound former representatives = true) :
    StructuralHolds language free bound equation former source := by
  simp only [checkStructural, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at checked
  obtain ⟨term, member, nonempty⟩ := checked.2
  cases found : constructorArguments? language free bound former.declaration term with
  | none => simp [found] at nonempty
  | some arguments =>
      obtain ⟨value, equal, _⟩ := constructorArguments?_sound found
      refine ⟨(mem_structuralFormers_iff language former).mpr checked.1, value, ?_⟩
      rw [equal]
      exact represented term member

/-- Certified representative coverage earns completeness; mere enumeration
does not. The object condition matches the executor's admitted carrier. -/
theorem checkStructural_complete {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {former : Former} {representatives : List Pattern}
    {equation : Pattern → Pattern → Prop} {source : Pattern}
    (covered : ∀ term, equation source term → term ∈ representatives)
    (objects : ∀ term, equation source term → isObjectPattern term = true)
    (holds : StructuralHolds language free bound equation former source) :
    checkStructural language free bound former representatives = true := by
  obtain ⟨member, value, related⟩ := holds
  have found := constructorArguments?_complete value (objects value.pattern related)
  simp only [checkStructural, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
  exact ⟨(mem_structuralFormers_iff language former).mp member,
    value.pattern, covered value.pattern related, by rw [found]; rfl⟩

theorem checkStructural_iff {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {former : Former} {representatives : List Pattern}
    {equation : Pattern → Pattern → Prop} {source : Pattern}
    (represented : ∀ term ∈ representatives, equation source term)
    (covered : ∀ term, equation source term → term ∈ representatives)
    (objects : ∀ term, equation source term → isObjectPattern term = true) :
    checkStructural language free bound former representatives = true ↔
      StructuralHolds language free bound equation former source :=
  ⟨checkStructural_sound represented, checkStructural_complete covered objects⟩

end Mettapedia.OSLF.NativeTypes.Structural
