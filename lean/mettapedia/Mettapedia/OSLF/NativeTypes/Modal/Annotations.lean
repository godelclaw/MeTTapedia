import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mettapedia.GSLT.LanguageDef.WellSortedOccurrence

open Mettapedia.OSLF.Framework

/-!
# Executable annotations for the full authored typing judgment

An annotation records choices that the source syntax does not determine:
the actual constructor declaration and the intermediate type of an explicit
substitution. No annotation contains a typing proof. The checker validates
every child against the independent authored typing rules, including named
binders and collection-rest metadata in source schemas.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.Annotations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

mutual
  inductive Annotation where
    | bvar
    | fvar
    | application (declaration : Nat) (arguments : AnnotationList)
    | lambda (body : Annotation)
    | multiLambda (body : Annotation)
    | subst (domain : TypeExpr) (body replacement : Annotation)
    | collection (elements : AnnotationList)
    | collectionConstructor (declaration : Nat) (elements : AnnotationList)
    deriving DecidableEq, Repr

  inductive AnnotationList where
    | nil
    | cons (first : Annotation) (remaining : AnnotationList)
    deriving DecidableEq, Repr
end

mutual
  /-- Check all actual term children, with intermediate types supplied as
  data and constructor alternatives selected by their declaration position. -/
  def check (language : LanguageDef) (free : FreeTypeContext)
      (bound : List TypeExpr) (source : Pattern) (expected : TypeExpr)
      (annotation : Annotation) : Bool :=
    match source, annotation with
    | .bvar index, .bvar => bound[index]? == some expected
    | .fvar name, .fvar => free name == some expected
    | .apply constructor arguments, .application declaration annotations =>
        match language.terms[declaration]? with
        | none => false
        | some rule => rule.label == constructor && expected == .base rule.category &&
            !usesBareCollection? rule &&
            checkArguments language free bound arguments rule.params annotations
    | .lambda _ body, .lambda bodyAnnotation =>
        match expected with
        | .arrow domain codomain => check language free (domain :: bound) body codomain bodyAnnotation
        | _ => false
    | .multiLambda arity _ body, .multiLambda bodyAnnotation =>
        match expected with
        | .arrow (.multiBinder domain) codomain =>
            check language free (List.replicate arity domain ++ bound) body codomain bodyAnnotation
        | _ => false
    | .subst body replacement, .subst domain bodyAnnotation replacementAnnotation =>
        check language free (domain :: bound) body expected bodyAnnotation &&
          check language free bound replacement domain replacementAnnotation
    | .collection kind elements _, .collection annotations =>
        match expected with
        | .collection actual elementType => actual == kind &&
            checkElements language free bound elements elementType annotations
        | _ => false
    | .collection kind elements _, .collectionConstructor declaration annotations =>
        match language.terms[declaration]? with
        | none => false
        | some rule =>
            match bareCollectionElementType? rule kind expected with
            | none => false
            | some elementType => checkElements language free bound elements elementType annotations
    | _, _ => false

  def checkArguments (language : LanguageDef) (free : FreeTypeContext)
      (bound : List TypeExpr) : List Pattern → List TermParam → AnnotationList → Bool
    | [], [], .nil => true
    | argument :: arguments, parameter :: parameters, .cons annotation annotations =>
        match parameterType? parameter with
        | none => false
        | some expected => matchesParameterRepresentation? parameter argument &&
            check language free bound argument expected annotation &&
            checkArguments language free bound arguments parameters annotations
    | _, _, _ => false

  def checkElements (language : LanguageDef) (free : FreeTypeContext)
      (bound : List TypeExpr) : List Pattern → TypeExpr → AnnotationList → Bool
    | [], _, .nil => true
    | element :: elements, expected, .cons annotation annotations =>
        check language free bound element expected annotation &&
          checkElements language free bound elements expected annotations
    | _, _, _ => false
end

mutual
  /-- A successful annotation is an independently authored typing derivation. -/
  theorem check_sound {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {source : Pattern} {expected : TypeExpr}
      {annotation : Annotation}
      (accepted : check language free bound source expected annotation = true) :
      HasType language free bound source expected := by
    cases annotation with
    | bvar =>
        cases source <;> simp [check] at accepted
        exact .bvar (by simpa only [beq_iff_eq] using accepted)
    | fvar =>
        cases source <;> simp [check] at accepted
        exact .fvar (by simpa only [beq_iff_eq] using accepted)
    | application declaration annotations =>
        cases source <;> simp only [check] at accepted
        all_goals try contradiction
        case apply constructor arguments =>
          cases lookup : language.terms[declaration]? with
          | none => simp [lookup] at accepted
          | some rule =>
              simp only [lookup, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at accepted
              rcases accepted with ⟨⟨⟨label, carrier⟩, ordinary⟩, children⟩
              subst constructor
              subst expected
              refine .constructor (List.mem_of_getElem? lookup) ?_ (checkArguments_sound children)
              intro bare
              have contradiction := (usesBareCollection?_eq_true_iff rule).mpr bare
              rw [contradiction] at ordinary
              contradiction
    | lambda annotation =>
        cases source <;> simp only [check] at accepted
        all_goals try contradiction
        case lambda binder body =>
          cases expected
          all_goals try contradiction
          exact .lambda (check_sound accepted)
    | multiLambda annotation =>
        cases source <;> simp only [check] at accepted
        all_goals try contradiction
        case multiLambda arity binders body =>
          cases expected
          all_goals try contradiction
          case arrow domain codomain =>
            cases domain
            all_goals try contradiction
            exact .multiLambda (check_sound accepted)
    | subst domain bodyAnnotation replacementAnnotation =>
        cases source <;> simp only [check] at accepted
        all_goals try contradiction
        case subst body replacement =>
          have both := (Bool.and_eq_true _ _).mp accepted
          exact .subst (check_sound both.1) (check_sound both.2)
    | collection annotations =>
        cases source <;> simp only [check] at accepted
        all_goals try contradiction
        case collection kind elements rest =>
          cases expected <;> simp only at accepted
          all_goals try contradiction
          case collection actual elementType =>
            have both := (Bool.and_eq_true _ _).mp accepted
            have same : actual = kind := by simpa only [beq_iff_eq] using both.1
            subst actual
            exact .collection (checkElements_sound both.2)
    | collectionConstructor declaration annotations =>
        cases source <;> simp only [check] at accepted
        all_goals try contradiction
        case collection kind elements rest =>
          cases lookup : language.terms[declaration]? with
          | none => simp [lookup] at accepted
          | some rule =>
            simp only [lookup] at accepted
            cases elementAt : bareCollectionElementType? rule kind expected with
            | none => simp [elementAt] at accepted
            | some elementType =>
                rw [elementAt] at accepted
                obtain ⟨carrier, parameter, shape⟩ :=
                  (bareCollectionElementType?_eq_some_iff rule kind expected elementType).mp elementAt
                subst expected
                exact .collectionConstructor (List.mem_of_getElem? lookup) shape
                  (checkElements_sound accepted)

  theorem checkArguments_sound {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam}
      {annotations : AnnotationList}
      (accepted : checkArguments language free bound arguments parameters annotations = true) :
      ArgumentsHaveTypes language free bound arguments parameters := by
    cases annotations with
    | nil =>
        cases arguments <;> cases parameters <;> simp [checkArguments] at accepted
        exact .nil
    | cons annotation annotations =>
        cases arguments <;> cases parameters <;> simp only [checkArguments] at accepted
        all_goals try contradiction
        case cons.cons argument arguments parameter parameters =>
          cases expectedAt : parameterType? parameter with
          | none => simp [expectedAt] at accepted
          | some expected =>
              simp only [expectedAt, Bool.and_eq_true] at accepted
              exact .cons
                ((matchesParameterRepresentation?_eq_true_iff parameter argument).mp accepted.1.1)
                expectedAt (check_sound accepted.1.2) (checkArguments_sound accepted.2)

  theorem checkElements_sound {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern} {expected : TypeExpr}
      {annotations : AnnotationList}
      (accepted : checkElements language free bound elements expected annotations = true) :
      ElementsHaveType language free bound elements expected := by
    cases annotations with
    | nil =>
        cases elements <;> simp [checkElements] at accepted
        exact .nil bound expected
    | cons annotation annotations =>
        cases elements <;> simp only [checkElements] at accepted
        all_goals try contradiction
        exact .cons (check_sound ((Bool.and_eq_true _ _).mp accepted).1)
          (checkElements_sound ((Bool.and_eq_true _ _).mp accepted).2)
end

mutual
  /-- Every raw authored typing has a finite annotation accepted by the
  algorithm, with no finite carrier or substitution-free restriction. -/
  theorem check_complete {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {source : Pattern} {expected : TypeExpr}
      (typed : HasType language free bound source expected) :
      ∃ annotation, check language free bound source expected annotation = true := by
    cases typed with
    | bvar lookup => exact ⟨.bvar, by simp [check, lookup]⟩
    | fvar lookup => exact ⟨.fvar, by simp [check, lookup]⟩
    | @constructor bound rule arguments declared ordinary typedArguments =>
        obtain ⟨declaration, lookup⟩ := List.mem_iff_getElem?.mp declared
        obtain ⟨annotations, accepted⟩ := checkArguments_complete typedArguments
        have notBare : usesBareCollection? rule = false :=
          Bool.eq_false_of_not_eq_true (fun bare => ordinary ((usesBareCollection?_eq_true_iff rule).mp bare))
        exact ⟨.application declaration annotations, by simp [check, lookup, notBare, accepted]⟩
    | lambda typedBody =>
        obtain ⟨annotation, accepted⟩ := check_complete typedBody
        exact ⟨.lambda annotation, accepted⟩
    | multiLambda typedBody =>
        obtain ⟨annotation, accepted⟩ := check_complete typedBody
        exact ⟨.multiLambda annotation, accepted⟩
    | @subst bound body replacement domain codomain typedBody typedReplacement =>
        obtain ⟨bodyAnnotation, bodyAccepted⟩ := check_complete typedBody
        obtain ⟨replacementAnnotation, replacementAccepted⟩ := check_complete typedReplacement
        exact ⟨.subst domain bodyAnnotation replacementAnnotation,
          by simp only [check, bodyAccepted, replacementAccepted, Bool.and_self]⟩
    | collection typedElements =>
        obtain ⟨annotations, accepted⟩ := checkElements_complete typedElements
        exact ⟨.collection annotations, by simp [check, accepted]⟩
    | @collectionConstructor bound rule parameter kind elements rest elementType declared shape typedElements =>
        obtain ⟨declaration, lookup⟩ := List.mem_iff_getElem?.mp declared
        obtain ⟨annotations, accepted⟩ := checkElements_complete typedElements
        have elementAt : bareCollectionElementType? rule kind (.base rule.category) = some elementType :=
          (bareCollectionElementType?_eq_some_iff rule kind (.base rule.category) elementType).mpr
            ⟨rfl, parameter, shape⟩
        exact ⟨.collectionConstructor declaration annotations,
          by simp [check, lookup, elementAt, accepted]⟩

  theorem checkArguments_complete {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound arguments parameters) :
      ∃ annotations, checkArguments language free bound arguments parameters annotations = true := by
    cases typed with
    | nil => exact ⟨.nil, rfl⟩
    | cons representation parameterAt typedArgument typedArguments =>
        obtain ⟨annotation, accepted⟩ := check_complete typedArgument
        obtain ⟨annotations, remainingAccepted⟩ := checkArguments_complete typedArguments
        exact ⟨.cons annotation annotations, by
          simp only [checkArguments, parameterAt, accepted, remainingAccepted,
            (matchesParameterRepresentation?_eq_true_iff _ _).mpr representation,
            Bool.and_self]⟩

  theorem checkElements_complete {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern} {expected : TypeExpr}
      (typed : ElementsHaveType language free bound elements expected) :
      ∃ annotations, checkElements language free bound elements expected annotations = true := by
    cases typed with
    | nil => exact ⟨.nil, rfl⟩
    | cons typedElement typedElements =>
        obtain ⟨annotation, accepted⟩ := check_complete typedElement
        obtain ⟨annotations, remainingAccepted⟩ := checkElements_complete typedElements
        exact ⟨.cons annotation annotations, by simp [checkElements, accepted, remainingAccepted]⟩
end

theorem annotation_exists_iff (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (source : Pattern) (expected : TypeExpr) :
    (∃ annotation, check language free bound source expected annotation = true) ↔
      HasType language free bound source expected :=
  ⟨fun ⟨_, accepted⟩ => check_sound accepted, check_complete⟩

end Mettapedia.OSLF.NativeTypes.Modal.Annotations
