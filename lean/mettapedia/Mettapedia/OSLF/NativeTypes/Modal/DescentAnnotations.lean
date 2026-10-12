import Mettapedia.OSLF.NativeTypes.Modal.Annotations
import Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

open Mettapedia.OSLF.Framework

/-!
# Checked annotations at every authored redex position

A descent certificate retains every intermediate typing choice and validates
the selected focus under the complete binder context. Each application and
collection frame also checks its siblings. Explicit substitution records its
intermediate domain separately on both possible descent branches.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.Annotations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence (take_selected_drop)

inductive DescentAnnotation where
  | here (focus : Annotation)
  | application (declaration : Nat) (arguments : AnnotationList) (inner : DescentAnnotation)
  | lambda (inner : DescentAnnotation)
  | multiLambda (inner : DescentAnnotation)
  | substBody (domain : TypeExpr) (replacement : Annotation) (inner : DescentAnnotation)
  | substReplacement (domain : TypeExpr) (body : Annotation) (inner : DescentAnnotation)
  | collection (elements : AnnotationList) (inner : DescentAnnotation)
  | collectionConstructor (declaration : Nat) (elements : AnnotationList) (inner : DescentAnnotation)
  deriving DecidableEq, Repr

/-- The selected bound context and focus type are checked at the hole; they
are never accepted merely because the whole source is well typed. -/
def checkDescent (language : LanguageDef) (free : FreeTypeContext)
    (focus : Pattern) (context : OneHoleContext) (bound : List TypeExpr)
    (expected : TypeExpr) (focusBound : List TypeExpr) (focusType : TypeExpr)
    (annotation : DescentAnnotation) : Bool :=
  match context, annotation with
  | .hole, .here focusAnnotation =>
      focusBound == bound && focusType == expected &&
        check language free bound focus expected focusAnnotation
  | .apply constructor before inner after, .application declaration annotations innerAnnotation =>
      match language.terms[declaration]? with
      | none => false
      | some rule =>
          rule.label == constructor && expected == .base rule.category &&
            !usesBareCollection? rule &&
            checkArguments language free bound (before ++ inner.fill focus :: after) rule.params annotations &&
            match rule.params[before.length]? with
            | none => false
            | some parameter =>
                match parameterType? parameter with
                | none => false
                | some parameterType =>
                    checkDescent language free focus inner bound parameterType focusBound focusType innerAnnotation
  | .lambda _ inner, .lambda innerAnnotation =>
      match expected with
      | .arrow domain codomain =>
          checkDescent language free focus inner (domain :: bound) codomain focusBound focusType innerAnnotation
      | _ => false
  | .multiLambda arity _ inner, .multiLambda innerAnnotation =>
      match expected with
      | .arrow (.multiBinder domain) codomain =>
          checkDescent language free focus inner (List.replicate arity domain ++ bound)
            codomain focusBound focusType innerAnnotation
      | _ => false
  | .substBody inner replacement, .substBody domain replacementAnnotation innerAnnotation =>
      check language free bound replacement domain replacementAnnotation &&
        checkDescent language free focus inner (domain :: bound) expected focusBound focusType innerAnnotation
  | .substReplacement body inner, .substReplacement domain bodyAnnotation innerAnnotation =>
      check language free (domain :: bound) body expected bodyAnnotation &&
        checkDescent language free focus inner bound domain focusBound focusType innerAnnotation
  | .collection kind before inner after _, .collection annotations innerAnnotation =>
      match expected with
      | .collection actual elementType => actual == kind &&
          checkElements language free bound (before ++ inner.fill focus :: after) elementType annotations &&
          checkDescent language free focus inner bound elementType focusBound focusType innerAnnotation
      | _ => false
  | .collection kind before inner after _, .collectionConstructor declaration annotations innerAnnotation =>
      match language.terms[declaration]? with
      | none => false
      | some rule =>
          match bareCollectionElementType? rule kind expected with
          | none => false
          | some elementType =>
              checkElements language free bound (before ++ inner.fill focus :: after) elementType annotations &&
                checkDescent language free focus inner bound elementType focusBound focusType innerAnnotation
  | _, _ => false

/-- Soundness includes the whole zipper, its selected constructor alternative,
both substitution branches, and the exact focus context and type. -/
theorem checkDescent_sound {language : LanguageDef} {free : FreeTypeContext}
    {focus : Pattern} {context : OneHoleContext} {bound focusBound : List TypeExpr}
    {expected focusType : TypeExpr} {annotation : DescentAnnotation}
    (accepted : checkDescent language free focus context bound expected focusBound focusType annotation = true) :
    TypedAt language free focus context bound expected focusBound focusType := by
  induction annotation generalizing context bound expected with
  | here focusAnnotation =>
      cases context <;> simp only [checkDescent] at accepted
      all_goals try contradiction
      case hole =>
        simp only [Bool.and_eq_true, beq_iff_eq] at accepted
        rcases accepted with ⟨⟨sameBound, sameType⟩, typed⟩
        subst focusBound
        subst focusType
        exact .here (check_sound typed)
  | application declaration annotations innerAnnotation ih =>
      cases context <;> simp only [checkDescent] at accepted
      all_goals try contradiction
      case apply constructor before inner after =>
        cases lookup : language.terms[declaration]? with
        | none => simp [lookup] at accepted
        | some rule =>
          simp only [lookup, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at accepted
          rcases accepted with ⟨⟨⟨⟨label, carrier⟩, ordinary⟩, arguments⟩, innerAccepted⟩
          cases parameterAt : rule.params[before.length]? with
          | none => simp [parameterAt] at innerAccepted
          | some parameter =>
            simp only [parameterAt] at innerAccepted
            cases typeAt : parameterType? parameter with
            | none => simp [typeAt] at innerAccepted
            | some parameterType =>
              simp only [typeAt] at innerAccepted
              subst constructor
              subst expected
              have parameterBound := (List.getElem?_eq_some_iff.mp parameterAt).1
              refine .application (List.mem_of_getElem? lookup) ?_ (checkArguments_sound arguments)
                (take_selected_drop parameterAt).symm ?_ typeAt (ih innerAccepted)
              · intro bare
                have impossible := (usesBareCollection?_eq_true_iff rule).mpr bare
                rw [impossible] at ordinary
                contradiction
              · simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt parameterBound)]
  | lambda innerAnnotation ih =>
      cases context <;> simp only [checkDescent] at accepted
      all_goals try contradiction
      case lambda binder inner =>
        cases expected
        all_goals try contradiction
        exact .lambda (ih accepted)
  | multiLambda innerAnnotation ih =>
      cases context <;> simp only [checkDescent] at accepted
      all_goals try contradiction
      case multiLambda arity binders inner =>
        cases expected
        all_goals try contradiction
        case arrow domain codomain =>
          cases domain
          all_goals try contradiction
          exact .multiLambda (ih accepted)
  | substBody domain replacementAnnotation innerAnnotation ih =>
      cases context <;> simp only [checkDescent] at accepted
      all_goals try contradiction
      exact .substBody (check_sound ((Bool.and_eq_true _ _).mp accepted).1)
        (ih ((Bool.and_eq_true _ _).mp accepted).2)
  | substReplacement domain bodyAnnotation innerAnnotation ih =>
      cases context <;> simp only [checkDescent] at accepted
      all_goals try contradiction
      exact .substReplacement (check_sound ((Bool.and_eq_true _ _).mp accepted).1)
        (ih ((Bool.and_eq_true _ _).mp accepted).2)
  | collection annotations innerAnnotation ih =>
      cases context <;> simp only [checkDescent] at accepted
      all_goals try contradiction
      case collection kind before inner after rest =>
        cases expected
        all_goals try contradiction
        case collection actual elementType =>
          simp only [Bool.and_eq_true, beq_iff_eq] at accepted
          rcases accepted with ⟨⟨sameKind, elements⟩, innerAccepted⟩
          subst actual
          exact .collection (checkElements_sound elements) (ih innerAccepted)
  | collectionConstructor declaration annotations innerAnnotation ih =>
      cases context <;> simp only [checkDescent] at accepted
      all_goals try contradiction
      case collection kind before inner after rest =>
        cases lookup : language.terms[declaration]? with
        | none => simp [lookup] at accepted
        | some rule =>
          simp only [lookup] at accepted
          cases elementAt : bareCollectionElementType? rule kind expected with
          | none => simp [elementAt] at accepted
          | some elementType =>
            simp only [elementAt] at accepted
            have both := (Bool.and_eq_true _ _).mp accepted
            obtain ⟨carrier, parameter, shape⟩ :=
              (bareCollectionElementType?_eq_some_iff rule kind expected elementType).mp elementAt
            subst expected
            exact .collectionConstructor (List.mem_of_getElem? lookup) shape
              (checkElements_sound both.1) (ih both.2)

/-- Every independently typed descent has a checking certificate. This is a
whole-language theorem, without a finite source-carrier enumeration. -/
theorem checkDescent_complete {language : LanguageDef} {free : FreeTypeContext}
    {focus : Pattern} {context : OneHoleContext} {bound focusBound : List TypeExpr}
    {expected focusType : TypeExpr}
    (typed : TypedAt language free focus context bound expected focusBound focusType) :
    ∃ annotation, checkDescent language free focus context bound expected focusBound focusType annotation = true := by
  induction typed with
  | here typing =>
      obtain ⟨annotation, accepted⟩ := check_complete typing
      exact ⟨.here annotation, by simp [checkDescent, accepted]⟩
  | @application rule before after inner bound focusBound expected result beforeParams afterParams parameter
      declared ordinary arguments shape length parameterType innerTyped ih =>
      obtain ⟨declaration, lookup⟩ := List.mem_iff_getElem?.mp declared
      obtain ⟨annotations, argumentsAccepted⟩ := checkArguments_complete arguments
      obtain ⟨innerAnnotation, innerAccepted⟩ := ih
      have parameterAt : rule.params[before.length]? = some parameter := by
        rw [shape, ← length]
        simp
      have notBare : usesBareCollection? rule = false :=
        Bool.eq_false_of_not_eq_true (fun bare => ordinary ((usesBareCollection?_eq_true_iff rule).mp bare))
      exact ⟨.application declaration annotations innerAnnotation, by
        simp [checkDescent, lookup, argumentsAccepted, parameterAt, parameterType, notBare, innerAccepted]⟩
  | lambda innerTyped ih =>
      obtain ⟨innerAnnotation, innerAccepted⟩ := ih
      exact ⟨.lambda innerAnnotation, innerAccepted⟩
  | multiLambda innerTyped ih =>
      obtain ⟨innerAnnotation, innerAccepted⟩ := ih
      exact ⟨.multiLambda innerAnnotation, innerAccepted⟩
  | @substBody inner replacement bound focusBound domain codomain result replacementTyped innerTyped ih =>
      obtain ⟨replacementAnnotation, replacementAccepted⟩ := check_complete replacementTyped
      obtain ⟨innerAnnotation, innerAccepted⟩ := ih
      exact ⟨.substBody domain replacementAnnotation innerAnnotation,
        by simp [checkDescent, replacementAccepted, innerAccepted]⟩
  | @substReplacement body inner bound focusBound domain codomain result bodyTyped innerTyped ih =>
      obtain ⟨bodyAnnotation, bodyAccepted⟩ := check_complete bodyTyped
      obtain ⟨innerAnnotation, innerAccepted⟩ := ih
      exact ⟨.substReplacement domain bodyAnnotation innerAnnotation,
        by simp [checkDescent, bodyAccepted, innerAccepted]⟩
  | collection elements innerTyped ih =>
      obtain ⟨annotations, elementsAccepted⟩ := checkElements_complete elements
      obtain ⟨innerAnnotation, innerAccepted⟩ := ih
      exact ⟨.collection annotations innerAnnotation, by simp [checkDescent, elementsAccepted, innerAccepted]⟩
  | @collectionConstructor rule parameter kind before after inner rest bound focusBound element result
      declared shape elements innerTyped ih =>
      obtain ⟨declaration, lookup⟩ := List.mem_iff_getElem?.mp declared
      obtain ⟨annotations, elementsAccepted⟩ := checkElements_complete elements
      obtain ⟨innerAnnotation, innerAccepted⟩ := ih
      have elementAt : bareCollectionElementType? rule kind (.base rule.category) = some element :=
        (bareCollectionElementType?_eq_some_iff rule kind (.base rule.category) element).mpr ⟨rfl, parameter, shape⟩
      exact ⟨.collectionConstructor declaration annotations innerAnnotation,
        by simp [checkDescent, lookup, elementAt, elementsAccepted, innerAccepted]⟩

theorem descent_annotation_exists_iff (language : LanguageDef) (free : FreeTypeContext)
    (focus : Pattern) (context : OneHoleContext) (bound focusBound : List TypeExpr)
    (expected focusType : TypeExpr) :
    (∃ annotation, checkDescent language free focus context bound expected focusBound focusType annotation = true) ↔
      TypedAt language free focus context bound expected focusBound focusType :=
  ⟨fun ⟨_, accepted⟩ => checkDescent_sound accepted, checkDescent_complete⟩

end Mettapedia.OSLF.NativeTypes.Modal.Annotations
