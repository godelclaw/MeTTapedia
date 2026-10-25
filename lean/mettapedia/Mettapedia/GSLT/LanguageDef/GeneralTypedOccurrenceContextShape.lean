import Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceReplacement

/-!
# Hole-path shape and authored parameter representation

Representation checking follows the retained declaration frames and inspects
only binding-node shape. Fixed sibling values and unordered residual sizes do
not affect it. Context shape records exactly the unchanged hole-path forms.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites WellSorted

inductive ContextShape : OneHoleContext → OneHoleContext → Prop where
  | hole : ContextShape .hole .hole
  | application {label : String} {before before' after after' : List Pattern}
      {inner inner' : OneHoleContext} : ContextShape inner inner' →
      ContextShape (.apply label before inner after) (.apply label before' inner' after')
  | lambda {binder : Option String} {inner inner' : OneHoleContext} : ContextShape inner inner' →
      ContextShape (.lambda binder inner) (.lambda binder inner')
  | multiLambda {arity : Nat} {binders : List String} {inner inner' : OneHoleContext} :
      ContextShape inner inner' → ContextShape (.multiLambda arity binders inner) (.multiLambda arity binders inner')
  | substBody {replacement replacement' : Pattern} {inner inner' : OneHoleContext} :
      ContextShape inner inner' → ContextShape (.substBody inner replacement) (.substBody inner' replacement')
  | substReplacement {body body' : Pattern} {inner inner' : OneHoleContext} :
      ContextShape inner inner' → ContextShape (.substReplacement body inner) (.substReplacement body' inner')
  | collection {kind : CollType} {rest rest' : Option String} {before before' after after' : List Pattern}
      {inner inner' : OneHoleContext} : ContextShape inner inner' →
      ContextShape (.collection kind before inner after rest) (.collection kind before' inner' after' rest')

theorem ContextShape.parameter {context context' : OneHoleContext} (shape : ContextShape context context')
    {target target' : Pattern}
    (same : ∀ parameter, matchesParameterRepresentation? parameter target =
      matchesParameterRepresentation? parameter target') (parameter : TermParam) :
    matchesParameterRepresentation? parameter (context.fill target) =
      matchesParameterRepresentation? parameter (context'.fill target') := by
  cases shape with
  | hole => exact same parameter
  | application | substBody | substReplacement | collection =>
    cases parameter <;> rfl
  | @lambda binder _ _ _ =>
    cases binder <;> cases parameter <;> rfl
  | @multiLambda _ binders _ _ _ =>
    cases binders <;> cases parameter <;> rfl

theorem ContextShape.replacementRepresentations {language : LanguageDef} {context context' : OneHoleContext}
    (shape : ContextShape context context') (frames : List TypingFrame) {target target' : Pattern}
    (same : ∀ parameter, matchesParameterRepresentation? parameter target =
      matchesParameterRepresentation? parameter target') :
    replacementRepresentations? language context frames target =
      replacementRepresentations? language context' frames target' := by
  induction shape generalizing frames with
  | hole => cases frames <;> rfl
  | @application label before before' after after' inner inner' shape ih =>
    cases frames with
    | nil => rfl
    | cons frame frames =>
      cases frame <;> try rfl
      case application declaration index =>
        simp only [replacementRepresentations?]
        cases language.terms[declaration]?.bind (fun rule => rule.params[index]?) with
        | none => rfl
        | some parameter =>
          simp only [shape.parameter same parameter, ih frames]
  | lambda shape ih =>
    cases frames with
    | nil => rfl
    | cons frame frames => cases frame <;> simp only [replacementRepresentations?, ih frames]
  | multiLambda shape ih =>
    cases frames with
    | nil => rfl
    | cons frame frames => cases frame <;> simp only [replacementRepresentations?, ih frames]
  | substBody | substReplacement => rfl
  | collection shape ih =>
    cases frames with
    | nil => rfl
    | cons frame frames => cases frame <;> simp only [replacementRepresentations?, ih frames]

theorem retained_set_copy_has_same_context_shape (value : Pattern) :
    ContextShape (.collection .hashSet [] .hole [] none)
      (.collection .hashSet [] .hole [value] none) := .collection .hole

/-- Inserting a binder changes the actual representation check. Equal
result types alone cannot erase this distinction. -/
theorem inserted_binder_changes_parameter_representation :
    matchesParameterRepresentation? (.abstractionNamed none "body" (.base "T"))
        (OneHoleContext.hole.fill (.fvar "f")) ≠
      matchesParameterRepresentation? (.abstractionNamed none "body" (.base "T"))
        ((OneHoleContext.lambda none .hole).fill (.fvar "f")) := by decide

end Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
