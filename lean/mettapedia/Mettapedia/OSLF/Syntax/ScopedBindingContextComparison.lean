import Mettapedia.OSLF.Syntax.ScopedBindingContexts
import Mettapedia.GSLT.Logic.RelativePushoutFullComparison

/-!
# The actual binding-context category comparison

Complete source terms and linear binder paths form their own category. Their
earned readouts construct a full, faithful, object-surjective functor into
the independently formed sorted constructor category. All competing IPO
apices and mediators are therefore included in the comparison.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.ScopedEncoding

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RelativePushout

variable (S : Binding.Signature)

local instance : Quiver (Scope S) := bindingFrameQuiver S

def objectReading : BindingContextObject S → SortedConstructors.ContextObject (signature S)
  | .origin => @Object.origin (Scope S) (SortedConstructors.frameQuiver (signature S))
      (SortedConstructors.action (signature S))
  | .interface scope => @Object.interface (Scope S) (SortedConstructors.frameQuiver (signature S))
      (SortedConstructors.action (signature S)) scope

variable {S}

def arrowReading : {first last : BindingContextObject S} → (first ⟶ last) →
    (objectReading S first ⟶ objectReading S last)
  | _, _, .identity => @Arrow.identity (Scope S) (SortedConstructors.frameQuiver (signature S))
      (SortedConstructors.action (signature S))
  | _, _, .value supplied => SortedConstructors.termArrow (signature S) (encode supplied)
  | _, _, .context context => SortedConstructors.contextArrow (signature S) (encodeContext context)

variable (S)

def contextFunctor :
    BindingContextObject S ⥤ SortedConstructors.ContextObject (signature S) where
  obj := objectReading S
  map := arrowReading
  map_id object := by cases object <;> rfl
  map_comp first second := by
    cases first with
    | identity => rfl
    | value supplied =>
      cases second with
      | context context =>
        exact congrArg (SortedConstructors.termArrow (signature S))
          (encodeContext_fill context supplied)
    | context inner =>
      cases second with
      | context outer =>
        exact congrArg (SortedConstructors.contextArrow (signature S))
          (encodeContext_comp inner outer)

variable {S}

instance contextFunctor_faithful : (contextFunctor S).Faithful where
  map_injective := by
    intro first last before after same
    cases before with
    | identity => cases after; rfl
    | value before =>
      cases after with
      | value after =>
        change SortedConstructors.termArrow (signature S) (encode before) =
          SortedConstructors.termArrow (signature S) (encode after) at same
        have sameTerm : encode before = encode after := by injection same
        exact congrArg bindingTermArrow (encode_injective sameTerm)
    | context before =>
      cases after with
      | context after =>
        change SortedConstructors.contextArrow (signature S) (encodeContext before) =
          SortedConstructors.contextArrow (signature S) (encodeContext after) at same
        have samePath : encodeContext before = encodeContext after := by injection same
        exact congrArg bindingContextArrow ((contextEquiv _ _).injective samePath)

instance contextFunctor_full : (contextFunctor S).Full where
  map_surjective := by
    intro first last supplied
    cases first with
    | origin =>
      cases last with
      | origin =>
        cases supplied
        exact ⟨@Arrow.identity (Scope S) (bindingFrameQuiver S) (bindingAction S), rfl⟩
      | interface scope =>
        cases supplied with
        | value term => exact ⟨bindingTermArrow (decode term),
            congrArg (SortedConstructors.termArrow (signature S)) (encode_decode term)⟩
    | interface source =>
      cases last with
      | origin => cases supplied
      | interface target =>
        cases supplied with
        | context context =>
          exact ⟨bindingContextArrow (decodeContext context),
            congrArg (SortedConstructors.contextArrow (signature S)) (encode_decodeContext context)⟩

theorem contextFunctor_objects : Function.Surjective (contextFunctor S).obj := by
  intro object
  cases object with
  | origin => exact ⟨bindingOrigin S, rfl⟩
  | interface scope => exact ⟨bindingInterface S scope, rfl⟩

instance contextFunctor_essSurj : (contextFunctor S).EssSurj :=
  Functor.essSurj_of_surj (contextFunctor_objects (S := S))

instance contextFunctor_isEquivalence : (contextFunctor S).IsEquivalence where

def contextCategoryEquivalence (S : Binding.Signature) :
    BindingContextObject S ≌ SortedConstructors.ContextObject (signature S) :=
  (contextFunctor S).asEquivalence

/-- Actual linear scoped binding redexes have complete redex-relative pushouts. -/
theorem binding_redex_relativePushouts {first second : Scope S}
    (agent : Binding.Term S first.1 first.2) (redex : Binding.Term S second.1 second.2) :
    HasRelativePushouts (bindingTermArrow agent) (bindingTermArrow redex) :=
  @ground_hasRelativePushouts (Scope S) (bindingFrameQuiver S) (bindingAction S)
    first second agent redex

theorem binding_idemPushout_iff_sorted {W X Y Z : BindingContextObject S}
    (first : W ⟶ X) (second : W ⟶ Y) (left : X ⟶ Z) (right : Y ⟶ Z)
    (square : first ≫ left = second ≫ right) :
    IsIdemPushout first second left right square ↔
      IsIdemPushout ((contextFunctor S).map first) ((contextFunctor S).map second)
        ((contextFunctor S).map left) ((contextFunctor S).map right)
        (by rw [← (contextFunctor S).map_comp, square, (contextFunctor S).map_comp]) :=
  ⟨preserves_idemPushout (contextFunctor S) (contextFunctor_objects (S := S)) square,
    reflects_idemPushout (contextFunctor S) square⟩

theorem binding_relativePushout_iff_sorted {W X Y Z : BindingContextObject S}
    {first : W ⟶ X} {second : W ⟶ Y} {left : X ⟶ Z} {right : Y ⟶ Z}
    (candidate : Candidate first second left right) :
    IsRelativePushout candidate ↔ IsRelativePushout (mapCandidate (contextFunctor S) candidate) :=
  relativePushout_iff_mapped (contextFunctor S) (contextFunctor_objects (S := S)) candidate

end Mettapedia.OSLF.Binding.ScopedEncoding
