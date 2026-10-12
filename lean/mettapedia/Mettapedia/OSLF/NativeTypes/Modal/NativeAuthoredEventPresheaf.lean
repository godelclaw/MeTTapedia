import Mettapedia.OSLF.NativeTypes.Modal.NativeAuthoredEventAction
import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeAdequacy

/-!
# Actual selected operational events over the original constructor category

The original authored binding clone remains the base category after rule
selection. Independently typed operational transport gives the event action;
its complete receipt, source and specified target are retained naturally.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeAuthoredEventPresheaf

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.NativeTypes.Generation
open CurriedBindingLanguage BindingSemanticAdmission
open IntrinsicScopedConditionalPresheaf
open NativeAuthoredEventAction

variable {environment : Environment} {language : LanguageDef}

def morphismSub {X Y : Base (algebra language)} (morphism : X ⟶ Y) :
    Sub (signature language) X.unop.context Y.unop.context :=
  BindingSubstitutionAlgebra.fromPositions X.unop.context morphism.unop

theorem morphismSub_identity (X : Base (algebra language)) :
    morphismSub (𝟙 X) = fun _ position => Term.var position := by
  funext sort position
  exact BindingSubstitutionAlgebra.fromPositions_ofEnvironment
    (fun _ position => Term.var position) position

theorem morphismSub_composition {X Y Z : Base (algebra language)}
    (first : X ⟶ Y) (second : Y ⟶ Z) :
    morphismSub (first ≫ second) =
      fun sort position => Binding.bind (morphismSub second) (morphismSub first sort position) := by
  funext sort position
  exact BindingSubstitutionAlgebra.fromPositions_substitute
    (algebra language).substitution first.unop (morphismSub second) position

def events (grammar : environment.language.terms = language.terms)
    (freeEmpty : environment.free = Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted environment) (sort : String) :
    Base (algebra language) ⥤ Type where
  obj X := Point environment language X.unop.context sort
  map morphism := TypeCat.ofHom (action grammar freeEmpty ready (morphismSub morphism))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro point
    change action grammar freeEmpty ready (morphismSub (𝟙 X)) point = point
    rw [morphismSub_identity]
    exact action_identity grammar freeEmpty ready point
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro point
    change action grammar freeEmpty ready (morphismSub (first ≫ second)) point =
      action grammar freeEmpty ready (morphismSub second)
        (action grammar freeEmpty ready (morphismSub first) point)
    rw [morphismSub_composition]
    exact (action_composition grammar freeEmpty ready (morphismSub first) (morphismSub second) point).symm

def source (grammar : environment.language.terms = language.terms)
    (freeEmpty : environment.free = Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted environment) (sort : String) :
    events grammar freeEmpty ready sort ⟶ semanticPrograms (algebra language) sort where
  app _ := TypeCat.ofHom Point.source
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro point
    rfl

noncomputable def target (grammar : environment.language.terms = language.terms)
    (freeEmpty : environment.free = Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted environment) (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup) (sort : String) :
    events grammar freeEmpty ready sort ⟶ semanticPrograms (algebra language) sort where
  app _ := TypeCat.ofHom (targetTerm grammar freeEmpty admitted labels)
  naturality _ _ morphism := by
    apply ConcreteCategory.hom_ext
    intro point
    exact targetTerm_natural grammar freeEmpty ready admitted labels (morphismSub morphism) point

end Mettapedia.OSLF.NativeTypes.Modal.NativeAuthoredEventPresheaf
