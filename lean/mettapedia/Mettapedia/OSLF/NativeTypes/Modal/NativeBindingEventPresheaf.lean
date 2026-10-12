import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingEventAction
import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeAdequacy

/-!
# Authored operational receipts in the native program presheaf category

The base category is the same independently generated binding clone that
interprets the native constructor signature. Actual firing receipts form a
presheaf there. Source and specified-target projections are natural maps
into the actual program carrier; individual witnesses remain distinct.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingEventPresheaf

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.NativeTypes.Generation
open CurriedBindingLanguage BindingSemanticAdmission
open IntrinsicScopedConditionalPresheaf
open NativeBindingEventAction

variable {environment : Environment}

def morphismSub {X Y : Base (algebra environment.language)} (morphism : X ⟶ Y) :
    Sub (signature environment.language) X.unop.context Y.unop.context :=
  BindingSubstitutionAlgebra.fromPositions X.unop.context morphism.unop

theorem morphismSub_identity (X : Base (algebra environment.language)) :
    morphismSub (𝟙 X) = fun _ position => Term.var position := by
  funext sort position
  exact BindingSubstitutionAlgebra.fromPositions_ofEnvironment
    (fun _ position => Term.var position) position

theorem morphismSub_composition {X Y Z : Base (algebra environment.language)}
    (first : X ⟶ Y) (second : Y ⟶ Z) :
    morphismSub (first ≫ second) =
      fun sort position => Binding.bind (morphismSub second) (morphismSub first sort position) := by
  funext sort position
  exact BindingSubstitutionAlgebra.fromPositions_substitute
    (algebra environment.language).substitution first.unop (morphismSub second) position

def events (freeEmpty : environment.free = Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted environment) (sort : String) :
    Base (algebra environment.language) ⥤ Type where
  obj X := Point environment X.unop.context sort
  map morphism := TypeCat.ofHom (action freeEmpty ready (morphismSub morphism))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro point
    change action freeEmpty ready (morphismSub (𝟙 X)) point = point
    rw [morphismSub_identity]
    exact action_identity freeEmpty ready point
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro point
    change action freeEmpty ready (morphismSub (first ≫ second)) point =
      action freeEmpty ready (morphismSub second) (action freeEmpty ready (morphismSub first) point)
    rw [morphismSub_composition]
    exact (action_composition freeEmpty ready (morphismSub first) (morphismSub second) point).symm

def source (freeEmpty : environment.free = Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted environment) (sort : String) :
    events freeEmpty ready sort ⟶ semanticPrograms (algebra environment.language) sort where
  app _ := TypeCat.ofHom Point.source
  naturality X Y morphism := by
    apply ConcreteCategory.hom_ext
    intro point
    rfl

noncomputable def target
    (freeEmpty : environment.free = Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted environment)
    (admitted : Admitted environment.language)
    (labels : (environment.language.terms.map (·.label)).Nodup) (sort : String) :
    events freeEmpty ready sort ⟶ semanticPrograms (algebra environment.language) sort where
  app _ := TypeCat.ofHom (targetTerm freeEmpty admitted labels)
  naturality X Y morphism := by
    apply ConcreteCategory.hom_ext
    intro point
    exact targetTerm_natural freeEmpty ready admitted labels (morphismSub morphism) point

theorem source_read
    (freeEmpty : environment.free = Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted environment) (sort : String)
    (X : Base (algebra environment.language)) (point : (events freeEmpty ready sort).obj X) :
    toPattern ((source freeEmpty ready sort).app X point) = toPattern point.source := rfl

theorem target_read
    (freeEmpty : environment.free = Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted environment)
    (admitted : Admitted environment.language)
    (labels : (environment.language.terms.map (·.label)).Nodup) (sort : String)
    (X : Base (algebra environment.language)) (point : (events freeEmpty ready sort).obj X) :
    toPattern ((target freeEmpty ready admitted labels sort).app X point) = point.receipt.target :=
  targetTerm_read freeEmpty admitted labels point

theorem complete_receipt_read
    (freeEmpty : environment.free = Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted environment) {sort : String}
    {X Y : Base (algebra environment.language)} (morphism : X ⟶ Y)
    (point : (events freeEmpty ready sort).obj X) :
    NativeReceiptRechecking.read ((events freeEmpty ready sort).map morphism point).receipt =
      NativeOperationalReceiptTransport.payload (bound X.unop.context) (bound Y.unop.context)
        (NativeBindingRendering.assignment (morphismSub morphism)) (NativeReceiptRechecking.read point.receipt) :=
  action_read freeEmpty ready (morphismSub morphism) point

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingEventPresheaf
