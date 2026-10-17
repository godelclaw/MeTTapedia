import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeSemantics
import Mettapedia.OSLF.Syntax.FreePresheafEventImage
import Mettapedia.CategoryTheory.AsSmallYoneda
import Mettapedia.CategoryTheory.ProgramReductionTheoryIsoClasses
import Mettapedia.GSLT.Core.RelativeClosedStructuralImagePresentation

/-!
# Actual authored carrier and receipt reduction theory

All generated carrier meanings enter one tagged program presheaf. Authored
receipt families remain a separate tagged event presheaf. Their actual source
and specified target determine the endpoint-image reduction subobject. The
original constructor arguments and arrows supply the structural origins;
the retained receipt families supply the modal rule diagrams.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.AuthoredProgramReduction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory
open Mettapedia.GSLT.Core
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.Binding
open CurriedBindingLanguage

variable (installed : AuthoredPipeline.Installed)

abbrev language := (BindingPipeline.plan installed.operational.generated).snapshot.language
abbrev Base := IntrinsicScopedConditionalPresheaf.Base (algebra (language installed))
abbrev Presheaves := Base installed ⥤ Type
abbrev Category := AsSmallYoneda.Small (Presheaves installed)
abbrev up := AsSmallYoneda.up (Presheaves installed)

/-- Every carrier has its own tag, including genuine function carriers. -/
def program : Presheaves installed where
  obj X := Σ carrier : NativeSignature.Carrier (language installed), (meaning carrier).obj X
  map f := TypeCat.ofHom fun value => ⟨value.1, (meaning value.1).map f value.2⟩
  map_id X := by
    apply ConcreteCategory.hom_ext
    rintro ⟨carrier, value⟩
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨carrier, value⟩
    simp

def carrierInjection (carrier : NativeSignature.Carrier (language installed)) :
    meaning carrier ⟶ program installed where
  app X := TypeCat.ofHom fun value =>
    (⟨carrier, value⟩ : Σ carrier : NativeSignature.Carrier (language installed), (meaning carrier).obj X)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro value
    rfl

theorem carrier_injection_injective (carrier : NativeSignature.Carrier (language installed))
    (X : Base installed) : Function.Injective ((carrierInjection installed carrier).app X) :=
  by
    change Function.Injective
      (@Sigma.mk (NativeSignature.Carrier (language installed)) (fun c => (meaning c).obj X) carrier)
    exact sigma_mk_injective

/-- Catalogue indices are retained even when complete receipts have equal endpoints. -/
def retainedEvents : Presheaves installed where
  obj X := Σ index : Fin installed.operational.modal.length,
    (installed.computedDiagram.events index).obj X
  map f := TypeCat.ofHom fun event =>
    ⟨event.1, (installed.computedDiagram.events event.1).map f event.2⟩
  map_id X := by
    apply ConcreteCategory.hom_ext
    rintro ⟨index, event⟩
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨index, event⟩
    simp

def eventInjection (index : Fin installed.operational.modal.length) :
    installed.computedDiagram.events index ⟶ retainedEvents installed where
  app X := TypeCat.ofHom fun event =>
    (⟨index, event⟩ : Σ index : Fin installed.operational.modal.length,
      (installed.computedDiagram.events index).obj X)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro event
    rfl

def endpoint
    (component : ∀ index : Fin installed.operational.modal.length,
      installed.computedDiagram.events index ⟶ meaning installed.operational.modal[index].program) :
    retainedEvents installed ⟶ program installed where
  app X := TypeCat.ofHom fun event =>
    ⟨installed.operational.modal[event.1].program,
      (component event.1).app X event.2⟩
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨index, event⟩
    change (⟨installed.operational.modal[index].program,
      (component index).app Y
        ((installed.computedDiagram.events index).map f event)⟩ : (program installed).obj Y) =
      ⟨installed.operational.modal[index].program,
        (meaning installed.operational.modal[index].program).map f
          ((component index).app X event)⟩
    exact congrArg (Sigma.mk installed.operational.modal[index].program)
      ((component index).naturality_apply f event)

def source : retainedEvents installed ⟶ program installed :=
  endpoint installed fun index => installed.computedDiagram.projection (.source index)

def target : retainedEvents installed ⟶ program installed :=
  endpoint installed fun index => installed.computedDiagram.projection (.target index)

def graph : FreePresheafEventExtension.Graph (program installed) where
  edge := retainedEvents installed
  source := source installed
  target := target installed

def endpointImage : Subfunctor (FunctorToTypes.prod (program installed) (program installed)) :=
  FreePresheafEventImage.endpointImage (graph installed)

theorem event_image_iff (X : Base installed)
    (first last : (program installed).obj X) :
    (first, last) ∈ (endpointImage installed).obj X ↔
      ∃ (index : Fin installed.operational.modal.length)
        (event : (installed.computedDiagram.events index).obj X),
        (carrierInjection installed installed.operational.modal[index].program).app X
            ((installed.computedDiagram.projection (.source index)).app X event) = first ∧
        (carrierInjection installed installed.operational.modal[index].program).app X
            ((installed.computedDiagram.projection (.target index)).app X event) = last := by
  rw [endpointImage, FreePresheafEventImage.mem_endpointImage_iff]
  constructor
  · rintro ⟨⟨index, event⟩, before, after⟩
    exact ⟨index, event, before, after⟩
  · rintro ⟨index, event, before, after⟩
    exact ⟨⟨index, event⟩, before, after⟩

/-- The actual equivalence raises the hom universe without altering a carrier. -/
def pairIso :
    (up installed).obj (program installed) ⨯ (up installed).obj (program installed) ≅
      (up installed).obj (FunctorToTypes.prod (program installed) (program installed)) :=
  (asIso (prodComparison (up installed) (program installed) (program installed))).symm ≪≫
    (up installed).mapIso (FunctorToTypes.binaryProductIso (program installed) (program installed))

def imageArrow : (up installed).obj (endpointImage installed).toFunctor ⟶
    (up installed).obj (program installed) ⨯ (up installed).obj (program installed) :=
  (up installed).map (endpointImage installed).ι ≫ (pairIso installed).inv

instance imageArrow_mono : Mono (imageArrow installed) := by
  unfold imageArrow
  infer_instance

abbrev sourceTheory : ProgramReductionTheory.Theory.{1,1} := by
  letI : Mono (imageArrow installed) := imageArrow_mono installed
  exact {
    closed := LambdaTheory.ofCategory (Category installed)
    program := (up installed).obj (program installed)
    reduction := Subobject.mk (imageArrow installed) }

abbrev sourceClass := ProgramReductionTheoryIsoClasses.of (sourceTheory installed)

def imageAction : (up installed).obj (retainedEvents installed) ⟶ (sourceTheory installed).Event :=
  (up installed).map (Subfunctor.toRange (FreePresheafEventImage.endpointMap (graph installed))) ≫
    (Subobject.underlyingIso (imageArrow installed)).inv

theorem imageAction_arrow :
    imageAction installed ≫ (sourceTheory installed).reduction.arrow =
      (up installed).map (FreePresheafEventImage.endpointMap (graph installed)) ≫
        (pairIso installed).inv := by
  unfold imageAction
  rw [Category.assoc, Subobject.underlyingIso_arrow]
  unfold imageArrow
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

theorem pairIso_inv_fst :
    (pairIso installed).inv ≫ prod.fst =
      (up installed).map (FunctorToTypes.prod.fst (F := program installed) (G := program installed)) := by
  change ((up installed).map (FunctorToTypes.binaryProductIso (program installed) (program installed)).inv ≫
    prodComparison (up installed) (program installed) (program installed)) ≫ prod.fst = _
  rw [Category.assoc, prodComparison_fst, ← Functor.map_comp,
    FunctorToTypes.binaryProductIso_inv_comp_fst]

theorem pairIso_inv_snd :
    (pairIso installed).inv ≫ prod.snd =
      (up installed).map (FunctorToTypes.prod.snd (F := program installed) (G := program installed)) := by
  change ((up installed).map (FunctorToTypes.binaryProductIso (program installed) (program installed)).inv ≫
    prodComparison (up installed) (program installed) (program installed)) ≫ prod.snd = _
  rw [Category.assoc, prodComparison_snd, ← Functor.map_comp,
    FunctorToTypes.binaryProductIso_inv_comp_snd]

theorem imageAction_source :
    imageAction installed ≫ (sourceTheory installed).source = (up installed).map (source installed) := by
  change imageAction installed ≫ ((sourceTheory installed).reduction.arrow ≫ prod.fst) = _
  rw [← Category.assoc, imageAction_arrow, Category.assoc, pairIso_inv_fst,
    ← Functor.map_comp]
  rfl

theorem imageAction_target :
    imageAction installed ≫ (sourceTheory installed).target = (up installed).map (target installed) := by
  change imageAction installed ≫ ((sourceTheory installed).reduction.arrow ≫ prod.snd) = _
  rw [← Category.assoc, imageAction_arrow, Category.assoc, pairIso_inv_snd,
    ← Functor.map_comp]
  rfl

def constructorOrigin (constructor : installed.operational.declarations.Constructor) :
    RelativeClosedStructuralImagePresentation.Constructor (sourceTheory installed) where
  arguments := (up installed).obj
    (carrierScope installed.operational.declarations.headers[constructor].parameters).1
  term := (up installed).map
    (constructorMap installed.operational.nativeMeaning_admitted
      installed.operational.declarations.headers[constructor]
      (installed_header_correct installed.operational.declarations constructor) ≫
        carrierInjection installed (.sort installed.operational.declarations.headers[constructor].result))

theorem constructor_arrow_read (constructor : installed.operational.declarations.Constructor)
    (X : Base installed)
    (arguments : (carrierScope installed.operational.declarations.headers[constructor].parameters).1.obj X) :
    ((constructorOrigin installed constructor).term.down).app X arguments =
      (carrierInjection installed (.sort installed.operational.declarations.headers[constructor].result)).app X
        ((constructorMap installed.operational.nativeMeaning_admitted
          installed.operational.declarations.headers[constructor]
          (installed_header_correct installed.operational.declarations constructor)).app X arguments) := rfl

def modalRule (index : Fin installed.operational.modal.length) :
    AuthoredClosedTheory.Rule (sourceTheory installed) where
  parameters := (up installed).obj (installed.computedDiagram.events index)
  left := (up installed).map
    (installed.computedDiagram.projection (.source index) ≫
      carrierInjection installed installed.operational.modal[index].program)
  right := (up installed).map
    (installed.computedDiagram.projection (.target index) ≫
      carrierInjection installed installed.operational.modal[index].program)
  action := (up installed).map (eventInjection installed index) ≫ imageAction installed
  source := by
    rw [Category.assoc, imageAction_source, ← Functor.map_comp]
    rfl
  target := by
    rw [Category.assoc, imageAction_target, ← Functor.map_comp]
    rfl

theorem modal_source_read (index : Fin installed.operational.modal.length)
    (X : Base installed) (event : (installed.computedDiagram.events index).obj X) :
    ((modalRule installed index).left.down).app X event =
      (carrierInjection installed installed.operational.modal[index].program).app X
        ((installed.computedDiagram.projection (.source index)).app X event) := rfl

theorem modal_target_read (index : Fin installed.operational.modal.length)
    (X : Base installed) (event : (installed.computedDiagram.events index).obj X) :
    ((modalRule installed index).right.down).app X event =
      (carrierInjection installed installed.operational.modal[index].program).app X
        ((installed.computedDiagram.projection (.target index)).app X event) := rfl

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.AuthoredProgramReduction
