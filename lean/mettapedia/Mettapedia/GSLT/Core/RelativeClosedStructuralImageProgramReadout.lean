import Mettapedia.GSLT.Core.RelativeClosedStructuralImageCoherent
import Mettapedia.CategoryTheory.RelativeClosedConjunctiveProgramModelReadout

/-!+# Complete program readings for the combined named-layer interpretation

An independently supplied program-theory map and a comparison of its base
functor with the independently realized local meanings determine the whole
program map out of the actual modal/structural native presentation. The
generated event object is compared with the original one; both endpoint
equations are earned by the existing program factor construction.

The complete restricted event map and every original program and firing
arrow are recovered. No entire extended interpretation or runtime execution
contract is supplied as a local-model field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedStructuralImageProgramReadout

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory ProgramReductionTheory AuthoredClosedTheory
open RelativeClosedSyntax GeneratedCategory
open RelativeClosedConjunctiveProgram.ModelReadout (factor factor_base)

universe k
variable {source target : Theory.{k,k}} {Index Origins : Type k}
variable {selected : Index → RelativeClosedPositionedModalPresentation.Selection source}
variable {constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source}
variable (model : RelativeClosedStructuralImageLocalModels.LocalModel
  source selected constructors target.closed.Obj)
variable (original : Map source target)
variable (originalBase : model.previous.base ≅ original.closed.functor)

abbrev inclusion := RelativeClosedStructuralImagePresentation.programInclusion source selected constructors
abbrev generated := RelativeClosedStructuralImagePresentation.programTheory source selected constructors

local instance inclusion_event_isIso : IsIso (inclusion (source := source)
    (selected := selected) (constructors := constructors)).reduction :=
  RelativeClosedProgramReductionExtension.complete_reduction_retained source
    (RelativeClosedStructuralImagePresentation.nativeTheory source selected constructors)
    (RelativeClosedStructuralImagePresentation.baseMap source selected constructors)

def interpretation : LambdaTheoryMap (generated (source := source) (selected := selected)
    (constructors := constructors)).closed target.closed where
  functor := model.nativeDiagram
  preservesFiniteLimits := RelativeClosedSyntax.Interpretation.functor_preservesFiniteLimits
    model.nativeModel.meanings model.nativeModel.realization
  preservesExponentials := RelativeClosedSyntax.Interpretation.functor_closed
    model.nativeModel.meanings model.nativeModel.realization

def baseComparison : (inclusion (source := source) (selected := selected)
    (constructors := constructors)).closed.functor ⋙ (interpretation model).functor ≅ original.closed.functor :=
  eqToIso model.base_readback ≪≫ originalBase

def extension : Map (generated (source := source) (selected := selected) (constructors := constructors)) target :=
  factor (inclusion (source := source) (selected := selected) (constructors := constructors))
    (interpretation model) original (baseComparison model original originalBase)

def restrictionComparison : ProgramReductionTheoryIsoClasses.MapIso
    (Map.compose (inclusion (source := source) (selected := selected) (constructors := constructors))
      (extension model original originalBase)) original :=
  factor_base (inclusion (source := source) (selected := selected) (constructors := constructors))
    (interpretation model) original (baseComparison model original originalBase)

theorem complete_restricted_event :
    (baseComparison model original originalBase).hom.app source.Event ≫ original.reduction =
      (extension model original originalBase).closed.functor.map
        (inclusion (source := source) (selected := selected) (constructors := constructors)).reduction ≫
          (extension model original originalBase).reduction :=
  (restrictionComparison model original originalBase).reduction_square

theorem complete_program_comparison :
    (extension model original originalBase).program.hom =
      (baseComparison model original originalBase).hom.app source.program ≫ original.program.hom := by
  have reading := (restrictionComparison model original originalBase).program
  change (baseComparison model original originalBase).hom.app source.program ≫ original.program.hom =
    (extension model original originalBase).closed.functor.map
      (𝟙 ((inclusion (source := source) (selected := selected) (constructors := constructors)).closed.functor.obj
        source.program)) ≫ (extension model original originalBase).program.hom at reading
  rw [(extension model original originalBase).closed.functor.map_id, Category.id_comp] at reading
  exact reading.symm

theorem complete_program_readout {context : source.closed.Obj} (term : context ⟶ source.program) :
    (extension model original originalBase).closed.functor.map
        ((inclusion (source := source) (selected := selected) (constructors := constructors)).closed.functor.map term) ≫
          (extension model original originalBase).program.hom =
      (baseComparison model original originalBase).hom.app context ≫
        (original.closed.functor.map term ≫ original.program.hom) := by
  rw [complete_program_comparison, ← Category.assoc]
  exact (congrArg (fun arrow => arrow ≫ original.program.hom)
    ((baseComparison model original originalBase).hom.naturality term)).trans (Category.assoc _ _ _)

theorem complete_event_readout {context : source.closed.Obj} (event : context ⟶ source.Event) :
    (extension model original originalBase).closed.functor.map
        ((inclusion (source := source) (selected := selected) (constructors := constructors)).closed.functor.map event ≫
          (inclusion (source := source) (selected := selected) (constructors := constructors)).reduction) ≫
            (extension model original originalBase).reduction =
      (baseComparison model original originalBase).hom.app context ≫
        (original.closed.functor.map event ≫ original.reduction) := by
  rw [(extension model original originalBase).closed.functor.map_comp, Category.assoc, ← complete_restricted_event,
    ← Category.assoc]
  exact (congrArg (fun arrow => arrow ≫ original.reduction)
    ((baseComparison model original originalBase).hom.naturality event)).trans (Category.assoc _ _ _)

theorem complete_authored_firing (origin : Index) :
    (extension model original originalBase).closed.functor.map
        (Rule.transport (inclusion (source := source) (selected := selected) (constructors := constructors))
          (selected origin).rule).action ≫ (extension model original originalBase).reduction =
      (baseComparison model original originalBase).hom.app (selected origin).rule.parameters ≫
        (original.closed.functor.map (selected origin).rule.action ≫ original.reduction) :=
  complete_event_readout model original originalBase (selected origin).rule.action

end Mettapedia.GSLT.Core.RelativeClosedStructuralImageProgramReadout
