import Mettapedia.GSLT.Core.RelativeClosedStructuralImageProgramReadout
import Mettapedia.GSLT.Core.RelativeClosedStructuralImageProgramUniversality
import Mettapedia.GSLT.Core.QuantifiedStructuralActionControls

/-!
# Combined named layers with an independent numeric program relation

The numeric source retains the genuine successor graph, positioned firing
and two-input constructor. Its complete named-layer interpretation is
independently realized in the native predicate doctrine. The supplied
target relation exchanges program values zero and one. All original
program and event readings pass through the earned program comparison.

The whole original firing is retained, with source one and reduct zero at
the zero/zero input. Omitting the program comparison is rejected. Complete
coherent uniqueness is calibrated on the independently realized model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedStructuralImageProgramControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory ProgramReductionTheory AuthoredClosedTheory
open RelativeClosedPositionedModalControlData
open RelativeClosedStructuralImageProgramReadout

abbrev source := theory
abbrev target := PositionedRewriteProgramComparisonControls.renamedTheory
abbrev constructors := RelativeClosedStructuralImageControls.constructors
abbrev nativeLogic := RelativeClosedQuantifiedAdjunctionControls.nativeLogic
abbrev original := PositionedRewriteProgramComparisonControls.programMap

private instance native_base_finite : PreservesFiniteLimits original.closed.functor :=
  original.closed.preservesFiniteLimits

private instance native_base_closed : MonoidalClosedFunctor original.closed.functor :=
  original.closed.preservesExponentials

def model : RelativeClosedStructuralImageLocalModels.LocalModel source selected constructors target.closed.Obj :=
  RelativeClosedStructuralImageLocalModels.native source selected constructors target.closed.Obj
    original.closed.functor nativeLogic

def originalBase : model.previous.base ≅ original.closed.functor := Iso.refl _

abbrev actual := extension model original originalBase
abbrev recovered := baseComparison model original originalBase
abbrev unit := RelativeClosedStructuralImagePresentation.programInclusion source selected constructors

def programReading {context : source.closed.Obj} (term : context ⟶ source.program) : context ⟶ target.program :=
  recovered.inv.app context ≫ actual.closed.functor.map (unit.closed.functor.map term) ≫ actual.program.hom

theorem complete_program_reading {context : source.closed.Obj} (term : context ⟶ source.program) :
    programReading term = original.closed.functor.map term ≫ original.program.hom := by
  change recovered.inv.app context ≫
    (actual.closed.functor.map (unit.closed.functor.map term) ≫ actual.program.hom) = _
  rw [complete_program_readout model original originalBase]
  exact recovered.inv_hom_id_app_assoc context _

def eventReading {context : source.closed.Obj} (event : context ⟶ source.Event) : context ⟶ target.Event :=
  recovered.inv.app context ≫
    actual.closed.functor.map (unit.closed.functor.map event ≫ unit.reduction) ≫ actual.reduction

theorem complete_event_reading {context : source.closed.Obj} (event : context ⟶ source.Event) :
    eventReading event = original.closed.functor.map event ≫ original.reduction := by
  change recovered.inv.app context ≫
    (actual.closed.functor.map (unit.closed.functor.map event ≫ unit.reduction) ≫ actual.reduction) = _
  rw [complete_event_readout model original originalBase]
  exact recovered.inv_hom_id_app_assoc context _

theorem entire_actual_firing : eventReading rule.action =
    rule.action ≫ PositionedRewriteProgramComparisonControls.eventComparison.hom :=
  complete_event_reading rule.action

theorem entire_source_reading : programReading rule.left =
    PositionedRewriteProgramComparisonControls.sourceReading :=
  (complete_program_reading rule.left).trans
    PositionedRewriteProgramComparisonControls.entire_source_reading.symm

theorem entire_target_reading : programReading rule.right =
    PositionedRewriteProgramComparisonControls.reductReading :=
  (complete_program_reading rule.right).trans
    PositionedRewriteProgramComparisonControls.entire_reduct_reading.symm

theorem actual_firing_source : eventReading rule.action ≫ target.source = programReading rule.left := by
  rw [complete_event_reading, Category.assoc, original.source, ← Category.assoc,
    ← original.closed.functor.map_comp, rule.source, complete_program_reading]

theorem actual_firing_target : eventReading rule.action ≫ target.target = programReading rule.right := by
  rw [complete_event_reading, Category.assoc, original.target, ← Category.assoc,
    ← original.closed.functor.map_comp, rule.target, complete_program_reading]

theorem native_zero_pair_source :
    base.map (programReading rule.left) ((Types.binaryProductIso Nat Nat).inv (0, 0)) = (1 : Nat) :=
  (congrArg (fun arrow : rule.parameters ⟶ program =>
    base.map arrow ((Types.binaryProductIso Nat Nat).inv (0, 0))) entire_source_reading).trans
      PositionedRewriteProgramComparisonControls.actual_zero_pair_source

theorem native_zero_pair_target :
    base.map (programReading rule.right) ((Types.binaryProductIso Nat Nat).inv (0, 0)) = (0 : Nat) :=
  (congrArg (fun arrow : rule.parameters ⟶ program =>
    base.map arrow ((Types.binaryProductIso Nat Nat).inv (0, 0))) entire_target_reading).trans
      PositionedRewriteProgramComparisonControls.actual_zero_pair_reduct

theorem unrenamed_reduct_is_rejected : programReading rule.right ≠ rule.right := by
  intro same
  exact PositionedRewriteProgramComparisonControls.outgoing_comparison_cannot_be_omitted
    (entire_target_reading.symm.trans same)

theorem complete_constructor_reading :
    programReading QuantifiedStructuralActionControls.Generated.constructor =
      QuantifiedStructuralActionControls.Generated.independentlySuppliedConstructor :=
  (complete_program_reading QuantifiedStructuralActionControls.Generated.constructor).trans
    QuantifiedStructuralActionControls.Generated.complete_independent_constructor_reading

theorem complete_old_modal_diagram :
    ((RelativeClosedStructuralImagePresentation.inclusion source selected constructors).functor ⋙
      (RelativeClosedStructuralImagePresentation.nativeInclusion source selected constructors).functor) ⋙
        actual.closed.functor = model.previous.diagram := by
  change ((RelativeClosedStructuralImagePresentation.inclusion source selected constructors).functor ⋙
    (RelativeClosedStructuralImagePresentation.nativeInclusion source selected constructors).functor) ⋙
      model.nativeDiagram = _
  rw [Functor.assoc, model.original_diagram_readback, model.previous_diagram_readback]

theorem complete_native_structural_name (origin : Origin) :
    HEq (actual.closed.functor.map (RelativeClosedSyntax.GeneratedCategory.classOf
      ((RelativeClosedStructuralImagePresentation.nativeInclusion source selected constructors).rawArrow
        (RelativeClosedStructuralImagePresentation.namedRaw source selected constructors origin))))
      (model.constructorValues origin).arrow := model.native_named_image origin

def completeComparison := RelativeClosedStructuralImageCoherent.comparison model model.nativeDiagram
  (RelativeClosedStructuralImageCoherent.canonicalImages model)
  (RelativeClosedStructuralImageCoherent.canonical_admitted model)

theorem canonical_comparison_is_calibrated : completeComparison = Iso.refl model.nativeDiagram :=
  RelativeClosedStructuralImageCoherent.canonical_comparison_refl model

theorem every_primitive_admitted_complete_cell_agrees (cell : model.nativeDiagram ⟶ model.nativeDiagram)
    (localComponents : RelativeClosedStructuralImageCoherent.CellAdmission model model.nativeDiagram
      (RelativeClosedStructuralImageCoherent.canonicalImages model) cell) :
    cell = completeComparison.hom :=
  RelativeClosedStructuralImageCoherent.admitted_cell_unique model model.nativeDiagram
    (RelativeClosedStructuralImageCoherent.canonicalImages model)
    (RelativeClosedStructuralImageCoherent.canonical_admitted model) cell localComponents

theorem canonical_program_square :
    (RelativeClosedStructuralImageCoherent.canonicalImages model).base.hom.app source.program ≫
        (originalBase.hom.app source.program ≫ original.program.hom) = actual.program.hom := by
  have component := RelativeClosedStructuralImageCoherent.complete_base_component model model.nativeDiagram
    (RelativeClosedStructuralImageCoherent.canonicalImages model)
    (RelativeClosedStructuralImageCoherent.canonical_admitted model) source.program
  rw [RelativeClosedStructuralImageCoherent.canonical_comparison_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp] at component
  rw [← component, complete_program_comparison model original originalBase]
  simp only [baseComparison, Iso.trans_hom, NatTrans.comp_app, Category.assoc]

def completeProgramComparison := RelativeClosedStructuralImageProgramUniversality.comparison
  model original originalBase actual (RelativeClosedStructuralImageCoherent.canonicalImages model)
    (RelativeClosedStructuralImageCoherent.canonical_admitted model) canonical_program_square

theorem canonical_program_comparison_is_calibrated :
    completeProgramComparison.comparison = Iso.refl actual.closed.functor :=
  RelativeClosedStructuralImageCoherent.canonical_comparison_refl model

theorem every_primitive_admitted_program_comparison_agrees
    (change : ProgramReductionTheoryIsoClasses.MapIso actual actual)
    (localComponents : RelativeClosedStructuralImageCoherent.CellAdmission model actual.closed.functor
      (RelativeClosedStructuralImageCoherent.canonicalImages model) change.comparison.hom) :
    change = completeProgramComparison :=
  RelativeClosedStructuralImageProgramUniversality.admitted_comparison_unique
    model original originalBase actual (RelativeClosedStructuralImageCoherent.canonicalImages model)
      (RelativeClosedStructuralImageCoherent.canonical_admitted model) canonical_program_square change localComponents

end Mettapedia.GSLT.Core.RelativeClosedStructuralImageProgramControls
