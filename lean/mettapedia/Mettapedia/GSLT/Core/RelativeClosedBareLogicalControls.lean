import Mettapedia.GSLT.Core.RelativeClosedBareLogicalReadout
import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedControls

/-!
# Independent renamed-relation controls for the bare logical extension

The source has the actual successor relation and a rewrite retaining two
numeric inputs. The independently supplied target exchanges zero and one.
The complete bare extension recovers the renamed firing, rejects the
unrenamed reduct and retains every admitted constructor function. A second
original interpretation repacks every context with the terminal object;
its compatible comparison is extended without additional primitive
admission.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedBareLogical.Controls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory ProgramReductionTheory AuthoredClosedTheory
open RelativeClosedPositionedModalControlData

abbrev source := ProgramReductionTheoryIsoClasses.of RelativeClosedNamedQuantifiedControls.source

def target : QuantifiedImplicativeProgramTheory.{1} where
  quantified := RelativeClosedNamedQuantifiedControls.target
  implication := RelativeClosedNamedQuantifiedControls.targetImplication

abbrev original := RelativeClosedNamedQuantifiedControls.original
abbrev actual := extension source target original
abbrev recovered := extensionRestriction source target original

def programReading {context : source.original.closed.Obj} (term : context ⟶ source.original.program) :=
  Readout.programReading source target original term

def eventReading {context : source.original.closed.Obj} (event : context ⟶ source.original.Event) :=
  Readout.eventReading source target original event

theorem entire_source : programReading rule.left = PositionedRewriteProgramComparisonControls.sourceReading :=
  (Readout.complete_program_reading source target original rule.left).trans
    PositionedRewriteProgramComparisonControls.entire_source_reading.symm

theorem entire_reduct : programReading rule.right = PositionedRewriteProgramComparisonControls.reductReading :=
  (Readout.complete_program_reading source target original rule.right).trans
    PositionedRewriteProgramComparisonControls.entire_reduct_reading.symm

theorem entire_firing : eventReading rule.action =
    rule.action ≫ PositionedRewriteProgramComparisonControls.eventComparison.hom :=
  Readout.complete_event_reading source target original rule.action

theorem actual_zero_pair_source :
    base.map (programReading rule.left) ((Types.binaryProductIso Nat Nat).inv (0, 0)) = (1 : Nat) :=
  (congrArg (fun arrow : rule.parameters ⟶ program =>
    base.map arrow ((Types.binaryProductIso Nat Nat).inv (0, 0))) entire_source).trans
      PositionedRewriteProgramComparisonControls.actual_zero_pair_source

theorem actual_zero_pair_reduct :
    base.map (programReading rule.right) ((Types.binaryProductIso Nat Nat).inv (0, 0)) = (0 : Nat) :=
  (congrArg (fun arrow : rule.parameters ⟶ program =>
    base.map arrow ((Types.binaryProductIso Nat Nat).inv (0, 0))) entire_reduct).trans
      PositionedRewriteProgramComparisonControls.actual_zero_pair_reduct

theorem incorrect_unrenamed_reduct_rejected : programReading rule.right ≠ rule.right := by
  intro same
  exact PositionedRewriteProgramComparisonControls.outgoing_comparison_cannot_be_omitted
    (entire_reduct.symm.trans same)

theorem full_two_input_constructor : programReading QuantifiedStructuralActionControls.Generated.constructor =
    QuantifiedStructuralActionControls.Generated.independentlySuppliedConstructor :=
  (Readout.complete_program_reading source target original QuantifiedStructuralActionControls.Generated.constructor).trans
    QuantifiedStructuralActionControls.Generated.complete_independent_constructor_reading

theorem entire_constructor_function
    (origin : RelativeClosedStructuralImagePresentation.Constructor source.original) :
    HEq (Readout.arrowReading source target original (RelativeClosedSyntax.GeneratedCategory.classOf
      ((RelativeClosedStructuralImagePresentation.nativeInclusion source.original
        (selections source) (constructors source)).rawArrow
        (RelativeClosedStructuralImagePresentation.namedRaw source.original
          (selections source) (constructors source) origin))))
      ((Readout.model source target original).constructorValues origin).arrow :=
  Readout.entire_constructor_function source target original origin

theorem complete_selected_firing :
    actual.functor.map (Rule.transport (unitMap source) selection.rule).action ≫ actual.reduction =
      recovered.comparison.hom.app selection.rule.parameters ≫
        (original.closed.functor.map selection.rule.action ≫ original.reduction) :=
  Readout.entire_authored_firing source target original selection

def repackedFunctor : source.original.closed.Obj ⥤ target.quantified.programTheory.closed.Obj :=
  original.closed.functor.copyObj
    (fun context => original.closed.functor.obj context ⊗ (𝟙_ target.quantified.programTheory.closed.Obj))
    (fun context => (ρ_ (original.closed.functor.obj context)).symm)

def repacking : original.closed.functor ≅ repackedFunctor :=
  original.closed.functor.isoCopyObj _ _

def repacked : Map source.original target.quantified.programTheory :=
  Map.ofFunctorIso original repacking

def originalComparison : ProgramReductionTheoryIsoClasses.MapIso original repacked :=
  Map.compatibleComparison original repacking

def repackedActual := extension source target repacked

def independentCompleteComparison : QuantifiedProgramTheory.MapIso actual repackedActual :=
  RelativeClosedNamedQuantifiedRestriction.completeComparisonWithOriginal target actual repacked
    (recovered.trans originalComparison)

theorem full_repacked_context (context : source.original.closed.Obj) :
    repacked.closed.functor.obj context =
      original.closed.functor.obj context ⊗ (𝟙_ target.quantified.programTheory.closed.Obj) := rfl

theorem repacked_complete_event :
    independentCompleteComparison.comparison.hom.app (freeObject source).quantified.programTheory.Event ≫
      repackedActual.reduction = actual.reduction :=
  independentCompleteComparison.underlying.reduction_square

theorem extension_classes_agree : QuantifiedImplicativeProgramTheory.classOf actual =
    QuantifiedImplicativeProgramTheory.classOf repackedActual :=
  Quotient.sound ⟨independentCompleteComparison⟩

theorem bare_classes_agree : ProgramReductionTheoryIsoClasses.classOf original =
    ProgramReductionTheoryIsoClasses.classOf repacked := Quotient.sound ⟨originalComparison⟩

theorem complete_bare_roundtrip :
    homEquiv source target (QuantifiedImplicativeProgramTheory.classOf actual) =
      ProgramReductionTheoryIsoClasses.classOf original :=
  restrict_extend source target (ProgramReductionTheoryIsoClasses.classOf original)

def quantifierCreatedArrow :=
  ((freeObject (Construction.firstExtension source)).quantified.operations.universal
    (freeObject (Construction.firstExtension source)).quantified.programTheory.target).operation

theorem actual_quantifier_created_arrow_folds :
    InternalPredicateFunctionObjectMaps.arrowImage (Construction.multiplicationMap source).conjunctive.declarations
      ((freeObject (Construction.firstExtension source)).quantified.operations.universal quantifierCreatedArrow).operation =
      ((freeObject source).quantified.operations.universal
        ((Construction.multiplicationMap source).functor.map quantifierCreatedArrow)).operation ∧
    InternalPredicateFunctionObjectMaps.arrowImage (Construction.multiplicationMap source).conjunctive.declarations
      ((freeObject (Construction.firstExtension source)).quantified.operations.existential quantifierCreatedArrow).operation =
      ((freeObject source).quantified.operations.existential
        ((Construction.multiplicationMap source).functor.map quantifierCreatedArrow)).operation :=
  ⟨Construction.folds_universal source quantifierCreatedArrow,
    Construction.folds_existential source quantifierCreatedArrow⟩

end Mettapedia.GSLT.Core.RelativeClosedBareLogical.Controls
