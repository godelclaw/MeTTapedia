import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedMeaning
import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedLogicalReadout
import Mettapedia.GSLT.Core.RelativeClosedStructuralImageProgramControls

/-!
# Complete named quantification with independent numeric controls

The target keeps its independently renamed successor relation. Both old
program endpoints and the complete firing pass through the combined named
interpretation and quantified completion. Forgetting the program comparison
gives an incorrect reduct. A quantifier-created arrow itself receives both
quantifiers and their complete interpretation squares.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory ProgramReductionTheory AuthoredClosedTheory
open RelativeClosedPositionedModalControlData
open RelativeClosedNamedQuantifiedPresentation

abbrev source := RelativeClosedStructuralImageProgramControls.source
abbrev constructors := RelativeClosedStructuralImageProgramControls.constructors
abbrev nativeLogic := RelativeClosedStructuralImageProgramControls.nativeLogic
abbrev original := RelativeClosedStructuralImageProgramControls.original

def target : QuantifiedProgramTheory.{1} where
  programTheory := RelativeClosedStructuralImageProgramControls.target
  operations := HigherOrderInternalPredicateQuantifiedObject.operations nativeLogic

abbrev targetImplication := HigherOrderInternalPredicateImplication.qualification nativeLogic

def independentBase : source.closed.Obj ⥤ target.programTheory.closed.Obj := original.closed.functor

private instance base_finite : PreservesFiniteLimits independentBase :=
  original.closed.preservesFiniteLimits

private instance base_closed : MonoidalClosedFunctor independentBase :=
  original.closed.preservesExponentials

abbrev model := RelativeClosedNamedQuantifiedMeaning.localModel source target selected constructors
  independentBase targetImplication

abbrev readings := RelativeClosedNamedQuantifiedMeaning.predicateReadings source target selected constructors
  independentBase targetImplication

abbrev actual := RelativeClosedNamedQuantifiedModels.extension model readings original (Iso.refl _)
abbrev recovered := RelativeClosedNamedQuantifiedModels.sourceComparison model readings original (Iso.refl _)
abbrev unit := programInclusion source selected constructors

def programReading {context : source.closed.Obj} (term : context ⟶ source.program) :
    context ⟶ target.programTheory.program :=
  recovered.comparison.inv.app context ≫ actual.functor.map (unit.closed.functor.map term) ≫
    (Map.compose unit actual.underlying).program.hom

theorem complete_program_reading {context : source.closed.Obj} (term : context ⟶ source.program) :
    programReading term = original.closed.functor.map term ≫ original.program.hom := by
  have carried := RelativeClosedNamedQuantifiedModels.complete_program_readout
    model readings original (Iso.refl _) term
  exact (congrArg (fun arrow => recovered.comparison.inv.app context ≫ arrow) carried).trans
    (recovered.comparison.inv_hom_id_app_assoc _ _)

def eventReading {context : source.closed.Obj} (event : context ⟶ source.Event) :
    context ⟶ target.programTheory.Event :=
  recovered.comparison.inv.app context ≫ actual.functor.map
    (unit.closed.functor.map event ≫ unit.reduction) ≫ actual.reduction

theorem complete_event_reading {context : source.closed.Obj} (event : context ⟶ source.Event) :
    eventReading event = original.closed.functor.map event ≫ original.reduction := by
  have carried := RelativeClosedNamedQuantifiedModels.complete_event_readout
    model readings original (Iso.refl _) event
  exact (congrArg (fun arrow => recovered.comparison.inv.app context ≫ arrow) carried).trans
    (recovered.comparison.inv_hom_id_app_assoc _ _)

theorem entire_firing : eventReading rule.action =
    rule.action ≫ PositionedRewriteProgramComparisonControls.eventComparison.hom :=
  complete_event_reading rule.action

theorem entire_source : programReading rule.left = PositionedRewriteProgramComparisonControls.sourceReading :=
  (complete_program_reading rule.left).trans
    PositionedRewriteProgramComparisonControls.entire_source_reading.symm

theorem entire_reduct : programReading rule.right = PositionedRewriteProgramComparisonControls.reductReading :=
  (complete_program_reading rule.right).trans
    PositionedRewriteProgramComparisonControls.entire_reduct_reading.symm

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

theorem full_constructor_reading : programReading QuantifiedStructuralActionControls.Generated.constructor =
    QuantifiedStructuralActionControls.Generated.independentlySuppliedConstructor :=
  (complete_program_reading QuantifiedStructuralActionControls.Generated.constructor).trans
    QuantifiedStructuralActionControls.Generated.complete_independent_constructor_reading

def arrowReading
    {before after : (namedTheory source selected constructors).closed.Obj} (arrow : before ⟶ after) :=
  (RelativeClosedNamedQuantifiedModels.restrictionComparison model readings original (Iso.refl _)).comparison.inv.app before ≫
    actual.functor.map ((unitMap source selected constructors).functor.map arrow) ≫
      (RelativeClosedNamedQuantifiedModels.restrictionComparison model readings original (Iso.refl _)).comparison.hom.app after

theorem complete_arrow_reading
    {before after : (namedTheory source selected constructors).closed.Obj} (arrow : before ⟶ after) :
    arrowReading arrow = model.nativeDiagram.map arrow :=
  RelativeClosedNamedQuantifiedModels.complete_arrow_read model readings original (Iso.refl _) arrow

theorem entire_constructor_function (origin : Origin) :
    HEq (arrowReading (RelativeClosedSyntax.GeneratedCategory.classOf
      ((RelativeClosedStructuralImagePresentation.nativeInclusion source selected constructors).rawArrow
        (RelativeClosedStructuralImagePresentation.namedRaw source selected constructors origin))))
      (model.constructorValues origin).arrow :=
  (heq_of_eq (complete_arrow_reading _)).trans (model.native_named_image origin)

theorem complete_named_constructor (origin : Origin) :
    constructorArrow source selected constructors origin = constructorBody source selected constructors origin :=
  constructor_definition source selected constructors origin

theorem complete_named_modality (origin : Option Origin) :
    modalArrow source selected constructors origin = modalBody source selected constructors origin :=
  modal_definition source selected constructors origin

abbrev completeTheory := completed source selected constructors

theorem implication_in_every_new_context {context : completeTheory.programTheory.closed.Obj}
    (first second : completeTheory.operations.predicates.Fiber context) :
    actual.conjunctive.declarations.image
        ((completeImplication source selected constructors).implies completeTheory.operations.predicates first second) =
      targetImplication.implies target.operations.predicates
        (actual.conjunctive.declarations.image first) (actual.conjunctive.declarations.image second) :=
  RelativeClosedQuantified.Implication.complete_candidate_supplied
    (source := (namedTheory source selected constructors).conjunctive) (target := target.quantified)
    (implication source selected constructors) actual.conjunctive targetImplication first second

def bornRoute := (completeTheory.operations.universal
  (CartesianMonoidalCategory.toUnit completeTheory.operations.predicates.proposition)).operation

theorem both_operations_on_quantifier_created_arrow :
    InternalPredicateFunctionObjectMaps.arrowImage actual.conjunctive.declarations
        (completeTheory.operations.universal bornRoute).operation =
      (target.operations.universal (actual.functor.map bornRoute)).operation ∧
    InternalPredicateFunctionObjectMaps.arrowImage actual.conjunctive.declarations
        (completeTheory.operations.existential bornRoute).operation =
      (target.operations.existential (actual.functor.map bornRoute)).operation :=
  both_quantifiers_on_every_arrow actual bornRoute

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedControls
