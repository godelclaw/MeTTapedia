import Mettapedia.GSLT.Core.RelativeClosedBareLogicalMonad

/-!
# Complete named-operation and firing readouts from the bare extension

Every original program map constructs an independent target interpretation.
Its compatible comparisons recover all old program and event sections,
every arrow of the named presentation, and each complete constructor
function. The source catalog contains every admitted positioned rule and
constructor; no primitive interpretation is supplied by the caller.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedBareLogical.Readout

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open ProgramReductionTheory AuthoredClosedTheory
open RelativeClosedGeneratedQuantifier.SourceOperations

universe k
variable (source : ProgramReductionTheoryIsoClasses.{k}) (target : QuantifiedImplicativeProgramTheory.{k})
variable (original : Map source.original target.quantified.programTheory)

def model := @RelativeClosedNamedQuantifiedMeaning.localModel source.original target.quantified
  (RelativeClosedPositionedModalPresentation.Selection source.original)
  (RelativeClosedStructuralImagePresentation.Constructor source.original)
  (selections source) (constructors source) original.closed.functor
  original.closed.preservesFiniteLimits original.closed.preservesExponentials target.implication

theorem readings : PredicateReadings
    (RelativeClosedNamedQuantifiedPresentation.language source.original (selections source) (constructors source))
    (RelativeClosedNamedQuantifiedPresentation.truth source.original (selections source) (constructors source))
    (model source target original).nativeModel target.quantified.operations.predicates :=
  @RelativeClosedNamedQuantifiedMeaning.predicateReadings source.original target.quantified
    (RelativeClosedPositionedModalPresentation.Selection source.original)
    (RelativeClosedStructuralImagePresentation.Constructor source.original)
    (selections source) (constructors source) original.closed.functor
    original.closed.preservesFiniteLimits original.closed.preservesExponentials target.implication

def recovered := extensionRestriction source target original

def programReading {context : source.original.closed.Obj} (term : context ⟶ source.original.program) :=
  (recovered source target original).comparison.inv.app context ≫
    (extension source target original).functor.map ((unitMap source).closed.functor.map term) ≫
      (restriction source target (extension source target original)).program.hom

theorem complete_program_reading {context : source.original.closed.Obj} (term : context ⟶ source.original.program) :
    programReading source target original term = original.closed.functor.map term ≫ original.program.hom :=
  (recovered source target original).complete_program_readout term

def eventReading {context : source.original.closed.Obj} (event : context ⟶ source.original.Event) :=
  (recovered source target original).comparison.inv.app context ≫
    (extension source target original).functor.map
      ((unitMap source).closed.functor.map event ≫ (unitMap source).reduction) ≫
        (extension source target original).reduction

theorem complete_event_reading {context : source.original.closed.Obj} (event : context ⟶ source.original.Event) :
    eventReading source target original event = original.closed.functor.map event ≫ original.reduction := by
  have entire := (recovered source target original).complete_event_readout event
  change (recovered source target original).comparison.inv.app context ≫
    (extension source target original).functor.map ((unitMap source).closed.functor.map event) ≫
      ((extension source target original).functor.map (unitMap source).reduction ≫
        (extension source target original).reduction) = _ at entire
  simpa only [eventReading, (extension source target original).functor.map_comp, Category.assoc] using entire

def namedComparison := RelativeClosedNamedQuantifiedModels.restrictionComparison
  (model source target original) (readings source target original) original (Iso.refl _)

def arrowReading
    {before after : (RelativeClosedNamedQuantifiedPresentation.namedTheory source.original
      (selections source) (constructors source)).closed.Obj} (arrow : before ⟶ after) :=
  (namedComparison source target original).comparison.inv.app before ≫
    (extension source target original).functor.map
      ((RelativeClosedNamedQuantifiedPresentation.unitMap source.original
        (selections source) (constructors source)).functor.map arrow) ≫
          (namedComparison source target original).comparison.hom.app after

theorem complete_arrow_reading
    {before after : (RelativeClosedNamedQuantifiedPresentation.namedTheory source.original
      (selections source) (constructors source)).closed.Obj} (arrow : before ⟶ after) :
    arrowReading source target original arrow = (model source target original).nativeDiagram.map arrow :=
  RelativeClosedNamedQuantifiedModels.complete_arrow_read
    (model source target original) (readings source target original) original (Iso.refl _) arrow

theorem entire_constructor_function (origin : RelativeClosedStructuralImagePresentation.Constructor source.original) :
    HEq (arrowReading source target original (classOf
      ((RelativeClosedStructuralImagePresentation.nativeInclusion source.original
        (selections source) (constructors source)).rawArrow
        (RelativeClosedStructuralImagePresentation.namedRaw source.original
          (selections source) (constructors source) origin))))
      ((model source target original).constructorValues origin).arrow :=
  (heq_of_eq (complete_arrow_reading source target original _)).trans
    ((model source target original).native_named_image origin)

theorem entire_authored_firing (origin : RelativeClosedPositionedModalPresentation.Selection source.original) :
    (extension source target original).functor.map (Rule.transport (unitMap source) origin.rule).action ≫
        (extension source target original).reduction =
      (recovered source target original).comparison.hom.app origin.rule.parameters ≫
        (original.closed.functor.map origin.rule.action ≫ original.reduction) :=
  RelativeClosedNamedQuantifiedMeaning.complete_authored_firing source.original target.quantified
    (selections source) (constructors source) target.implication original origin

end Mettapedia.GSLT.Core.RelativeClosedBareLogical.Readout
