import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedPresentation
import Mettapedia.GSLT.Core.RelativeClosedStructuralImageProgramReadout
import Mettapedia.CategoryTheory.RelativeClosedGeneratedPredicateModelMaps

/-!
# Independent local models of the complete named quantified theory

The old predicate, modal and constructor declarations are realized locally.
Three predicate readings and an independently supplied program map then earn
the complete conjunctive program map. The actual quantified universal
construction extends it, recovering every old arrow, program and firing.
Candidate interpretations are compared through compatible isomorphisms;
raw context objects are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory ProgramReductionTheory AuthoredClosedTheory
open RelativeClosedGeneratedQuantifier.SourceOperations
open RelativeClosedNamedQuantifiedPresentation

universe k
variable {source : Theory.{k,k}} {target : QuantifiedProgramTheory.{k}} {Index Origins : Type k}
variable {selected : Index → RelativeClosedPositionedModalPresentation.Selection source}
variable {constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source}
variable (model : RelativeClosedStructuralImageLocalModels.LocalModel source selected constructors
  target.programTheory.closed.Obj)
variable (readings : PredicateReadings (language source selected constructors)
  (truth source selected constructors) model.nativeModel target.operations.predicates)
variable (original : Map source target.programTheory)
variable (originalBase : model.previous.base ≅ original.closed.functor)

abbrev originalInterpretation := RelativeClosedStructuralImageProgramReadout.extension model original originalBase

def namedMap : ConjunctiveProgramTheory.Map (namedTheory source selected constructors) target.conjunctive where
  conjunctive := {
    declarations := readings.predicateMap
    finite := PredicateReadings.predicateMap_finite readings
    closed := PredicateReadings.predicateMap_closed readings }
  program := (originalInterpretation model original originalBase).program
  reduction := (originalInterpretation model original originalBase).reduction
  source := (originalInterpretation model original originalBase).source
  target := (originalInterpretation model original originalBase).target

def extension : QuantifiedProgramTheory.Map (completed source selected constructors) target :=
  RelativeClosedQuantifiedProgram.HomEquivalence.extension (namedTheory source selected constructors) target
    (namedMap model readings original originalBase)

def restrictionComparison : ConjunctiveProgramTheory.MapIso
    (ConjunctiveProgramTheory.Map.compose (unitMap source selected constructors)
      (extension model readings original originalBase))
    (namedMap model readings original originalBase) :=
  RelativeClosedQuantifiedProgram.HomEquivalence.extension_restriction
    (namedTheory source selected constructors) target (namedMap model readings original originalBase)

theorem complete_arrow_read
    {before after : (namedTheory source selected constructors).closed.Obj} (arrow : before ⟶ after) :
    (restrictionComparison model readings original originalBase).comparison.inv.app before ≫
        (extension model readings original originalBase).functor.map
          ((unitMap source selected constructors).functor.map arrow) ≫
            (restrictionComparison model readings original originalBase).comparison.hom.app after =
      model.nativeDiagram.map arrow := by
  have natural := (restrictionComparison model readings original originalBase).comparison.hom.naturality arrow
  change (extension model readings original originalBase).functor.map
      ((unitMap source selected constructors).functor.map arrow) ≫
      (restrictionComparison model readings original originalBase).comparison.hom.app after =
    (restrictionComparison model readings original originalBase).comparison.hom.app before ≫
      model.nativeDiagram.map arrow at natural
  calc
    _ = (restrictionComparison model readings original originalBase).comparison.inv.app before ≫
        ((restrictionComparison model readings original originalBase).comparison.hom.app before ≫
          model.nativeDiagram.map arrow) := by
      exact congrArg
        (fun carried => (restrictionComparison model readings original originalBase).comparison.inv.app before ≫ carried)
        natural
    _ = _ := (restrictionComparison model readings original originalBase).comparison.inv_hom_id_app_assoc _ _

def sourceComparison : ProgramReductionTheoryIsoClasses.MapIso
    (Map.compose (programInclusion source selected constructors)
      (extension model readings original originalBase).underlying) original := by
  change ProgramReductionTheoryIsoClasses.MapIso
    (Map.compose
      (Map.compose (RelativeClosedStructuralImagePresentation.programInclusion source selected constructors)
        (unitMap source selected constructors).underlying)
      (extension model readings original originalBase).underlying) original
  rw [Map.compose_assoc]
  exact ((restrictionComparison model readings original originalBase).underlying.precompose
    (RelativeClosedStructuralImagePresentation.programInclusion source selected constructors)).trans
      (RelativeClosedStructuralImageProgramReadout.restrictionComparison model original originalBase)

theorem complete_program_readout {context : source.closed.Obj} (term : context ⟶ source.program) :
    (extension model readings original originalBase).functor.map
        ((programInclusion source selected constructors).closed.functor.map term) ≫
          (Map.compose (programInclusion source selected constructors)
            (extension model readings original originalBase).underlying).program.hom =
      (sourceComparison model readings original originalBase).comparison.hom.app context ≫
        (original.closed.functor.map term ≫ original.program.hom) := by
  have programRead := (sourceComparison model readings original originalBase).program
  change ((programInclusion source selected constructors).closed.functor ⋙
      (extension model readings original originalBase).functor).map term ≫ _ = _
  rw [← programRead, ← Category.assoc]
  exact (congrArg (fun arrow => arrow ≫ original.program.hom)
    ((sourceComparison model readings original originalBase).comparison.hom.naturality term)).trans
      (Category.assoc _ _ _)

theorem complete_event_readout {context : source.closed.Obj} (event : context ⟶ source.Event) :
    (extension model readings original originalBase).functor.map
        ((programInclusion source selected constructors).closed.functor.map event ≫
          (programInclusion source selected constructors).reduction) ≫
            (extension model readings original originalBase).reduction =
      (sourceComparison model readings original originalBase).comparison.hom.app context ≫
        (original.closed.functor.map event ≫ original.reduction) := by
  have eventRead := (sourceComparison model readings original originalBase).reduction_square
  change (sourceComparison model readings original originalBase).comparison.hom.app source.Event ≫
    original.reduction = (extension model readings original originalBase).functor.map
      (programInclusion source selected constructors).reduction ≫
        (extension model readings original originalBase).reduction at eventRead
  rw [(extension model readings original originalBase).functor.map_comp, Category.assoc, ← eventRead,
    ← Category.assoc]
  exact (congrArg (fun arrow => arrow ≫ original.reduction)
    ((sourceComparison model readings original originalBase).comparison.hom.naturality event)).trans
      (Category.assoc _ _ _)

theorem complete_authored_firing (origin : Index) :
    (extension model readings original originalBase).functor.map
        (Rule.transport (programInclusion source selected constructors) (selected origin).rule).action ≫
          (extension model readings original originalBase).reduction =
      (sourceComparison model readings original originalBase).comparison.hom.app (selected origin).rule.parameters ≫
        (original.closed.functor.map (selected origin).rule.action ≫ original.reduction) :=
  complete_event_readout model readings original originalBase (selected origin).rule.action

variable (candidate : QuantifiedProgramTheory.Map (completed source selected constructors) target)
variable (localComparison : ConjunctiveProgramTheory.MapIso
  (ConjunctiveProgramTheory.Map.compose (unitMap source selected constructors) candidate)
  (namedMap model readings original originalBase))

def completeComparison : QuantifiedProgramTheory.MapIso candidate (extension model readings original originalBase) :=
  RelativeClosedQuantifiedProgram.HomEquivalence.completeComparison
    (namedTheory source selected constructors) target (namedMap model readings original originalBase)
    candidate localComparison

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedModels
