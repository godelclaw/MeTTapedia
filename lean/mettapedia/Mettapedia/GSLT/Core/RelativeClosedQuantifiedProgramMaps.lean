import Mettapedia.GSLT.Core.RelativeClosedQuantifiedRuleFrames
import Mettapedia.CategoryTheory.RelativeClosedQuantifiedHomEquivalence

/-!
# Extending independently supplied program maps through quantified completion

The target reduction relation is independently supplied, rather than built
as the image relation. A local weak predicate map and actual program/event
endpoint squares extend to a genuine program theory map. The complete base
comparison of the quantified universal construction earns the program
isomorphism and event arrow. Restriction recovers the supplied program map
through a compatible natural isomorphism, including its entire event map.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory ProgramReductionTheory
open RelativeClosedQuantified RelativeClosedQuantifiedRuleFrames

universe k

private theorem endpoint_extension {C D E : Type k} [Category.{k} C] [Category.{k} D] [Category.{k} E]
    (first : C ⥤ D) (second : D ⥤ E) (original : C ⥤ E) (comparison : first ⋙ second ≅ original)
    {events programs : C} {newEvents : D} {targetEvents targetPrograms : E}
    (endpoint : events ⟶ programs) (eventComparison : newEvents ⟶ first.obj events)
    (newEndpoint : newEvents ⟶ first.obj programs)
    (programComparison : original.obj programs ≅ targetPrograms)
    (event : original.obj events ⟶ targetEvents) (targetEndpoint : targetEvents ⟶ targetPrograms)
    (suppliedSquare : event ≫ targetEndpoint = original.map endpoint ≫ programComparison.hom)
    (generatedSquare : eventComparison ≫ first.map endpoint = newEndpoint) :
    (second.map eventComparison ≫ comparison.hom.app events ≫ event) ≫ targetEndpoint =
      second.map newEndpoint ≫ (comparison.hom.app programs ≫ programComparison.hom) := by
  calc
    _ = second.map eventComparison ≫
        ((comparison.hom.app events ≫ original.map endpoint) ≫ programComparison.hom) := by
      simp only [Category.assoc, suppliedSquare]
    _ = second.map eventComparison ≫
        ((second.map (first.map endpoint) ≫ comparison.hom.app programs) ≫ programComparison.hom) :=
      congrArg (fun arrow => second.map eventComparison ≫ (arrow ≫ programComparison.hom))
        (comparison.hom.naturality endpoint).symm
    _ = _ := by
      simp only [← Category.assoc]
      rw [← second.map_comp, generatedSquare]

private theorem transported_reading {C D E : Type k} [Category.{k} C] [Category.{k} D] [Category.{k} E]
    (first : C ⥤ D) (second : D ⥤ E) (original : C ⥤ E) (comparison : first ⋙ second ≅ original)
    {before after : C} {result : E} (arrow : before ⟶ after) (reading : original.obj after ⟶ result) :
    comparison.inv.app before ≫ second.map (first.map arrow) ≫
        (comparison.hom.app after ≫ reading) = original.map arrow ≫ reading := by
  calc
    _ = comparison.inv.app before ≫ ((second.map (first.map arrow) ≫ comparison.hom.app after) ≫ reading) := by
      simp only [Category.assoc]
    _ = comparison.inv.app before ≫ ((comparison.hom.app before ≫ original.map arrow) ≫ reading) :=
      congrArg (fun carried => comparison.inv.app before ≫ (carried ≫ reading))
        (comparison.hom.naturality arrow)
    _ = _ := by
      rw [Category.assoc, comparison.inv_hom_id_app_assoc]

variable (source target : Theory.{k,k})
variable (predicates : InternalConjunctiveObject.Operations source.closed.Obj) (laws : predicates.Laws)
variable (quantified : InternalPredicateQuantifiedObject.Operations target.closed.Obj)

def destination : QuantifiedClosedTheory.{k} where
  closed := target.closed
  operations := quantified

structure Supplied where
  declarations : ConjunctiveClosedTheory.Map (conjunctive source predicates laws)
    (destination target quantified).conjunctive
  program : declarations.functor.obj source.program ≅ target.program
  event : declarations.functor.obj source.Event ⟶ target.Event
  sourceEquation : event ≫ target.source = declarations.functor.map source.source ≫ program.hom
  targetEquation : event ≫ target.target = declarations.functor.map source.target ≫ program.hom

variable {source target predicates laws quantified}

namespace Supplied

variable (supplied : Supplied source target predicates laws quantified)

def original : Map source target where
  closed := supplied.declarations.underlying
  program := supplied.program
  reduction := supplied.event
  source := supplied.sourceEquation
  target := supplied.targetEquation

abbrev extension := Extension.extendMap supplied.declarations

def baseComparison : ConjunctiveClosedTheory.MapIso
    (Extension.restrictMap supplied.extension) supplied.declarations :=
  HomEquivalence.extension_restriction (conjunctive source predicates laws)
    (destination target quantified) supplied.declarations

def generatedEvents : (generatedTheory source predicates laws).Event ≅
    (inclusion source predicates laws).functor.obj source.Event :=
  RelativeClosedProgramReductionExtension.eventComparison source
    (freeObject (conjunctive source predicates laws)).closed (inclusion source predicates laws)

theorem generated_source_reading :
    (generatedEvents (source := source) (predicates := predicates) (laws := laws)).hom ≫ (inclusion source predicates laws).functor.map source.source =
      (generatedTheory source predicates laws).source := by
  have inverse := RelativeClosedProgramReductionExtension.complete_source_reading source
    (freeObject (conjunctive source predicates laws)).closed (inclusion source predicates laws)
  exact (congrArg (fun arrow => (generatedEvents (source := source) (predicates := predicates) (laws := laws)).hom ≫ arrow) inverse.symm).trans
    ((generatedEvents (source := source) (predicates := predicates) (laws := laws)).hom_inv_id_assoc _)

theorem generated_target_reading :
    (generatedEvents (source := source) (predicates := predicates) (laws := laws)).hom ≫ (inclusion source predicates laws).functor.map source.target =
      (generatedTheory source predicates laws).target := by
  have inverse := RelativeClosedProgramReductionExtension.complete_target_reading source
    (freeObject (conjunctive source predicates laws)).closed (inclusion source predicates laws)
  exact (congrArg (fun arrow => (generatedEvents (source := source) (predicates := predicates) (laws := laws)).hom ≫ arrow) inverse.symm).trans
    ((generatedEvents (source := source) (predicates := predicates) (laws := laws)).hom_inv_id_assoc _)

def extendedProgram : supplied.extension.functor.obj (generatedTheory source predicates laws).program ≅
    target.program :=
  (supplied.baseComparison.comparison.app source.program) ≪≫ supplied.program

def extendedEvent : supplied.extension.functor.obj (generatedTheory source predicates laws).Event ⟶
    target.Event :=
  supplied.extension.functor.map (generatedEvents (source := source) (predicates := predicates) (laws := laws)).hom ≫
    supplied.baseComparison.comparison.hom.app source.Event ≫ supplied.event

theorem extended_source : supplied.extendedEvent ≫ target.source =
    supplied.extension.functor.map (generatedTheory source predicates laws).source ≫ supplied.extendedProgram.hom :=
  endpoint_extension (inclusion source predicates laws).functor supplied.extension.functor
    supplied.declarations.functor supplied.baseComparison.comparison source.source
    (generatedEvents (source := source) (predicates := predicates) (laws := laws)).hom
    (generatedTheory source predicates laws).source supplied.program supplied.event target.source
    supplied.sourceEquation (generated_source_reading (source := source) (predicates := predicates) (laws := laws))

theorem extended_target : supplied.extendedEvent ≫ target.target =
    supplied.extension.functor.map (generatedTheory source predicates laws).target ≫ supplied.extendedProgram.hom :=
  endpoint_extension (inclusion source predicates laws).functor supplied.extension.functor
    supplied.declarations.functor supplied.baseComparison.comparison source.target
    (generatedEvents (source := source) (predicates := predicates) (laws := laws)).hom
    (generatedTheory source predicates laws).target supplied.program supplied.event target.target
    supplied.targetEquation (generated_target_reading (source := source) (predicates := predicates) (laws := laws))

def programMap : Map (generatedTheory source predicates laws) target where
  closed := supplied.extension.underlying
  program := supplied.extendedProgram
  reduction := supplied.extendedEvent
  source := supplied.extended_source
  target := supplied.extended_target

def restrictionComparison : ProgramReductionTheoryIsoClasses.MapIso
    (Map.compose (generatedInclusion source predicates laws) supplied.programMap) supplied.original where
  comparison := supplied.baseComparison.comparison
  program := by
    change supplied.baseComparison.comparison.hom.app source.program ≫ supplied.program.hom =
      supplied.extension.functor.map (𝟙 ((inclusion source predicates laws).functor.obj source.program)) ≫
        (supplied.baseComparison.comparison.hom.app source.program ≫ supplied.program.hom)
    exact (congrArg (fun arrow => arrow ≫
      (supplied.baseComparison.comparison.hom.app source.program ≫ supplied.program.hom))
      (supplied.extension.functor.map_id _)).trans (Category.id_comp _)|>.symm

theorem complete_restricted_event :
    supplied.baseComparison.comparison.hom.app source.Event ≫ supplied.event =
      supplied.extension.functor.map (generatedInclusion source predicates laws).reduction ≫ supplied.extendedEvent :=
  supplied.restrictionComparison.reduction_square

theorem complete_program_readout {context : source.closed.Obj} (term : context ⟶ source.program) :
    supplied.baseComparison.comparison.inv.app context ≫
        supplied.extension.functor.map ((inclusion source predicates laws).functor.map term) ≫
          supplied.extendedProgram.hom =
      supplied.declarations.functor.map term ≫ supplied.program.hom := by
  change supplied.baseComparison.comparison.inv.app context ≫
    supplied.extension.functor.map ((inclusion source predicates laws).functor.map term) ≫
      (supplied.baseComparison.comparison.hom.app source.program ≫ supplied.program.hom) = _
  exact transported_reading (inclusion source predicates laws).functor supplied.extension.functor
    supplied.declarations.functor supplied.baseComparison.comparison term supplied.program.hom

theorem complete_event_readout {context : source.closed.Obj} (event : context ⟶ source.Event) :
    supplied.baseComparison.comparison.inv.app context ≫
        supplied.extension.functor.map ((inclusion source predicates laws).functor.map event ≫
          (generatedInclusion source predicates laws).reduction) ≫ supplied.extendedEvent =
      supplied.declarations.functor.map event ≫ supplied.event := by
  have complete := supplied.complete_restricted_event
  have first : supplied.extension.functor.map
        ((inclusion source predicates laws).functor.map event ≫ (generatedInclusion source predicates laws).reduction) ≫
          supplied.extendedEvent =
      supplied.extension.functor.map ((inclusion source predicates laws).functor.map event) ≫
        (supplied.baseComparison.comparison.hom.app source.Event ≫ supplied.event) :=
    (congrArg (fun arrow => arrow ≫ supplied.extendedEvent) (supplied.extension.functor.map_comp _ _)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun arrow => supplied.extension.functor.map
          ((inclusion source predicates laws).functor.map event) ≫ arrow) complete.symm))
  exact (congrArg (fun arrow => supplied.baseComparison.comparison.inv.app context ≫ arrow) first).trans
    (transported_reading (inclusion source predicates laws).functor supplied.extension.functor
      supplied.declarations.functor supplied.baseComparison.comparison event supplied.event)

end Supplied

end Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramMaps
