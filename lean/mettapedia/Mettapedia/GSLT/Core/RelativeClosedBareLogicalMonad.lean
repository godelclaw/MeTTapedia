import Mettapedia.GSLT.Core.RelativeClosedBareLogicalAdjunction
import Mathlib.CategoryTheory.Monad.Adjunction
import Mettapedia.CategoryTheory.ProgramReductionMapReadout

/-!
# The construction monad on bare program theories

The earned free/forgetful adjunction induces a construction monad. Its
multiplication interprets the genuinely iterated named logical extension
in the first extension. The complete original program diagram has a
compatible comparison with the identity, and every generated quantifier
and implication retains its full operation under the fold.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedBareLogical.Construction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory

universe k

def monad : Monad (ProgramReductionTheoryIsoClasses.{k}) := adjunction.toMonad

theorem underlying_object (source : ProgramReductionTheoryIsoClasses.{k}) :
    monad.obj source = QuantifiedImplicativeProgramTheory.forgetProgram.obj (freeObject source) := rfl

theorem underlying_map {source target : ProgramReductionTheoryIsoClasses.{k}} (mapping : source ⟶ target) :
    monad.map mapping = QuantifiedImplicativeProgramTheory.forgetProgram.map (freeMap mapping) := rfl

theorem unit_component (source : ProgramReductionTheoryIsoClasses.{k}) :
    monad.η.app source = unit source := unit_app source

abbrev firstExtension (source : ProgramReductionTheoryIsoClasses.{k}) :=
  QuantifiedImplicativeProgramTheory.forgetProgram.obj (freeObject source)

def multiplicationMap (source : ProgramReductionTheoryIsoClasses.{k}) :
    QuantifiedImplicativeProgramTheory.Map (freeObject (firstExtension source)) (freeObject source) :=
  counitMap (freeObject source)

theorem multiplication_component (source : ProgramReductionTheoryIsoClasses.{k}) :
    monad.μ.app source = ProgramReductionTheoryIsoClasses.classOf (multiplicationMap source).underlying := rfl

def baseComparison (source : ProgramReductionTheoryIsoClasses.{k}) :
    ProgramReductionTheoryIsoClasses.MapIso
      (restriction (firstExtension source) (freeObject source) (multiplicationMap source))
      (ProgramReductionTheory.Map.identity (freeObject source).quantified.programTheory) :=
  extensionRestriction (firstExtension source) (freeObject source)
    (ProgramReductionTheory.Map.identity (freeObject source).quantified.programTheory)

def complete_old_diagram (source : ProgramReductionTheoryIsoClasses.{k}) :
    (unitMap (firstExtension source)).closed.functor ⋙ (multiplicationMap source).functor ≅
      𝟭 (freeObject source).quantified.programTheory.closed.Obj :=
  (baseComparison source).comparison

theorem complete_program_readout (source : ProgramReductionTheoryIsoClasses.{k})
    {context : (freeObject source).quantified.programTheory.closed.Obj}
    (term : context ⟶ (freeObject source).quantified.programTheory.program) :
    (baseComparison source).comparison.inv.app context ≫
        (restriction (firstExtension source) (freeObject source) (multiplicationMap source)).closed.functor.map term ≫
          (restriction (firstExtension source) (freeObject source) (multiplicationMap source)).program.hom = term := by
  have entire := (baseComparison source).complete_program_readout term
  exact entire.trans (Category.comp_id term)

theorem complete_event_readout (source : ProgramReductionTheoryIsoClasses.{k})
    {context : (freeObject source).quantified.programTheory.closed.Obj}
    (event : context ⟶ (freeObject source).quantified.programTheory.Event) :
    (baseComparison source).comparison.inv.app context ≫
        (multiplicationMap source).functor.map
          ((unitMap (firstExtension source)).closed.functor.map event ≫ (unitMap (firstExtension source)).reduction) ≫
            (multiplicationMap source).reduction = event := by
  have entire := (baseComparison source).complete_event_readout event
  change (baseComparison source).comparison.inv.app context ≫
    (multiplicationMap source).functor.map ((unitMap (firstExtension source)).closed.functor.map event) ≫
      ((multiplicationMap source).functor.map (unitMap (firstExtension source)).reduction ≫
        (multiplicationMap source).reduction) = event ≫ 𝟙 _ at entire
  simpa only [(multiplicationMap source).functor.map_comp, Category.assoc, Category.comp_id] using entire

local instance multiplication_finite (source : ProgramReductionTheoryIsoClasses.{k}) :
    PreservesFiniteLimits (multiplicationMap source).conjunctive.declarations.functor :=
  (multiplicationMap source).conjunctive.finite

local instance multiplication_closed (source : ProgramReductionTheoryIsoClasses.{k}) :
    MonoidalClosedFunctor (multiplicationMap source).conjunctive.declarations.functor :=
  (multiplicationMap source).conjunctive.closed

theorem folds_universal (source : ProgramReductionTheoryIsoClasses.{k})
    {before after : (freeObject (firstExtension source)).quantified.programTheory.closed.Obj}
    (route : before ⟶ after) :
    InternalPredicateFunctionObjectMaps.arrowImage (multiplicationMap source).conjunctive.declarations
        ((freeObject (firstExtension source)).quantified.operations.universal route).operation =
      ((freeObject source).quantified.operations.universal ((multiplicationMap source).functor.map route)).operation :=
  QuantifiedProgramTheory.complete_universal_action (multiplicationMap source) route

theorem folds_existential (source : ProgramReductionTheoryIsoClasses.{k})
    {before after : (freeObject (firstExtension source)).quantified.programTheory.closed.Obj}
    (route : before ⟶ after) :
    InternalPredicateFunctionObjectMaps.arrowImage (multiplicationMap source).conjunctive.declarations
        ((freeObject (firstExtension source)).quantified.operations.existential route).operation =
      ((freeObject source).quantified.operations.existential ((multiplicationMap source).functor.map route)).operation :=
  QuantifiedProgramTheory.complete_existential_action (multiplicationMap source) route

theorem folds_complete_implication (source : ProgramReductionTheoryIsoClasses.{k})
    {context : (freeObject (firstExtension source)).quantified.programTheory.closed.Obj}
    (first second : (freeObject (firstExtension source)).quantified.operations.predicates.Fiber context) :
    (multiplicationMap source).conjunctive.declarations.image
        ((freeObject (firstExtension source)).implication.implies
          (freeObject (firstExtension source)).quantified.operations.predicates first second) =
      (freeObject source).implication.implies (freeObject source).quantified.operations.predicates
        ((multiplicationMap source).conjunctive.declarations.image first)
        ((multiplicationMap source).conjunctive.declarations.image second) :=
  QuantifiedImplicativeProgramTheory.complete_implication (multiplicationMap source) first second

theorem right_unit (source : ProgramReductionTheoryIsoClasses.{k}) :
    monad.map (monad.η.app source) ≫ monad.μ.app source = 𝟙 (firstExtension source) := monad.right_unit source

theorem left_unit (source : ProgramReductionTheoryIsoClasses.{k}) :
    monad.η.app (firstExtension source) ≫ monad.μ.app source = 𝟙 (firstExtension source) := monad.left_unit source

theorem associativity (source : ProgramReductionTheoryIsoClasses.{k}) :
    monad.map (monad.μ.app source) ≫ monad.μ.app source =
      monad.μ.app (firstExtension source) ≫ monad.μ.app source := monad.assoc source

end Mettapedia.GSLT.Core.RelativeClosedBareLogical.Construction
