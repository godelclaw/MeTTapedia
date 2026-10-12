import Mettapedia.CategoryTheory.RelativeClosedQuantifiedProgramAdjunction
import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# The quantified program construction monad and its actual fold

The monad comes from the earned program-theory adjunction. Multiplication
interprets the iterated quantified completion in the original completed
theory, retaining all old context arrows and the complete supplied program
and event readings. Both quantifiers fold through their canonical closed
comparisons. Only the quantified program stratum is asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedQuantifiedProgram.Construction

open _root_.CategoryTheory
open Mettapedia.GSLT.Core

universe k

def monad : Monad (ConjunctiveProgramTheory.{k}) := FreeForgetful.adjunction.toMonad

theorem underlying_object (source : ConjunctiveProgramTheory.{k}) :
    monad.obj source = (freeObject source).conjunctive := rfl

theorem underlying_map {source target : ConjunctiveProgramTheory.{k}} (mapping : source ⟶ target) :
    monad.map mapping = QuantifiedProgramTheory.forget.map (FreeForgetful.freeMap mapping) := rfl

theorem unit_component (source : ConjunctiveProgramTheory.{k}) :
    monad.η.app source = FreeForgetful.unit source := FreeForgetful.unit_app source

def multiplicationMap (source : ConjunctiveProgramTheory.{k}) :
    QuantifiedProgramTheory.Map (freeObject (freeObject source).conjunctive) (freeObject source) :=
  FreeForgetful.counitMap (freeObject source)

theorem multiplication_component (source : ConjunctiveProgramTheory.{k}) :
    monad.μ.app source = ConjunctiveProgramTheory.classOf (multiplicationMap source) := rfl

def baseComparison (source : ConjunctiveProgramTheory.{k}) :
    ConjunctiveProgramTheory.MapIso
      (HomEquivalence.restriction (freeObject source).conjunctive (freeObject source)
        (multiplicationMap source))
      (ConjunctiveProgramTheory.Map.identity (freeObject source).conjunctive) :=
  HomEquivalence.extension_restriction (freeObject source).conjunctive (freeObject source)
    (ConjunctiveProgramTheory.Map.identity (freeObject source).conjunctive)

theorem complete_old_diagram (source : ConjunctiveProgramTheory.{k}) :
    (unitMap (freeObject source).conjunctive).functor ⋙ (multiplicationMap source).functor =
      𝟭 (freeObject source).programTheory.closed.Obj :=
  RelativeClosedQuantified.Extension.complete_base_recovered
    (ConjunctiveClosedTheory.Map.identity (freeObject source).conjunctive.conjunctive)

theorem complete_program_readout (source : ConjunctiveProgramTheory.{k})
    {context : (freeObject source).programTheory.closed.Obj}
    (term : context ⟶ (freeObject source).programTheory.program) :
    (baseComparison source).comparison.inv.app context ≫
        (multiplicationMap source).functor.map
          ((unitMap (freeObject source).conjunctive).functor.map term) ≫
            (multiplicationMap source).program.hom = term := by
  have reading := (HomEquivalence.localMap (freeObject source).conjunctive (freeObject source)
    (ConjunctiveProgramTheory.Map.identity (freeObject source).conjunctive)).complete_program_readout term
  exact reading.trans (Category.comp_id _)

theorem complete_event_readout (source : ConjunctiveProgramTheory.{k})
    {context : (freeObject source).programTheory.closed.Obj}
    (event : context ⟶ (freeObject source).programTheory.Event) :
    (baseComparison source).comparison.inv.app context ≫
        (multiplicationMap source).functor.map
          ((unitMap (freeObject source).conjunctive).functor.map event ≫
            (unitMap (freeObject source).conjunctive).reduction) ≫
              (multiplicationMap source).reduction = event := by
  have reading := (HomEquivalence.localMap (freeObject source).conjunctive (freeObject source)
    (ConjunctiveProgramTheory.Map.identity (freeObject source).conjunctive)).complete_event_readout event
  exact reading.trans (Category.comp_id _)

theorem folds_universal (source : ConjunctiveProgramTheory.{k})
    {before after : (freeObject (freeObject source).conjunctive).programTheory.closed.Obj}
    (route : before ⟶ after) :
    InternalPredicateFunctionObjectMaps.arrowImage (multiplicationMap source).conjunctive.declarations
        ((freeObject (freeObject source).conjunctive).operations.universal route).operation =
      ((freeObject source).operations.universal ((multiplicationMap source).functor.map route)).operation :=
  QuantifiedProgramTheory.complete_universal_action (multiplicationMap source) route

theorem folds_existential (source : ConjunctiveProgramTheory.{k})
    {before after : (freeObject (freeObject source).conjunctive).programTheory.closed.Obj}
    (route : before ⟶ after) :
    InternalPredicateFunctionObjectMaps.arrowImage (multiplicationMap source).conjunctive.declarations
        ((freeObject (freeObject source).conjunctive).operations.existential route).operation =
      ((freeObject source).operations.existential ((multiplicationMap source).functor.map route)).operation :=
  QuantifiedProgramTheory.complete_existential_action (multiplicationMap source) route

instance multiplication_isIso (source : ConjunctiveProgramTheory.{k}) : IsIso (monad.μ.app source) := by
  change IsIso (QuantifiedProgramTheory.forget.map
    (FreeForgetful.adjunction.counit.app (freeObject source)))
  infer_instance

theorem right_unit (source : ConjunctiveProgramTheory.{k}) :
    monad.map (monad.η.app source) ≫ monad.μ.app source = 𝟙 (monad.obj source) := monad.right_unit source

theorem left_unit (source : ConjunctiveProgramTheory.{k}) :
    monad.η.app (monad.obj source) ≫ monad.μ.app source = 𝟙 (monad.obj source) := monad.left_unit source

theorem associativity (source : ConjunctiveProgramTheory.{k}) :
    monad.map (monad.μ.app source) ≫ monad.μ.app source =
      monad.μ.app (monad.obj source) ≫ monad.μ.app source := monad.assoc source

end Mettapedia.CategoryTheory.RelativeClosedQuantifiedProgram.Construction
