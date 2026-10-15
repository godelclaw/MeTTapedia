import Mettapedia.CategoryTheory.RelativeClosedImplicativeQuantifiedAdjunction
import Mettapedia.CategoryTheory.RelativeClosedQuantifiedProgramMonad

/-!
# The implication-qualified quantified construction monad

The monad is induced by the earned varying-theory adjunction. Its
multiplication interprets the iterated, genuinely generated quantifier
extension in the first completion. Complete program and event readouts and
all three logical operations survive this fold in arbitrary new contexts.
Compatible map classes retain the actual raw context presentations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedImplicativeQuantified.Construction

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe k

def monad : Monad (ImplicativeProgramTheory.{k}) := adjunction.toMonad

theorem underlying_object (source : ImplicativeProgramTheory.{k}) :
    monad.obj source = (freeObject source).implicative := rfl

theorem unit_component (source : ImplicativeProgramTheory.{k}) :
    monad.η.app source = unit source := unit_app source

def multiplicationMap (source : ImplicativeProgramTheory.{k}) :
    QuantifiedImplicativeProgramTheory.Map (freeObject (freeObject source).implicative) (freeObject source) :=
  counitMap (freeObject source)

theorem multiplication_component (source : ImplicativeProgramTheory.{k}) :
    monad.μ.app source = ImplicativeProgramTheory.classOf (multiplicationMap source) := rfl

def baseComparison (source : ImplicativeProgramTheory.{k}) :
    ImplicativeProgramTheory.MapIso
      (restriction (freeObject source).implicative (freeObject source) (multiplicationMap source))
      (ConjunctiveProgramTheory.Map.identity (freeObject source).implicative.conjunctive) :=
  extensionRestriction (freeObject source).implicative (freeObject source)
    (ConjunctiveProgramTheory.Map.identity (freeObject source).implicative.conjunctive)

theorem complete_old_diagram (source : ImplicativeProgramTheory.{k}) :
    (unitMap (freeObject source).implicative).functor ⋙ (multiplicationMap source).functor =
      𝟭 (freeObject source).quantified.programTheory.closed.Obj :=
  RelativeClosedQuantifiedProgram.Construction.complete_old_diagram source.conjunctive

theorem complete_program_readout (source : ImplicativeProgramTheory.{k})
    {context : (freeObject source).quantified.programTheory.closed.Obj}
    (term : context ⟶ (freeObject source).quantified.programTheory.program) :
    (baseComparison source).comparison.inv.app context ≫
        (multiplicationMap source).functor.map ((unitMap (freeObject source).implicative).functor.map term) ≫
          (multiplicationMap source).program.hom = term :=
  RelativeClosedQuantifiedProgram.Construction.complete_program_readout source.conjunctive term

theorem complete_event_readout (source : ImplicativeProgramTheory.{k})
    {context : (freeObject source).quantified.programTheory.closed.Obj}
    (event : context ⟶ (freeObject source).quantified.programTheory.Event) :
    (baseComparison source).comparison.inv.app context ≫
        (multiplicationMap source).functor.map
          ((unitMap (freeObject source).implicative).functor.map event ≫
            (unitMap (freeObject source).implicative).reduction) ≫
              (multiplicationMap source).reduction = event :=
  RelativeClosedQuantifiedProgram.Construction.complete_event_readout source.conjunctive event

local instance multiplication_finite (source : ImplicativeProgramTheory.{k}) :
    PreservesFiniteLimits (multiplicationMap source).conjunctive.declarations.functor :=
  (multiplicationMap source).conjunctive.finite

local instance multiplication_closed (source : ImplicativeProgramTheory.{k}) :
    MonoidalClosedFunctor (multiplicationMap source).conjunctive.declarations.functor :=
  (multiplicationMap source).conjunctive.closed

theorem folds_universal (source : ImplicativeProgramTheory.{k})
    {before after : (freeObject (freeObject source).implicative).quantified.programTheory.closed.Obj}
    (route : before ⟶ after) :
    InternalPredicateFunctionObjectMaps.arrowImage (multiplicationMap source).conjunctive.declarations
        ((freeObject (freeObject source).implicative).quantified.operations.universal route).operation =
      ((freeObject source).quantified.operations.universal ((multiplicationMap source).functor.map route)).operation :=
  QuantifiedProgramTheory.complete_universal_action (multiplicationMap source) route

theorem folds_existential (source : ImplicativeProgramTheory.{k})
    {before after : (freeObject (freeObject source).implicative).quantified.programTheory.closed.Obj}
    (route : before ⟶ after) :
    InternalPredicateFunctionObjectMaps.arrowImage (multiplicationMap source).conjunctive.declarations
        ((freeObject (freeObject source).implicative).quantified.operations.existential route).operation =
      ((freeObject source).quantified.operations.existential ((multiplicationMap source).functor.map route)).operation :=
  QuantifiedProgramTheory.complete_existential_action (multiplicationMap source) route

theorem folds_complete_implication (source : ImplicativeProgramTheory.{k})
    {context : (freeObject (freeObject source).implicative).quantified.programTheory.closed.Obj}
    (first second : (freeObject (freeObject source).implicative).quantified.operations.predicates.Fiber context) :
    (multiplicationMap source).conjunctive.declarations.image
        ((freeObject (freeObject source).implicative).implication.implies
          (freeObject (freeObject source).implicative).quantified.operations.predicates first second) =
      (freeObject source).implication.implies (freeObject source).quantified.operations.predicates
        ((multiplicationMap source).conjunctive.declarations.image first)
        ((multiplicationMap source).conjunctive.declarations.image second) :=
  QuantifiedImplicativeProgramTheory.complete_implication (multiplicationMap source) first second

instance multiplication_isIso (source : ImplicativeProgramTheory.{k}) : IsIso (monad.μ.app source) := by
  change IsIso (QuantifiedImplicativeProgramTheory.forget.map (adjunction.counit.app (freeObject source)))
  infer_instance

theorem right_unit (source : ImplicativeProgramTheory.{k}) :
    monad.map (monad.η.app source) ≫ monad.μ.app source = 𝟙 (monad.obj source) := monad.right_unit source

theorem left_unit (source : ImplicativeProgramTheory.{k}) :
    monad.η.app (monad.obj source) ≫ monad.μ.app source = 𝟙 (monad.obj source) := monad.left_unit source

theorem associativity (source : ImplicativeProgramTheory.{k}) :
    monad.map (monad.μ.app source) ≫ monad.μ.app source =
      monad.μ.app (monad.obj source) ≫ monad.μ.app source := monad.assoc source

end Mettapedia.CategoryTheory.RelativeClosedImplicativeQuantified.Construction
