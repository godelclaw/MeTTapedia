import Mettapedia.CategoryTheory.RelativeClosedQuantifiedAdjunction
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# The induced quantified-completion monad and complete fold readings

The monad is induced by the independently earned adjunction. Multiplication
is the genuine quantified target interpretation of the second completion.
It retains the entire earlier category and folds every later quantifier
using its canonical complete function-object comparison. Since quantifier
qualifications are uniquely determined by the conjunctive object, the
forgetful functor is full and faithful and multiplication is invertible.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedQuantified.Construction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory
open RelativeClosedGeneratedQuantifier Iteration

universe k

def monad : Monad (ConjunctiveClosedTheory.{k}) := FreeForgetful.adjunction.toMonad

theorem underlying_object (source : ConjunctiveClosedTheory.{k}) :
    monad.obj source = (freeObject source).conjunctive := rfl

theorem underlying_map {source target : ConjunctiveClosedTheory.{k}} (mapping : source ⟶ target) :
    monad.map mapping = QuantifiedClosedTheory.forget.map (FreeForgetful.freeMap mapping) := rfl

theorem unit_component (source : ConjunctiveClosedTheory.{k}) :
    monad.η.app source = FreeForgetful.unit source := FreeForgetful.unit_app source

def multiplicationMap (source : ConjunctiveClosedTheory.{k}) :
    QuantifiedClosedTheory.Map (freeObject (freeObject source).conjunctive) (freeObject source) :=
  FreeForgetful.counitMap (freeObject source)

theorem multiplication_component (source : ConjunctiveClosedTheory.{k}) :
    monad.μ.app source = ConjunctiveClosedTheory.classOf (multiplicationMap source) := rfl

theorem retains_old_diagram (source : ConjunctiveClosedTheory.{k}) :
    baseFunctor (Closure.signature (stage (freeObject source).conjunctive)) ⋙
      (multiplicationMap source).functor = 𝟭 (freeObject source).closed.Obj := by
  rw [← Extension.unit_functor_base (freeObject source).conjunctive]
  exact Extension.complete_base_recovered (ConjunctiveClosedTheory.Map.identity (freeObject source).conjunctive)

theorem retains_old_object (source : ConjunctiveClosedTheory.{k}) (object : (freeObject source).closed.Obj) :
    (multiplicationMap source).functor.obj
      (baseObject (Closure.signature (stage (freeObject source).conjunctive)) object) = object :=
  congrArg (fun functor => functor.obj object) (retains_old_diagram source)

theorem retains_old_arrow (source : ConjunctiveClosedTheory.{k})
    {before after : (freeObject source).closed.Obj} (arrow : before ⟶ after) :
    (multiplicationMap source).functor.map
        (baseArrow (signature := Closure.signature (stage (freeObject source).conjunctive)) arrow) ≫
      eqToHom (retains_old_object source after) =
        eqToHom (retains_old_object source before) ≫ arrow := by
  have complete := (eqToIso (retains_old_diagram source)).hom.naturality arrow
  simpa only [eqToIso.hom, eqToHom_app, _root_.CategoryTheory.Functor.comp_map,
    _root_.CategoryTheory.Functor.id_map, baseFunctor] using complete

theorem folds_universal (source : ConjunctiveClosedTheory.{k})
    {before after : (freeObject (freeObject source).conjunctive).closed.Obj} (route : before ⟶ after) :
    InternalPredicateFunctionObjectMaps.arrowImage (multiplicationMap source).declarations
      ((freeObject (freeObject source).conjunctive).operations.universal route).operation =
        ((freeObject source).operations.universal ((multiplicationMap source).functor.map route)).operation :=
  (QuantifiedClosedTheory.Map.quantified (multiplicationMap source)).universal_image route

theorem folds_existential (source : ConjunctiveClosedTheory.{k})
    {before after : (freeObject (freeObject source).conjunctive).closed.Obj} (route : before ⟶ after) :
    InternalPredicateFunctionObjectMaps.arrowImage (multiplicationMap source).declarations
      ((freeObject (freeObject source).conjunctive).operations.existential route).operation =
        ((freeObject source).operations.existential ((multiplicationMap source).functor.map route)).operation :=
  (QuantifiedClosedTheory.Map.quantified (multiplicationMap source)).existential_image route

instance multiplication_isIso (source : ConjunctiveClosedTheory.{k}) : IsIso (monad.μ.app source) := by
  change IsIso (QuantifiedClosedTheory.forget.map
    (FreeForgetful.adjunction.counit.app (freeObject source)))
  infer_instance

theorem right_unit (source : ConjunctiveClosedTheory.{k}) :
    monad.map (monad.η.app source) ≫ monad.μ.app source = 𝟙 (monad.obj source) := monad.right_unit source

theorem left_unit (source : ConjunctiveClosedTheory.{k}) :
    monad.η.app (monad.obj source) ≫ monad.μ.app source = 𝟙 (monad.obj source) := monad.left_unit source

theorem associativity (source : ConjunctiveClosedTheory.{k}) :
    monad.map (monad.μ.app source) ≫ monad.μ.app source =
      monad.μ.app (monad.obj source) ≫ monad.μ.app source := monad.assoc source

end Mettapedia.CategoryTheory.RelativeClosedQuantified.Construction
