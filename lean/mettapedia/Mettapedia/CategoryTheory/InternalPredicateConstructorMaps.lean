import Mettapedia.CategoryTheory.InternalPredicateQuantifiedCoherence
import Mettapedia.CategoryTheory.InternalPredicateQuantifiedObjectMaps

/-!
# Structural image action through independently compared constructors

Local quantified predicate maps determine the complete existential action.
Independently supplied argument and program isomorphisms compare the actual
constructor carriers. One local constructor square earns the whole image
operation square and every supplied predicate family, including future
parameters. The theorem concerns constructor images; disjoint parse-tree
roots require the additional syntax and equation admission conditions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalPredicateConstructorMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open InternalPredicateFunctionObject InternalPredicateFunctionObjectMaps
open InternalPredicateQuantifiedCoherence PositionedModalOutgoingComparison

universe u v k
variable {C : Type u} [Category.{k} C] [CartesianMonoidalCategory C]
variable [MonoidalClosed C] [HasEqualizers C]
variable {D : Type v} [Category.{k} D] [CartesianMonoidalCategory D]
variable [MonoidalClosed D] [HasEqualizers D]
variable {source : InternalPredicateQuantifiedObject.Operations C}
variable {target : InternalPredicateQuantifiedObject.Operations D}
variable (mapping : InternalPredicateQuantifiedObject.Map source target)

def comparedPower (value : C) {actual : D} (comparison : mapping.functor.obj value ≅ actual) :
    mapping.functor.obj (power source.predicates value) ≅ power target.predicates actual :=
  powerComparison mapping.predicates value ≪≫ powerReindexIso target.predicates comparison

variable {arguments program : C} (constructor : arguments ⟶ program)
variable {actualArguments actualProgram : D}
variable (argumentComparison : mapping.functor.obj arguments ≅ actualArguments)
variable (programComparison : mapping.functor.obj program ≅ actualProgram)

def translatedConstructor : actualArguments ⟶ actualProgram :=
  argumentComparison.inv ≫ mapping.functor.map constructor ≫ programComparison.hom

theorem complete_translated_square :
    mapping.functor.map (source.existential constructor).operation ≫
        (comparedPower mapping program programComparison).hom =
      (comparedPower mapping arguments argumentComparison).hom ≫
        (target.existential
          (translatedConstructor mapping constructor argumentComparison programComparison)).operation := by
  calc
    _ = (mapping.functor.map (source.existential constructor).operation ≫
        (powerComparison mapping.predicates program).hom) ≫
          (powerReindexIso target.predicates programComparison).hom := (Category.assoc _ _ _).symm
    _ = ((powerComparison mapping.predicates arguments).hom ≫
        (target.existential (mapping.functor.map constructor)).operation) ≫
          (powerReindexIso target.predicates programComparison).hom :=
      congrArg (fun arrow => arrow ≫ (powerReindexIso target.predicates programComparison).hom)
        (mapping.existential_square constructor)
    _ = _ := (Category.assoc _ _ _).trans
      ((congrArg (fun arrow => (powerComparison mapping.predicates arguments).hom ≫ arrow)
        (existential_constructor_comparison target (mapping.functor.map constructor)
          argumentComparison programComparison)).trans (Category.assoc _ _ _).symm)

variable (actualConstructor : actualArguments ⟶ actualProgram)
variable (square : mapping.functor.map constructor ≫ programComparison.hom =
  argumentComparison.hom ≫ actualConstructor)

include square in
theorem independently_supplied_constructor :
    translatedConstructor mapping constructor argumentComparison programComparison = actualConstructor := by
  change argumentComparison.inv ≫ (mapping.functor.map constructor ≫ programComparison.hom) = actualConstructor
  rw [square, Iso.inv_hom_id_assoc]

include square in
theorem complete_independent_square :
    mapping.functor.map (source.existential constructor).operation ≫
        (comparedPower mapping program programComparison).hom =
      (comparedPower mapping arguments argumentComparison).hom ≫
        (target.existential actualConstructor).operation :=
  (complete_translated_square mapping constructor argumentComparison programComparison).trans
    (congrArg (fun arrow => (comparedPower mapping arguments argumentComparison).hom ≫
      (target.existential arrow).operation)
        (independently_supplied_constructor mapping constructor argumentComparison programComparison
          actualConstructor square))

include square in
theorem complete_supplied_family {parameter : C}
    (predicate : parameter ⟶ power source.predicates arguments) :
    mapping.functor.map (predicate ≫ (source.existential constructor).operation) ≫
        (comparedPower mapping program programComparison).hom =
      (mapping.functor.map predicate ≫ (comparedPower mapping arguments argumentComparison).hom) ≫
        (target.existential actualConstructor).operation := by
  rw [mapping.functor.map_comp, Category.assoc,
    complete_independent_square mapping constructor argumentComparison programComparison actualConstructor square,
    ← Category.assoc]

include square in
theorem complete_future_family {first second : C} (future : first ⟶ second)
    (predicate : second ⟶ power source.predicates arguments) :
    mapping.functor.map ((future ≫ predicate) ≫ (source.existential constructor).operation) ≫
        (comparedPower mapping program programComparison).hom =
      mapping.functor.map future ≫
        ((mapping.functor.map predicate ≫ (comparedPower mapping arguments argumentComparison).hom) ≫
          (target.existential actualConstructor).operation) := by
  rw [complete_supplied_family mapping constructor argumentComparison programComparison actualConstructor square,
    mapping.functor.map_comp]
  simp only [Category.assoc]

end Mettapedia.CategoryTheory.InternalPredicateConstructorMaps
