import Mettapedia.CategoryTheory.InternalPredicateImplicationMaps
import Mettapedia.CategoryTheory.InternalPredicateFunctionObjectMaps

/-!
# Implication on complete supplied predicate functions

The canonical function-object comparison retains the supplied value and
parameter together. Implication commutes with that complete reading and
with parameter substitution. The comparison uses two independently
supplied function sections.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalPredicateImplicationFunctionMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open InternalConjunctiveObject InternalPredicateImplication
open InternalPredicateFunctionObject InternalPredicateFunctionObjectMaps

universe u v k
variable {C : Type u} [Category.{k} C] [CartesianMonoidalCategory C]
variable [MonoidalClosed C] [HasEqualizers C]
variable {D : Type v} [Category.{k} D] [CartesianMonoidalCategory D]
variable [MonoidalClosed D] [HasEqualizers D]
variable {source : Operations C} {target : Operations D}
variable (mapping : Map source target) [PreservesFiniteLimits mapping.functor]
variable [MonoidalClosedFunctor mapping.functor]
variable (targetLaws : target.Laws)
variable (sourceImplication : Qualification source) (targetImplication : Qualification target)
include targetLaws

theorem supplied_read {value parameter : C}
    (first second : parameter ⟶ power source value) :
    inv (CartesianMonoidalCategory.prodComparison mapping.functor value parameter) ≫
        mapping.image (sourceImplication.implies source (read source first) (read source second)) =
      targetImplication.implies target
        (read target (sectionImage mapping first)) (read target (sectionImage mapping second)) := by
  refine (congrArg (fun arrow =>
      inv (CartesianMonoidalCategory.prodComparison mapping.functor value parameter) ≫ arrow)
    (InternalPredicateImplicationMaps.implication_supplied mapping targetLaws
      sourceImplication targetImplication (read source first) (read source second))).trans ?_
  exact (targetImplication.implies_substitution target _ _ _).trans
    (congrArg₂ (targetImplication.implies target)
      (sectionImage_read mapping first).symm (sectionImage_read mapping second).symm)

theorem supplied_substitution {value firstParameter secondParameter : C}
    (incoming : firstParameter ⟶ secondParameter)
    (first second : secondParameter ⟶ power source value) :
    inv (CartesianMonoidalCategory.prodComparison mapping.functor value firstParameter) ≫
        mapping.image (sourceImplication.implies source
          (read source (incoming ≫ first)) (read source (incoming ≫ second))) =
      (mapping.functor.obj value ◁ mapping.functor.map incoming) ≫
        targetImplication.implies target
          (read target (sectionImage mapping first)) (read target (sectionImage mapping second)) := by
  refine (supplied_read mapping targetLaws sourceImplication targetImplication
    (incoming ≫ first) (incoming ≫ second)).trans ?_
  have firstRead : read target (sectionImage mapping (incoming ≫ first)) =
      (mapping.functor.obj value ◁ mapping.functor.map incoming) ≫
        read target (sectionImage mapping first) :=
    (congrArg (read target) (sectionImage_substitution mapping incoming first)).trans
      (read_substitution target _ _)
  have secondRead : read target (sectionImage mapping (incoming ≫ second)) =
      (mapping.functor.obj value ◁ mapping.functor.map incoming) ≫
        read target (sectionImage mapping second) :=
    (congrArg (read target) (sectionImage_substitution mapping incoming second)).trans
      (read_substitution target _ _)
  exact (congrArg₂ (targetImplication.implies target) firstRead secondRead).trans
    (targetImplication.implies_substitution target _ _ _).symm

end Mettapedia.CategoryTheory.InternalPredicateImplicationFunctionMaps
