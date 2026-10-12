import Mettapedia.CategoryTheory.InternalPredicateQuantifiedObject
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateQuantifier

/-!
# Classifier construction of a locally quantified predicate object

The generic classifier and its independently earned quantifiers construct
the truth, conjunction and complete function arrows. Their actual finite
diagrams assemble the local structure used by arbitrary interpretations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.HigherOrderInternalPredicateQuantifiedObject

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v p
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasEqualizers C]
variable (doctrine : PredicateDoctrine.HigherOrder.{u,v,p} C)

def operations : InternalPredicateQuantifiedObject.Operations C where
  predicates := HigherOrderInternalPredicateObject.operations doctrine
  laws := HigherOrderInternalPredicateObject.laws doctrine
  universal arrow := HigherOrderInternalPredicateQuantifier.forallQualification doctrine arrow
  existential arrow := HigherOrderInternalPredicateQuantifier.existsQualification doctrine arrow

theorem universal_read {source target : C} (arrow : source ⟶ target) :
    ((operations doctrine).universal arrow).operation =
      HigherOrderInternalPredicateQuantifier.forallOperation doctrine arrow := rfl

theorem existential_read {source target : C} (arrow : source ⟶ target) :
    ((operations doctrine).existential arrow).operation =
      HigherOrderInternalPredicateQuantifier.existsOperation doctrine arrow := rfl

end Mettapedia.CategoryTheory.HigherOrderInternalPredicateQuantifiedObject
