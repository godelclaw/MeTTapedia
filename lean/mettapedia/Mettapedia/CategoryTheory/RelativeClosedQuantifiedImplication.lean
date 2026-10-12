import Mettapedia.CategoryTheory.RelativeClosedQuantifiedExtension
import Mettapedia.CategoryTheory.InternalPredicateImplicationMaps
import Mettapedia.CategoryTheory.InternalPredicateImplicationFunctionMaps

/-!
# Quantified completion retains locally qualified implication

The actual completion unit transports the three implication diagrams.
Every independently supplied weak map from that completion preserves the
resulting operation and both complete inputs. Applying the same contract
to restriction retains the original implication before completion. The
quantifier extension introduces no implication-preservation hypothesis.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedQuantified.Implication

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open InternalConjunctiveOrderComparison InternalPredicateImplication

universe k
variable (source : ConjunctiveClosedTheory.{k})
variable (qualified : Qualification source.operations)

def freeQualification : Qualification (freeObject source).operations.predicates :=
  InternalPredicateImplicationMaps.qualificationImage (Extension.unitMap source).declarations qualified

theorem unit_square :
    (Extension.unitMap source).functor.map qualified.operation ≫
        (Extension.unitMap source).declarations.proposition.hom =
      (tupleComparison (Extension.unitMap source).declarations).hom ≫
        (freeQualification source qualified).operation :=
  InternalPredicateImplicationMaps.implication_square (Extension.unitMap source).declarations
    (freeObject source).operations.laws qualified (freeQualification source qualified)

theorem unit_supplied {context : source.closed.Obj} (first second : source.operations.Fiber context) :
    (Extension.unitMap source).declarations.image (qualified.implies source.operations first second) =
      (freeQualification source qualified).implies (freeObject source).operations.predicates
        ((Extension.unitMap source).declarations.image first)
        ((Extension.unitMap source).declarations.image second) :=
  InternalPredicateImplicationMaps.implication_supplied (Extension.unitMap source).declarations
    (freeObject source).operations.laws qualified (freeQualification source qualified) first second

variable {source} {target : QuantifiedClosedTheory.{k}}
variable (candidate : QuantifiedClosedTheory.Map (freeObject source) target)
variable (targetQualification : Qualification target.operations.predicates)

local instance candidate_finite : PreservesFiniteLimits candidate.functor := candidate.finite
local instance candidate_declarations_finite : PreservesFiniteLimits candidate.declarations.functor := candidate.finite
local instance candidate_declarations_closed : MonoidalClosedFunctor candidate.declarations.functor := candidate.closed
local instance candidate_product (value parameter : (freeObject source).closed.Obj) :
    IsIso (CartesianMonoidalCategory.prodComparison candidate.functor value parameter) :=
  CartesianMonoidalCategory.isIso_prodComparison_of_preservesLimit_pair candidate.functor value parameter

theorem complete_candidate_square :
    candidate.functor.map (freeQualification source qualified).operation ≫
        candidate.declarations.proposition.hom =
      (tupleComparison candidate.declarations).hom ≫ targetQualification.operation :=
  InternalPredicateImplicationMaps.implication_square candidate.declarations target.operations.laws
    (freeQualification source qualified) targetQualification

theorem complete_candidate_supplied {context : (freeObject source).closed.Obj}
    (first second : (freeObject source).operations.predicates.Fiber context) :
    candidate.declarations.image
        ((freeQualification source qualified).implies (freeObject source).operations.predicates first second) =
      targetQualification.implies target.operations.predicates
        (candidate.declarations.image first) (candidate.declarations.image second) :=
  InternalPredicateImplicationMaps.implication_supplied candidate.declarations target.operations.laws
    (freeQualification source qualified) targetQualification first second

theorem restricted_candidate_supplied {context : source.closed.Obj}
    (first second : source.operations.Fiber context) :
    (Extension.restrictMap candidate).declarations.image (qualified.implies source.operations first second) =
      targetQualification.implies target.operations.predicates
        ((Extension.restrictMap candidate).declarations.image first)
        ((Extension.restrictMap candidate).declarations.image second) :=
  InternalPredicateImplicationMaps.implication_supplied (Extension.restrictMap candidate).declarations
    target.operations.laws qualified targetQualification first second

theorem complete_candidate_function_read {value parameter : (freeObject source).closed.Obj}
    (first second : parameter ⟶ InternalPredicateFunctionObject.power
      (freeObject source).operations.predicates value) :
    inv (CartesianMonoidalCategory.prodComparison candidate.functor value parameter) ≫
        candidate.declarations.image ((freeQualification source qualified).implies
          (freeObject source).operations.predicates
          (InternalPredicateFunctionObject.read (freeObject source).operations.predicates first)
          (InternalPredicateFunctionObject.read (freeObject source).operations.predicates second)) =
      targetQualification.implies target.operations.predicates
        (InternalPredicateFunctionObject.read target.operations.predicates
          (InternalPredicateFunctionObjectMaps.sectionImage candidate.declarations first))
        (InternalPredicateFunctionObject.read target.operations.predicates
          (InternalPredicateFunctionObjectMaps.sectionImage candidate.declarations second)) := by
  exact @InternalPredicateImplicationFunctionMaps.supplied_read
    (freeObject source).closed.Obj _ _ _ _ target.closed.Obj _ _ _ _
    (freeObject source).operations.predicates target.operations.predicates
    candidate.declarations candidate.finite candidate.closed target.operations.laws
    (freeQualification source qualified) targetQualification value parameter first second

end Mettapedia.CategoryTheory.RelativeClosedQuantified.Implication
