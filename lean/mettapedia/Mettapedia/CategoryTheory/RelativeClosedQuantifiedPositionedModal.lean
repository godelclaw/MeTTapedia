import Mettapedia.CategoryTheory.RelativeClosedQuantifiedImplication
import Mettapedia.CategoryTheory.InternalPredicatePositionedModalMaps

/-!
# Positioned-modal operators in the actual quantified completion

The construction uses the actual completion unit on all supplied instance
maps and its transported implication qualification. An arbitrary weak map
out of the completion preserves the complete operator, every supplied pair
of predicate functions, and changes of their parameter context. The maps
are supplied by a rule consumer; they do not alone provide a firing origin.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedQuantified.PositionedModal

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open InternalPredicateFunctionObject InternalPredicateFunctionObjectMaps
open InternalPredicatePositionedModalMaps

universe k
variable (source : ConjunctiveClosedTheory.{k})
variable (qualified : InternalPredicateImplication.Qualification source.operations)
variable {instances assignments assay carrier outgoing : source.closed.Obj}

def operator (forget : instances ⟶ assignments) (focus : assignments ⟶ carrier)
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing) :
    profiles (freeObject source).operations.predicates
        ((Extension.unitMap source).functor.obj assay) ((Extension.unitMap source).functor.obj outgoing) ⟶
      power (freeObject source).operations.predicates ((Extension.unitMap source).functor.obj carrier) :=
  modalityOperator (freeObject source).operations (Implication.freeQualification source qualified)
    ((Extension.unitMap source).functor.map forget) ((Extension.unitMap source).functor.map focus)
    ((Extension.unitMap source).functor.map instantiate) ((Extension.unitMap source).functor.map reduct)

variable {source} {target : QuantifiedClosedTheory.{k}}
variable (candidate : QuantifiedClosedTheory.Map (freeObject source) target)
variable (targetQualification : InternalPredicateImplication.Qualification target.operations.predicates)

theorem complete_candidate_square
    (forget : instances ⟶ assignments) (focus : assignments ⟶ carrier)
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing) :
    candidate.functor.map (operator source qualified forget focus instantiate reduct) ≫
        (powerComparison candidate.quantified.predicates ((Extension.unitMap source).functor.obj carrier)).hom =
      (profilesComparison candidate.quantified ((Extension.unitMap source).functor.obj assay)
        ((Extension.unitMap source).functor.obj outgoing)).hom ≫
      modalityOperator target.operations targetQualification
        (candidate.functor.map ((Extension.unitMap source).functor.map forget))
        (candidate.functor.map ((Extension.unitMap source).functor.map focus))
        (candidate.functor.map ((Extension.unitMap source).functor.map instantiate))
        (candidate.functor.map ((Extension.unitMap source).functor.map reduct)) :=
  modality_square candidate.quantified (Implication.freeQualification source qualified) targetQualification
    ((Extension.unitMap source).functor.map forget) ((Extension.unitMap source).functor.map focus)
    ((Extension.unitMap source).functor.map instantiate) ((Extension.unitMap source).functor.map reduct)

theorem complete_candidate_supplied
    (forget : instances ⟶ assignments) (focus : assignments ⟶ carrier)
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing)
    {parameter : (freeObject source).closed.Obj}
    (inputs : parameter ⟶ profiles (freeObject source).operations.predicates
      ((Extension.unitMap source).functor.obj assay) ((Extension.unitMap source).functor.obj outgoing)) :
    sectionImage candidate.quantified.predicates (inputs ≫ operator source qualified forget focus instantiate reduct) =
      candidate.functor.map inputs ≫
        (profilesComparison candidate.quantified ((Extension.unitMap source).functor.obj assay)
          ((Extension.unitMap source).functor.obj outgoing)).hom ≫
      modalityOperator target.operations targetQualification
        (candidate.functor.map ((Extension.unitMap source).functor.map forget))
        (candidate.functor.map ((Extension.unitMap source).functor.map focus))
        (candidate.functor.map ((Extension.unitMap source).functor.map instantiate))
        (candidate.functor.map ((Extension.unitMap source).functor.map reduct)) :=
  modality_supplied_image candidate.quantified (Implication.freeQualification source qualified) targetQualification
    ((Extension.unitMap source).functor.map forget) ((Extension.unitMap source).functor.map focus)
    ((Extension.unitMap source).functor.map instantiate) ((Extension.unitMap source).functor.map reduct) inputs

theorem complete_candidate_future
    (forget : instances ⟶ assignments) (focus : assignments ⟶ carrier)
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing)
    {first second : (freeObject source).closed.Obj} (incoming : first ⟶ second)
    (inputs : second ⟶ profiles (freeObject source).operations.predicates
      ((Extension.unitMap source).functor.obj assay) ((Extension.unitMap source).functor.obj outgoing)) :
    sectionImage candidate.quantified.predicates
        ((incoming ≫ inputs) ≫ operator source qualified forget focus instantiate reduct) =
      candidate.functor.map incoming ≫
        (candidate.functor.map inputs ≫
          (profilesComparison candidate.quantified ((Extension.unitMap source).functor.obj assay)
            ((Extension.unitMap source).functor.obj outgoing)).hom ≫
          modalityOperator target.operations targetQualification
            (candidate.functor.map ((Extension.unitMap source).functor.map forget))
            (candidate.functor.map ((Extension.unitMap source).functor.map focus))
            (candidate.functor.map ((Extension.unitMap source).functor.map instantiate))
            (candidate.functor.map ((Extension.unitMap source).functor.map reduct))) :=
  modality_future_image candidate.quantified (Implication.freeQualification source qualified) targetQualification
    ((Extension.unitMap source).functor.map forget) ((Extension.unitMap source).functor.map focus)
    ((Extension.unitMap source).functor.map instantiate) ((Extension.unitMap source).functor.map reduct) incoming inputs

end Mettapedia.CategoryTheory.RelativeClosedQuantified.PositionedModal
