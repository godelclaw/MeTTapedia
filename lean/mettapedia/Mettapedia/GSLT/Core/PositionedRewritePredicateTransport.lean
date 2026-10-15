import Mettapedia.GSLT.Core.PositionedRewriteFrameTransport
import Mettapedia.CategoryTheory.PositionedModalOutgoingComparison

/-!
# Shared program and predicate action on complete rule frames

Three local predicate comparisons share the actual program theory functor.
Finite limits and closedness are supplied by that theory map. Preservation
of implication, both quantifiers and the whole positioned-modal operator
is derived. Its postcondition input uses the independently earned outgoing
isomorphism, including the program comparison, and its rely input remains
independent. Actual supplied events retain the separate frame action.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.PositionedRewritePredicateTransport

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory ProgramReductionTheory AuthoredClosedTheory
open InternalPredicateFunctionObject InternalPredicateFunctionObjectMaps
open InternalPredicatePositionedModalMaps PositionedModalOutgoingComparison

universe u v
variable {first second : Theory.{u,v}}
variable (mapping : Map first second)
variable (source : InternalPredicateQuantifiedObject.Operations first.closed.Obj)
variable (target : InternalPredicateQuantifiedObject.Operations second.closed.Obj)

structure PredicateComparison where
  proposition : mapping.closed.functor.obj source.predicates.proposition ≅ target.predicates.proposition
  truth : mapping.closed.functor.map source.predicates.truth ≫ proposition.hom =
    CartesianMonoidalCategory.toUnit (mapping.closed.functor.obj (𝟙_ first.closed.Obj)) ≫ target.predicates.truth
  conjunction : mapping.closed.functor.map source.predicates.conjunction ≫ proposition.hom =
    CartesianMonoidalCategory.lift
      (mapping.closed.functor.map (fst source.predicates.proposition source.predicates.proposition) ≫ proposition.hom)
      (mapping.closed.functor.map (snd source.predicates.proposition source.predicates.proposition) ≫ proposition.hom) ≫
        target.predicates.conjunction

variable {mapping source target}

namespace PredicateComparison

variable (comparison : PredicateComparison mapping source target)

def predicates : InternalConjunctiveObject.Map source.predicates target.predicates where
  functor := mapping.closed.functor
  proposition := comparison.proposition
  truth := comparison.truth
  conjunction := comparison.conjunction

instance predicates_finite : PreservesFiniteLimits comparison.predicates.functor :=
  mapping.closed.preservesFiniteLimits

instance predicates_closed : MonoidalClosedFunctor comparison.predicates.functor :=
  mapping.closed.preservesExponentials

def quantified : InternalPredicateQuantifiedObject.Map source target where
  predicates := comparison.predicates
  finite := mapping.closed.preservesFiniteLimits
  closed := mapping.closed.preservesExponentials

end PredicateComparison

variable (comparison : PredicateComparison mapping source target)
variable (sourceImplication : InternalPredicateImplication.Qualification source.predicates)
variable (targetImplication : InternalPredicateImplication.Qualification target.predicates)
variable {rule : Rule first} (frame : PositionedRewriteModal.Frame rule)

def inputsComparison :
    mapping.closed.functor.obj (profiles source.predicates frame.assay (frame.assay ⨯ first.program)) ≅
      profiles target.predicates (frame.transport mapping).assay
        ((frame.transport mapping).assay ⨯ second.program) :=
  profilesComparison comparison.quantified frame.assay (frame.assay ⨯ first.program) ≪≫
    profilesReindexIso (predicates := target.predicates) (frame.outgoingComparison mapping)

theorem complete_operator_square :
    mapping.closed.functor.map (modalityOperator source sourceImplication
        frame.forget frame.focus frame.instantiate frame.outgoing) ≫
        (powerComparison comparison.predicates frame.carrier).hom =
      (inputsComparison comparison frame).hom ≫
        modalityOperator target targetImplication
          (frame.transport mapping).forget (frame.transport mapping).focus
          (frame.transport mapping).instantiate (frame.transport mapping).outgoing := by
  have outgoingRead : (frame.transport mapping).outgoing =
      mapping.closed.functor.map frame.outgoing ≫ (frame.outgoingComparison mapping).hom :=
    (frame.outgoing_transport mapping).symm
  have canonical := modalityOperator_comparison target targetImplication
    (mapping.closed.functor.map frame.forget) (mapping.closed.functor.map frame.focus)
    (mapping.closed.functor.map frame.instantiate) (mapping.closed.functor.map frame.outgoing)
    (frame.outgoingComparison mapping)
  have frameCanonical :
      (profilesReindexIso (predicates := target.predicates) (frame.outgoingComparison mapping)).hom ≫
        modalityOperator target targetImplication
          (frame.transport mapping).forget (frame.transport mapping).focus
          (frame.transport mapping).instantiate (frame.transport mapping).outgoing =
      modalityOperator target targetImplication
        (mapping.closed.functor.map frame.forget) (mapping.closed.functor.map frame.focus)
        (mapping.closed.functor.map frame.instantiate) (mapping.closed.functor.map frame.outgoing) := by
    rw [outgoingRead]
    exact canonical
  exact (modality_square comparison.quantified sourceImplication targetImplication
    frame.forget frame.focus frame.instantiate frame.outgoing).trans
      ((congrArg (fun arrow =>
        (profilesComparison comparison.quantified frame.assay (frame.assay ⨯ first.program)).hom ≫ arrow)
        frameCanonical.symm).trans (Category.assoc _ _ _).symm)

theorem complete_supplied_image {parameter : first.closed.Obj}
    (inputs : parameter ⟶ profiles source.predicates frame.assay (frame.assay ⨯ first.program)) :
    sectionImage comparison.predicates
        (inputs ≫ modalityOperator source sourceImplication
          frame.forget frame.focus frame.instantiate frame.outgoing) =
      mapping.closed.functor.map inputs ≫ (inputsComparison comparison frame).hom ≫
        modalityOperator target targetImplication
          (frame.transport mapping).forget (frame.transport mapping).focus
          (frame.transport mapping).instantiate (frame.transport mapping).outgoing := by
  exact (congrArg (fun arrow => arrow ≫ (powerComparison comparison.predicates frame.carrier).hom)
    (comparison.predicates.functor.map_comp inputs
      (modalityOperator source sourceImplication frame.forget frame.focus frame.instantiate frame.outgoing))).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun arrow => comparison.predicates.functor.map inputs ≫ arrow)
            (complete_operator_square comparison sourceImplication targetImplication frame)))

theorem complete_future_image {before after : first.closed.Obj} (incoming : before ⟶ after)
    (inputs : after ⟶ profiles source.predicates frame.assay (frame.assay ⨯ first.program)) :
    sectionImage comparison.predicates
        ((incoming ≫ inputs) ≫ modalityOperator source sourceImplication
          frame.forget frame.focus frame.instantiate frame.outgoing) =
      mapping.closed.functor.map incoming ≫
        (mapping.closed.functor.map inputs ≫ (inputsComparison comparison frame).hom ≫
          modalityOperator target targetImplication
            (frame.transport mapping).forget (frame.transport mapping).focus
            (frame.transport mapping).instantiate (frame.transport mapping).outgoing) := by
  rw [complete_supplied_image, mapping.closed.functor.map_comp, Category.assoc]

end Mettapedia.GSLT.Core.PositionedRewritePredicateTransport
