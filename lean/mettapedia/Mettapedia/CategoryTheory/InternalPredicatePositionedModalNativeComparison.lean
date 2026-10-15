import Mettapedia.CategoryTheory.InternalPredicatePositionedModalMaps
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateQuantifiedObject
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateImplication
import Mettapedia.CategoryTheory.PositionedRewritePredicatePower

/-!
# Native comparison of the complete positioned-modal operator

The operator built from the finite implication and quantifier interfaces
classifies the independently formed native conditional and modal predicate.
The comparison reads both function inputs on their whole value/parameter
contexts, and uniqueness determines the complete operation arrow.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalPredicatePositionedModalNativeComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open InternalPredicateFunctionObject InternalPredicatePositionedModalMaps

universe u v p
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasEqualizers C]
variable (doctrine : PredicateDoctrine.HigherOrder.{u,v,p} C)

abbrev quantified := HigherOrderInternalPredicateQuantifiedObject.operations doctrine
abbrev implication := HigherOrderInternalPredicateImplication.qualification doctrine

variable {instances assignments assay carrier outgoing : C}
variable (forget : instances ⟶ assignments) (focus : assignments ⟶ carrier)
variable (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing)

theorem condition_supplied {parameter : C}
    (inputs : parameter ⟶ profiles (quantified doctrine).predicates assay outgoing) :
    HigherOrderInternalPredicateObject.family doctrine
        (inputs ≫ conditionOperator (quantified doctrine).predicates (implication doctrine) instantiate reduct) =
      PositionedRewritePredicatePower.conditionAt doctrine instantiate reduct inputs := by
  have composed : inputs ≫ conditionOperator (quantified doctrine).predicates (implication doctrine)
      instantiate reduct = condition (quantified doctrine).predicates (implication doctrine)
        instantiate reduct (inputs ≫ fst _ _) (inputs ≫ snd _ _) :=
    (condition_substitution (quantified doctrine).predicates (implication doctrine)
      inputs instantiate reduct (fst _ _) (snd _ _)).symm
  change HigherOrderInternalPredicateObject.decode doctrine
    (read (quantified doctrine).predicates (inputs ≫ conditionOperator
      (quantified doctrine).predicates (implication doctrine) instantiate reduct)) = _
  exact (congrArg (fun name => HigherOrderInternalPredicateObject.decode doctrine
    (read (quantified doctrine).predicates name)) composed).trans
      ((congrArg (HigherOrderInternalPredicateObject.decode doctrine)
        (condition_read (quantified doctrine).predicates (implication doctrine)
          instantiate reduct (inputs ≫ fst _ _) (inputs ≫ snd _ _))).trans
        ((HigherOrderInternalPredicateImplication.applied_read doctrine _ _).trans
          (congrArg₂ (fun first second => first ⇨ second)
            (HigherOrderInternalPredicateQuantifier.precomposition_supplied doctrine instantiate (inputs ≫ fst _ _))
            (HigherOrderInternalPredicateQuantifier.precomposition_supplied doctrine reduct (inputs ≫ snd _ _)))))

theorem modality_supplied {parameter : C}
    (inputs : parameter ⟶ profiles (quantified doctrine).predicates assay outgoing) :
    HigherOrderInternalPredicateObject.family doctrine
        (inputs ≫ modalityOperator (quantified doctrine) (implication doctrine) forget focus instantiate reduct) =
      PositionedRewritePredicatePower.modalAt doctrine forget focus instantiate reduct inputs := by
  have expression : inputs ≫ modalityOperator (quantified doctrine) (implication doctrine)
      forget focus instantiate reduct =
      ((inputs ≫ conditionOperator (quantified doctrine).predicates (implication doctrine) instantiate reduct) ≫
        ((quantified doctrine).universal forget).operation) ≫
          ((quantified doctrine).existential focus).operation := by
    simp only [modalityOperator, Category.assoc]
  exact (congrArg (HigherOrderInternalPredicateObject.family doctrine) expression).trans
    ((HigherOrderInternalPredicateQuantifier.exists_supplied doctrine focus _).trans
      (congrArg (doctrine.existsAlong (focus ▷ parameter))
        ((HigherOrderInternalPredicateQuantifier.forall_supplied doctrine forget _).trans
          (congrArg (doctrine.forallAlong (forget ▷ parameter))
            (condition_supplied doctrine instantiate reduct inputs)))))

theorem complete_operation :
    modalityOperator (quantified doctrine) (implication doctrine) forget focus instantiate reduct =
      PositionedRewritePredicatePower.operation doctrine forget focus instantiate reduct :=
  PositionedRewritePredicatePower.operation_unique doctrine forget focus instantiate reduct _
    (by
      have complete := modality_supplied doctrine forget focus instantiate reduct (𝟙 _)
      exact (congrArg (HigherOrderInternalPredicateObject.family doctrine)
        (Category.id_comp (modalityOperator (quantified doctrine) (implication doctrine)
          forget focus instantiate reduct))).symm.trans complete)

theorem future_supplied {first second : C} (incoming : first ⟶ second)
    (inputs : second ⟶ profiles (quantified doctrine).predicates assay outgoing) :
    HigherOrderInternalPredicateObject.family doctrine
        ((incoming ≫ inputs) ≫ modalityOperator (quantified doctrine) (implication doctrine)
          forget focus instantiate reduct) =
      doctrine.reindex (carrier ◁ incoming)
        (PositionedRewritePredicatePower.modalAt doctrine forget focus instantiate reduct inputs) :=
  (modality_supplied doctrine forget focus instantiate reduct (incoming ≫ inputs)).trans
    (PositionedRewritePredicatePower.modal_substitution doctrine forget focus instantiate reduct incoming inputs).symm

end Mettapedia.CategoryTheory.InternalPredicatePositionedModalNativeComparison
