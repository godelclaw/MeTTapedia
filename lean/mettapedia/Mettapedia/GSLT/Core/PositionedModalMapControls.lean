import Mettapedia.CategoryTheory.InternalPredicatePositionedModalNativeComparison
import Mettapedia.CategoryTheory.RelativeClosedQuantifiedPositionedModal
import Mettapedia.GSLT.Core.InternalPredicateImplicationMapControls
import Mettapedia.GSLT.Core.PositionedRewriteModalPowerControls

/-!
# Whole modal action on an authored numeric rewrite

The source uses the nonidentity Boolean proposition presentation. Its actual
instance and reduct maps belong to the independently authored sum/successor
rewrite. The complete two-input comparison transports the operator back to
the native model, where its answer is the independently checked strict
comparison of focus and parameter. A future parameter changes that answer,
and an independently formed constant-truth function is rejected.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.PositionedModalMapControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory ElementaryTypePredicateReadout
open InternalPredicateFunctionObject InternalPredicateFunctionObjectMaps
open InternalPredicatePositionedModalMaps

abbrev native := InternalPredicateImplicationMapControls.nativeOperations
abbrev encoded := InternalPredicateImplicationMapControls.sourceOperations
abbrev encodedImplication := InternalPredicateImplicationMapControls.sourceImplication
abbrev nativeImplication := HigherOrderInternalPredicateImplication.qualification doctrine
abbrev frame := PositionedRewriteModalPowerControls.frame
abbrev outgoing := PositionedRewriteModalPowerControls.outgoing

def mapping : InternalPredicateQuantifiedObject.Map encoded native :=
  InternalPredicateQuantifiedObject.Transport.forwardMap native
    InternalPredicateImplicationMapControls.changedPresentation

def inputComparison := profilesComparison mapping frame.assay outgoing

def encodedInputs : Nat ⟶ profiles encoded.predicates frame.assay outgoing :=
  PositionedRewriteModalPowerControls.inputs ≫ inputComparison.inv

def encodedOperator : profiles encoded.predicates frame.assay outgoing ⟶ power encoded.predicates frame.carrier :=
  modalityOperator encoded encodedImplication frame.forget frame.focus frame.instantiate frame.outgoing

def mappedOutput : Nat ⟶ power native.predicates frame.carrier :=
  sectionImage mapping.predicates (encodedInputs ≫ encodedOperator)

theorem input_recovery : encodedInputs ≫ inputComparison.hom = PositionedRewriteModalPowerControls.inputs :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun arrow => PositionedRewriteModalPowerControls.inputs ≫ arrow)
      inputComparison.inv_hom_id).trans (Category.comp_id _))

theorem native_operator_comparison :
    modalityOperator native nativeImplication frame.forget frame.focus frame.instantiate frame.outgoing =
      PositionedRewriteModalPowerControls.modalFunction :=
  InternalPredicatePositionedModalNativeComparison.complete_operation doctrine
    frame.forget frame.focus frame.instantiate frame.outgoing

theorem complete_output_evaluation :
    mappedOutput = PositionedRewriteModalPowerControls.inputs ≫ PositionedRewriteModalPowerControls.modalFunction := by
  have complete := modality_supplied_image mapping encodedImplication nativeImplication
    frame.forget frame.focus frame.instantiate frame.outgoing encodedInputs
  change mappedOutput = encodedInputs ≫ inputComparison.hom ≫
    modalityOperator native nativeImplication frame.forget frame.focus frame.instantiate frame.outgoing at complete
  exact complete.trans
    ((Category.assoc encodedInputs inputComparison.hom _).symm.trans
      ((congrArg (fun arrow => arrow ≫ modalityOperator native nativeImplication
        frame.forget frame.focus frame.instantiate frame.outgoing) input_recovery).trans
          (congrArg (fun operation => PositionedRewriteModalPowerControls.inputs ≫ operation)
            native_operator_comparison)))

theorem complete_native_read (focus parameter : Nat) :
    Contains (HigherOrderInternalPredicateObject.family doctrine mappedOutput) (focus, parameter) ↔
      parameter < focus := by
  rw [complete_output_evaluation]
  exact PositionedRewriteModalPowerControls.output_read focus parameter

theorem the_mapped_modal_answer_is_proper :
    Contains (HigherOrderInternalPredicateObject.family doctrine mappedOutput) (2, 1) ∧
      ¬ Contains (HigherOrderInternalPredicateObject.family doctrine mappedOutput) (1, 1) := by
  rw [complete_native_read, complete_native_read]
  exact ⟨by decide, by decide⟩

def mappedFutureOutput : Nat ⟶ power native.predicates frame.carrier :=
  sectionImage mapping.predicates
    ((PositionedRewriteModalPowerControls.future ≫ encodedInputs) ≫ encodedOperator)

theorem complete_future_evaluation : mappedFutureOutput =
    PositionedRewriteModalPowerControls.future ≫
      (PositionedRewriteModalPowerControls.inputs ≫ PositionedRewriteModalPowerControls.modalFunction) := by
  have expression := congrArg (sectionImage mapping.predicates)
    (Category.assoc PositionedRewriteModalPowerControls.future encodedInputs encodedOperator)
  exact expression.trans
    ((sectionImage_substitution mapping.predicates PositionedRewriteModalPowerControls.future
      (encodedInputs ≫ encodedOperator)).trans
        (congrArg (fun arrow => PositionedRewriteModalPowerControls.future ≫ arrow)
          complete_output_evaluation))

theorem complete_future_read (focus parameter : Nat) :
    Contains (HigherOrderInternalPredicateObject.family doctrine mappedFutureOutput) (focus, parameter) ↔
      parameter + 1 < focus := by
  have expression : mappedFutureOutput =
      (PositionedRewriteModalPowerControls.future ≫ PositionedRewriteModalPowerControls.inputs) ≫
        PositionedRewriteModalPowerControls.modalFunction :=
    complete_future_evaluation.trans (Category.assoc _ _ _).symm
  rw [expression]
  exact PositionedRewriteModalPowerControls.complete_future_read focus parameter

theorem the_future_changes_the_mapped_modal_answer :
    Contains (HigherOrderInternalPredicateObject.family doctrine mappedOutput) (2, 1) ∧
      ¬ Contains (HigherOrderInternalPredicateObject.family doctrine mappedFutureOutput) (2, 1) := by
  rw [complete_native_read, complete_future_read]
  exact ⟨by decide, by decide⟩

def constantTruthOutput : Nat ⟶ power native.predicates frame.carrier :=
  PositionedRewritePredicatePower.name doctrine (⊤ : Subobject (frame.carrier ⊗ Nat))

theorem constant_truth_is_not_this_modal_output : mappedOutput ≠ constantTruthOutput := by
  intro same
  have held : Contains (HigherOrderInternalPredicateObject.family doctrine constantTruthOutput) (1, 1) := by
    have read := PositionedRewritePredicatePower.family_name doctrine
      (⊤ : Subobject (frame.carrier ⊗ Nat))
    exact (congrArg (fun predicate => Contains predicate (1, 1)) read).mpr (contains_top _)
  rw [← same] at held
  exact (complete_native_read 1 1).not.mpr (Nat.lt_irrefl 1) held

end Mettapedia.GSLT.Core.PositionedModalMapControls
