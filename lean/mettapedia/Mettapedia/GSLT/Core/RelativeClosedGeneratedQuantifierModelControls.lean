import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierModelNativeComparison
import Mettapedia.GSLT.Core.RelativeClosedGeneratedQuantifierClosureQuantifierControls

/-!
# Complete general-model quantifier values and a failed local candidate

The independently supplied program model enters the general quantified
construction through its local initial readings. The actual final functor's
operator value is checked at both endpoints before extracting its function.
Full inputs, changing parameters and empty inputs have their exact native
readouts. A truth-valued constant candidate fails the finite existential
format by complete-operation uniqueness and the actual empty-input reading.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedGeneratedQuantifierModelControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory
open RelativeClosedSyntax GeneratedCategory RelativeClosedGeneratedQuantifier
open Iteration Closure
open HigherOrderInternalPredicateObject HigherOrderInternalPredicateQuantifier
open ElementaryTypePredicateReadout
open PositionedRewritePredicatePower (name family_name)
open RelativeClosedGeneratedQuantifierIterationControls
open RelativeClosedGeneratedQuantifierClosureQuantifierControls (finalRoute finalInput finalOutput)

def quantifiers := HigherOrderInternalPredicateQuantifiedObject.operations doctrine

def suppliedModel : Model quantifiers initial := model.toModel

def actualOperatorValue : RelativeClosedSyntax.Interpretation.ArrowValue Type :=
  modelOperatorValue suppliedModel finalRoute
    (Closure.existential initial (classOf finalRoute.arrow)).operation

theorem actualOperatorValue_read :
    actualOperatorValue = (⟨finalInput, finalOutput, secondImage⟩ :
      RelativeClosedSyntax.Interpretation.ArrowValue Type) :=
  (model_operator_native model finalRoute
    (Closure.existential initial (classOf finalRoute.arrow)).operation).trans
      RelativeClosedGeneratedQuantifierClosureQuantifierControls.finalOperatorValue_read

def checkedOperator : Option (finalInput ⟶ finalOutput) :=
  RelativeClosedSyntax.Interpretation.ArrowValue.readAt (some actualOperatorValue) finalInput finalOutput

theorem checkedOperator_read : checkedOperator = some secondImage := by
  change RelativeClosedSyntax.Interpretation.ArrowValue.readAt
    (some actualOperatorValue) finalInput finalOutput = some secondImage
  rw [actualOperatorValue_read]
  exact RelativeClosedSyntax.Interpretation.ArrowValue.readAt_supplied secondImage

def actualOperator : finalInput ⟶ finalOutput :=
  checkedOperator.get (by rw [checkedOperator_read]; rfl)

theorem actualOperator_read : actualOperator = secondImage :=
  Option.some.inj ((Option.some_get (by rw [checkedOperator_read]; rfl)).trans checkedOperator_read)

def suppliedOutput (first second : Nat → Nat) :
    Subobject (power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace ⊗ Nat) :=
  family doctrine (selectedName first second ≫ actualOperator)

theorem suppliedOutput_read (first second : Nat → Nat)
    (result : power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace) (parameter : Nat) :
    Contains (suppliedOutput first second) (result, parameter) ↔
      result = firstImage (chosen first second parameter) := by
  change Contains (family doctrine (selectedName first second ≫ actualOperator)) (result, parameter) ↔ _
  rw [actualOperator_read]
  exact complete_output_read first second result parameter

theorem actual_function_retains_future_parameters (first second : Nat → Nat)
    (result : power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace) (parameter : Nat) :
    Contains (family doctrine ((future ≫ selectedName first second) ≫ actualOperator)) (result, parameter) ↔
      result = firstImage (chosen first second (parameter + 1)) := by
  rw [actualOperator_read]
  exact future_retains_the_whole_first_stage_input first second result parameter

theorem actual_function_rejects_empty_input
    (result : power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace) (parameter : Nat) :
    ¬Contains (family doctrine (emptyName ≫ actualOperator)) (result, parameter) := by
  rw [actualOperator_read]
  exact the_actual_second_stage_quantifier_rejects_every_empty_input result parameter

def constantTruth : finalInput ⟶ finalOutput :=
  name doctrine (⊤ : Subobject
    (power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace ⊗ finalInput))

theorem constantTruth_empty_read :
    family doctrine (emptyName ≫ constantTruth) =
      (⊤ : Subobject (power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace ⊗ Nat)) := by
  change PositionedRewritePredicatePower.family doctrine (emptyName ≫ constantTruth) = _
  rw [← PositionedRewritePredicatePower.family_substitution, constantTruth,
    PositionedRewritePredicatePower.family_name, doctrine.reindex_top]

theorem constantTruth_is_not_the_actual_operator : constantTruth ≠ actualOperator := by
  intro same
  let result := firstImage (chosen id id 0)
  have admitted : Contains (family doctrine (emptyName ≫ constantTruth)) (result, 0) :=
    constantTruth_empty_read.symm ▸ contains_top (result, 0)
  have equalFamilies := congrArg (fun arrow : finalInput ⟶ finalOutput =>
    family doctrine (emptyName ≫ arrow)) same
  exact actual_function_rejects_empty_input result 0
    ((congrArg (fun predicate :
        Subobject (power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace ⊗ Nat) =>
      Contains predicate (result, 0)) equalFamilies).mp admitted)

theorem constantTruth_cannot_satisfy_the_three_local_existential_diagrams :
    ¬∃ candidate : InternalPredicateExistential.Existential quantifiers.predicates firstImage,
      candidate.operation = constantTruth := by
  rintro ⟨candidate, reading⟩
  have unique := quantifiers.existential_unique firstImage candidate
  have actual : (quantifiers.existential firstImage).operation = actualOperator :=
    second_image_complete.symm.trans actualOperator_read.symm
  exact constantTruth_is_not_the_actual_operator (reading.symm.trans (unique.trans actual))

theorem every_closure_route_has_both_complete_model_images (route : Route (Closure.signature initial)) :
    modelOperatorValue suppliedModel route (Closure.universal initial (classOf route.arrow)).operation =
      quantifiedValue quantifiers .universal (modelRouteValue suppliedModel route) ∧
    modelOperatorValue suppliedModel route (Closure.existential initial (classOf route.arrow)).operation =
      quantifiedValue quantifiers .existential (modelRouteValue suppliedModel route) :=
  ⟨universal_image suppliedModel route, existential_image suppliedModel route⟩

end Mettapedia.GSLT.Core.RelativeClosedGeneratedQuantifierModelControls
