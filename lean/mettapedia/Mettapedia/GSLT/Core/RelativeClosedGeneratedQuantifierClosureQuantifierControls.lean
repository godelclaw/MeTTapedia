import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierClosureQuantifierReadout
import Mettapedia.GSLT.Core.RelativeClosedGeneratedQuantifierClosureControls

/-!
# The actual closure quantifier keeps its complete native function input

The route is an independently authored first-stage added quantifier. The
closure's unique existential operation maps to a complete native arrow,
whose checked endpoints earn extraction of the actual function. Its whole
parameterized predicate readout retains both supplied inputs and future
restriction. A nonempty complete input and the empty predicate have distinct
images, excluding a constant or truth-only final interpretation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedGeneratedQuantifierClosureQuantifierControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory
open RelativeClosedSyntax GeneratedCategory RelativeClosedGeneratedQuantifier
open Iteration Closure
open HigherOrderInternalPredicateObject HigherOrderInternalPredicateQuantifier
open ElementaryTypePredicateReadout
open PositionedRewritePredicatePower (name family_name)
open RelativeClosedGeneratedQuantifierIterationControls

def finalRoute : Route (Closure.signature initial) := firstRoute.translate (stageMap initial 1)

def finalOperatorValue : RelativeClosedSyntax.Interpretation.ArrowValue Type :=
  nativeOperatorValue model finalRoute (Closure.existential initial (classOf finalRoute.arrow)).operation

abbrev finalInput := power doctrine (power doctrine RelativeClosedGeneratedQuantifierControls.inputSpace)
abbrev finalOutput := power doctrine (power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace)

theorem finalOperatorValue_read :
    finalOperatorValue = (⟨finalInput, finalOutput, secondImage⟩ :
      RelativeClosedSyntax.Interpretation.ArrowValue Type) := by
  have actual := unique_existential_native_read model 1 firstRoute firstImage first_route_read
  change finalOperatorValue = (⟨finalInput, finalOutput, existsOperation doctrine firstImage⟩ :
    RelativeClosedSyntax.Interpretation.ArrowValue Type) at actual
  exact actual.trans (congrArg (fun arrow : finalInput ⟶ finalOutput =>
    (⟨finalInput, finalOutput, arrow⟩ : RelativeClosedSyntax.Interpretation.ArrowValue Type))
      second_image_complete.symm)

def checkedFinalOperator : Option (finalInput ⟶ finalOutput) :=
  RelativeClosedSyntax.Interpretation.ArrowValue.readAt (some finalOperatorValue) finalInput finalOutput

theorem checkedFinalOperator_read : checkedFinalOperator = some secondImage := by
  change RelativeClosedSyntax.Interpretation.ArrowValue.readAt
    (some finalOperatorValue) finalInput finalOutput = some secondImage
  rw [finalOperatorValue_read]
  exact RelativeClosedSyntax.Interpretation.ArrowValue.readAt_supplied secondImage

def finalOperator : finalInput ⟶ finalOutput :=
  checkedFinalOperator.get (by rw [checkedFinalOperator_read]; rfl)

theorem finalOperator_read : finalOperator = secondImage :=
  Option.some.inj ((Option.some_get (by rw [checkedFinalOperator_read]; rfl)).trans checkedFinalOperator_read)

def completeOutput (first second : Nat → Nat) :
    Subobject (power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace ⊗ Nat) :=
  family doctrine (selectedName first second ≫ finalOperator)

theorem completeOutput_read (first second : Nat → Nat)
    (result : power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace) (parameter : Nat) :
    Contains (completeOutput first second) (result, parameter) ↔
      result = firstImage (chosen first second parameter) := by
  change Contains (family doctrine (selectedName first second ≫ finalOperator)) (result, parameter) ↔ _
  rw [finalOperator_read]
  exact complete_output_read first second result parameter

theorem actual_closure_operator_retains_the_supplied_whole_input
    (first second : Nat → Nat) (parameter : Nat) :
    Contains (completeOutput first second) (firstImage (chosen first second parameter), parameter) :=
  (completeOutput_read first second _ parameter).mpr rfl

theorem actual_closure_operator_retains_future_parameters (first second : Nat → Nat)
    (result : power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace) (parameter : Nat) :
    Contains (family doctrine ((future ≫ selectedName first second) ≫ finalOperator)) (result, parameter) ↔
      result = firstImage (chosen first second (parameter + 1)) := by
  rw [finalOperator_read]
  exact future_retains_the_whole_first_stage_input first second result parameter

theorem actual_closure_operator_rejects_empty_inputs
    (result : power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace) (parameter : Nat) :
    ¬Contains (family doctrine (emptyName ≫ finalOperator)) (result, parameter) := by
  rw [finalOperator_read]
  exact the_actual_second_stage_quantifier_rejects_every_empty_input result parameter

theorem complete_input_and_empty_input_have_distinct_actual_images (first second : Nat → Nat) :
    selectedName first second ≫ finalOperator ≠ emptyName ≫ finalOperator := by
  intro same
  have readings := congrArg (family doctrine) same
  have positive := actual_closure_operator_retains_the_supplied_whole_input first second 0
  have negative := actual_closure_operator_rejects_empty_inputs (firstImage (chosen first second 0)) 0
  exact negative ((congrArg
    (fun predicate : Subobject (power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace ⊗ Nat) =>
      Contains predicate (firstImage (chosen first second 0), 0)) readings).mp positive)

theorem every_actual_closure_arrow_has_both_qualifications
    {source target : Object (Closure.signature initial)} (route : source ⟶ target) :
    Nonempty (InternalPredicateQuantifier.Universal (Closure.operations initial) route) ∧
      Nonempty (InternalPredicateExistential.Existential (Closure.operations initial) route) :=
  ⟨⟨Closure.universal initial route⟩, ⟨Closure.existential initial route⟩⟩

theorem the_whole_native_stage_functor_is_retained (depth : Nat) :
    (stageMap initial depth).functor ⋙ nativeDiagram model = stageDiagram model depth :=
  native_whole_stage_restriction model depth

end Mettapedia.GSLT.Core.RelativeClosedGeneratedQuantifierClosureQuantifierControls
