import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorConstructorProjections
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorComputationControls

/-!
# Constructed Vec selectors and original source-row controls

The Boolean-list interpretation extends the existing signature with choice
at the element and vector carriers. Constructor field injectivity supplies
the new background; the generated selectors then satisfy both projection
laws. A constructor that discards its head fails that background condition.
The original source/context certificates feed the new shared table unchanged.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorComputationRows.SelectedProjections.Controls
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies Programs.Annotated
open NativeVectorComputationRows.Controls (BaseSort number element vector carrier inhabitant)
local infixr:60 " ⇒ " => HOL.Ty.arr

inductive Const : HOL.Ty BaseSort → Type where
  | original {type : HOL.Ty BaseSort} (symbol : NativeVectorComputationRows.Controls.Const type) : Const type
  | select (type : HOL.Ty BaseSort) : Const (HOL.SelectionProofs.Selection type)

def operations : Operations BaseSort Const where
  number := number
  element := element
  vector := vector
  result := number
  zero := .const (.original .zero)
  successor := .const (.original .successor)
  nil := .const (.original .nil)
  cons := .const (.original .cons)
  head := .const (.original .head)
  tail := .const (.original .tail)
  selection := .const (.original .selection)

def choices : Choices operations := ⟨.const (.select element), .const (.select vector)⟩
def generated := constructed operations choices

noncomputable def meaning : {type : HOL.Ty BaseSort} → Const type → HOL.Ty.denote.{0,0} carrier type
  | _, .original symbol => NativeVectorComputationRows.Controls.meaning symbol
  | _, .select type => HOL.HOLLightStandardTheory.selectionOperation carrier inhabitant type

noncomputable def model : HOL.HenkinModel.{0,0,0} BaseSort Const := .standard carrier meaning

theorem recursion_choice_holds : model.models (HOL.SelectionProofs.principle operations.selection) :=
  NativeVectorComputationRows.Controls.selection_holds

theorem recursion_holds : model.models
    (HOL.NaturalRecursionProofs.statement operations.zero operations.successor (vector ⇒ number)) :=
  NativeVectorComputationRows.Controls.recursion_holds

theorem head_choice_holds : model.models (HOL.SelectionProofs.principle choices.headSelection) := by
  intro predicate _ witness _ holds
  exact HOL.HOLLightStandardTheory.selectionOperation_specified carrier inhabitant element predicate ⟨witness, holds⟩

theorem tail_choice_holds : model.models (HOL.SelectionProofs.principle choices.tailSelection) := by
  intro predicate _ witness _ holds
  exact HOL.HOLLightStandardTheory.selectionOperation_specified carrier inhabitant vector predicate ⟨witness, holds⟩

theorem field_injective : model.models (HOL.ConstructorProjections.fieldInjective operations.cons) := by
  intro n _ h _ t _ n' _ h' _ t' _ same
  change (ULift.up (h'.down :: t'.down) : ULift.{1} (List Bool)) = ULift.up (h.down :: t.down) at same
  have fields := List.cons.inj (congrArg ULift.down same)
  exact ⟨ULift.ext _ _ fields.1, ULift.ext _ _ fields.2⟩

theorem background_realizable :
    ∀ formula ∈ closedAssumptions operations choices, model.models formula := by
  intro formula member
  simp only [closedAssumptions, assumptions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact recursion_choice_holds
  · exact recursion_holds
  · exact head_choice_holds
  · exact tail_choice_holds
  · exact field_injective

def headImplication : HOL.ProofSyntax Const []
    (.imp (HOL.SelectionProofs.principle choices.headSelection)
      (.imp (HOL.ConstructorProjections.fieldInjective operations.cons) generated.headLaw)) :=
  .impI (.impI (head_law operations choices (.hyp 1) (.hyp 0)))

def tailImplication : HOL.ProofSyntax Const []
    (.imp (HOL.SelectionProofs.principle choices.tailSelection)
      (.imp (HOL.ConstructorProjections.fieldInjective operations.cons) generated.tailLaw)) :=
  .impI (.impI (tail_law operations choices (.hyp 1) (.hyp 0)))

theorem head_implication_free : headImplication.FunctionExtensionalityFree :=
  head_law_free operations choices _ _ True.intro True.intro

theorem tail_implication_free : tailImplication.FunctionExtensionalityFree :=
  tail_law_free operations choices _ _ True.intro True.intro

def sampleHead : HOL.ClosedTerm Const element := .app operations.head operations.nil

def headComputation := HOL.ConstructorProjections.second_at
  (Δ := [HOL.SelectionProofs.principle choices.headSelection, HOL.ConstructorProjections.fieldInjective operations.cons])
  choices.headSelection operations.cons operations.zero sampleHead operations.nil (.hyp 0) (.hyp 1)

def tailComputation := HOL.ConstructorProjections.third_at
  (Δ := [HOL.SelectionProofs.principle choices.tailSelection, HOL.ConstructorProjections.fieldInjective operations.cons])
  choices.tailSelection operations.cons operations.zero sampleHead operations.nil (.hyp 0) (.hyp 1)

theorem head_computation_free : headComputation.FunctionExtensionalityFree :=
  HOL.ConstructorProjections.second_at_free
    (Δ := [HOL.SelectionProofs.principle choices.headSelection, HOL.ConstructorProjections.fieldInjective operations.cons])
    choices.headSelection operations.cons operations.zero sampleHead operations.nil
    (.hyp 0) (.hyp 1) True.intro True.intro

theorem tail_computation_free : tailComputation.FunctionExtensionalityFree :=
  HOL.ConstructorProjections.third_at_free
    (Δ := [HOL.SelectionProofs.principle choices.tailSelection, HOL.ConstructorProjections.fieldInjective operations.cons])
    choices.tailSelection operations.cons operations.zero sampleHead operations.nil
    (.hyp 0) (.hyp 1) True.intro True.intro

theorem generated_head_holds : model.models generated.headLaw := by
  have valid := HOL.Soundness.extTheorem_sound headImplication.erase model
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
  exact valid head_choice_holds field_injective

theorem generated_tail_holds : model.models generated.tailLaw := by
  have valid := HOL.Soundness.extTheorem_sound tailImplication.erase model
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
  exact valid tail_choice_holds field_injective

noncomputable def losesHead : {type : HOL.Ty BaseSort} → Const type → HOL.Ty.denote.{0,0} carrier type
  | _, .original .cons => fun _ _ t => t
  | _, symbol => meaning symbol

noncomputable def badModel : HOL.HenkinModel.{0,0,0} BaseSort Const := .standard carrier losesHead

theorem lossy_constructor_refused : ¬ badModel.models (HOL.ConstructorProjections.fieldInjective operations.cons) := by
  intro condition
  have fields := condition (ULift.up 0) trivial (ULift.up false) trivial (ULift.up []) trivial
    (ULift.up 1) trivial (ULift.up true) trivial (ULift.up []) trivial rfl
  cases fields.1

def profile := NativeVectorComputationRows.Controls.profile

def roots (Γ : HOL.Ctx BaseSort) (left right : CTm Tower.Head Γ.length) (code : SchemaJudgmentCode.Code Tower.Head Γ.length) :=
  (AnnotatedPredicateReading.Roots.read? (entries operations choices profile) profile Γ left right code).map
    AnnotatedPredicateReading.Roots.Result.equality

def received (row : Row) :=
  AnnotatedPredicateReading.Interpreter.check? (church profile) (JudgmentReplay.decoder profile)
    AnnotatedPredicateReading.Interpreter.standard roots (row.parameters generated)
    (NativeVectorComputationRows.Controls.sourceContext row)
    (liftTm (row.rawLeft generated)) (liftTm (row.rawRight generated))
    (NativeVectorComputationRows.Controls.sourceType row)
    (NativeVectorComputationRows.Controls.contextCertificate row) (NativeVectorComputationRows.Controls.certificate row)

theorem nil_received : (received .nil).isSome = true := by decide +kernel
theorem cons_received : (received .cons).isSome = true := by decide +kernel

def receipt (row : Row) :=
  AnnotatedPredicateReading.Roots.readReceipt? (entries operations choices profile) profile (row.parameters generated)
    (NativeVectorComputationRows.Controls.citedRow row)

theorem original_addresses : (receipt .nil).map (fun result => result.parsed.index.val) = some 2 ∧
    (receipt .cons).map (fun result => result.parsed.index.val) = some 3 := by decide +kernel

theorem row_free : (rowProof operations choices .cons).FunctionExtensionalityFree := rowProof_free operations choices .cons

def nilResult :=
  (AnnotatedPredicateReading.Roots.read? (entries operations choices profile) profile (Row.nil.parameters generated)
    (liftTm (Row.nil.rawLeft generated)) (liftTm (Row.nil.rawRight generated))
    (NativeVectorComputationRows.Controls.citedRow .nil)).get (by decide +kernel)

theorem received_free : nilResult.equality.2.proof.FunctionExtensionalityFree :=
  nilResult.equality_free (entries_free operations choices profile)

theorem head_program_changes : generated.head ≠ operations.head := by
  intro same
  cases same

theorem tail_program_changes : generated.tail ≠ operations.tail := by
  intro same
  cases same

theorem disabled_refused :
    (AnnotatedPredicateReading.Roots.readReceipt? (entries operations choices profile) (fun _ => false)
      (Row.cons.parameters generated) (NativeVectorComputationRows.Controls.citedRow .cons)).isNone = true := by decide +kernel

theorem exchanged_fields_refused :
    (AnnotatedPredicateReading.Roots.readReceipt? (entries operations choices profile) profile
      (Row.cons.parameters generated) NativeVectorComputationRows.Controls.exchangedFields).isNone = true := by decide +kernel

#print axioms background_realizable
#print axioms generated_head_holds
#print axioms generated_tail_holds
#print axioms lossy_constructor_refused
#print axioms nil_received
#print axioms cons_received
#print axioms received_free
#print axioms head_computation_free
#print axioms tail_computation_free
#print axioms head_implication_free
#print axioms tail_implication_free
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorComputationRows.SelectedProjections.Controls
