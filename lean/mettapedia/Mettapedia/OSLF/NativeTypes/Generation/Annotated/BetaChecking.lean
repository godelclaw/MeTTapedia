import Mettapedia.OSLF.NativeTypes.Generation.Annotated.Checking
import Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls

open Mettapedia.OSLF.Framework

/-!
# Actual beta execution through an annotated generated template

The root template and its complete typing certificate are supplied to the
same generated output as the concrete catalogue. The independently checked
certificate earns the same scoped beta schema. The instance then uses the
actual captured argument and dependent body, with its native receipt retained.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.Annotated.BetaChecking

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Modal.Rules
open Mettapedia.OSLF.NativeTypes.Generation Mettapedia.OSLF.NativeTypes.Modal.Annotations
open Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer (generated term source)
open Mettapedia.GSLT.Examples.ScopedLamCongExecution (betaRule)

def annotation : SourceAnnotation :=
  {bound := [], programCarrier := term, focusBound := [], focusCarrier := term,
    descent := .here (.application 0 (.cons (.application 1 (.cons (.lambda .fvar) .nil))
      (.cons .fvar .nil)))}

theorem actual_source_annotation :
    (generated.instantiateAnnotatedSource? 0 annotation).isOk = true := by decide +kernel

theorem actual_raw_root : generated.rawSites[0]? =
    some ({context := .hole, focus := betaRule.left, declaration := 0, rule := betaRule} : Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Site) := by
  change (selectedSites Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.chosen.language {})[0]? = _
  rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.chosen_language]
  cbv

theorem actual_schema_annotation :
    (generated.instantiateAnnotatedSchema? 0 annotation).isOk = true := by
  have sourceSuccess := actual_source_annotation
  unfold Generated.instantiateAnnotatedSchema?
  cases sourceAt : generated.instantiateAnnotatedSource? 0 annotation with
  | error issue => simp [sourceAt, Except.isOk, Except.toBool] at sourceSuccess
  | ok checkedSource =>
      have retained := instantiated_source_input_retained sourceAt
      have sameSource : checkedSource.site =
          ({context := .hole, focus := betaRule.left, declaration := 0, rule := betaRule} : Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Site) := by
        have actualAt := checkedSource.present
        rw [retained.1, actual_raw_root] at actualAt
        exact Option.some.inj actualAt.symm
      have selectedRule : (Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.declaration, 0) ∈ generated.plan.rules.zipIdx := by
        rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.runtime_plan_actual]
        simp [Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.runtimePlan]
      obtain ⟨checked, engineAt, _⟩ := annotated_source_engine_complete checkedSource
        Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.declaration 0 selectedRule (by rw [sameSource]; rfl) (by rw [sameSource]; rfl)
      simp [engineAt, Except.isOk, Except.toBool]

def checked : AnnotatedSchema generated :=
  match result : generated.instantiateAnnotatedSchema? 0 annotation with
  | .ok accepted => accepted
  | .error issue => by
      have success := actual_schema_annotation
      rw [result] at success
      contradiction

theorem actual_annotated_schema_produced :
    generated.instantiateAnnotatedSchema? 0 annotation = .ok checked := by
  unfold checked
  split
  · rename_i accepted actualAt
    exact actualAt
  · rename_i issue failed
    have success := actual_schema_annotation
    rw [failed] at success
    contradiction

private theorem schema_ext {plan : Plan} (left right : Schema plan)
    (ordinal : left.ordinal = right.ordinal) (declaration : left.declaration = right.declaration)
    (position : left.position = right.position) (bound : left.bound = right.bound)
    (program : left.programCarrier = right.programCarrier) (focusBound : left.focusBound = right.focusBound)
    (focus : left.focusCarrier = right.focusCarrier) : left = right := by
  cases left
  cases right
  simp only [Schema.mk.injEq] at *
  exact ⟨ordinal, declaration, position, bound, program, focusBound, focus⟩

theorem schema_agrees_with_catalogue :
    checked.schema = Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.schema := by
  have retained := instantiated_schema_input_retained actual_annotated_schema_produced
  have actualAt := checked.source.present
  rw [retained.1, actual_raw_root] at actualAt
  have sameSource := Option.some.inj actualAt.symm
  let payload : RulePlan × Nat := checked.entry.val
  have ownMember : payload ∈ generated.plan.rules.zipIdx := checked.entry.property
  rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.runtime_plan_actual] at ownMember
  have own : checked.entry.val = (Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.declaration, 0) :=
    List.mem_singleton.mp ownMember
  let previousPayload : RulePlan × Nat :=
    (Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.schema.declaration, Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.schema.ordinal)
  have previousMember : previousPayload ∈ generated.plan.rules.zipIdx :=
    Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.schema.declared
  rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.runtime_plan_actual] at previousMember
  have previous : (Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.schema.declaration,
      Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.schema.ordinal) = (Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.declaration, 0) :=
    List.mem_singleton.mp previousMember
  have shape := Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.computed_schema_shape
  apply schema_ext
  · change checked.entry.val.2 = _
    rw [own]
    exact (congrArg Prod.snd previous).symm
  · change checked.entry.val.1 = _
    rw [own]
    exact (congrArg Prod.fst previous).symm
  · change checked.source.site.position = _
    rw [sameSource, shape.1]
    rfl
  · change checked.source.annotation.bound = _
    rw [retained.2, shape.2.1]
    rfl
  · change checked.source.annotation.programCarrier = _
    rw [retained.2, shape.2.2.2.2.1]
    rfl
  · change checked.source.annotation.focusBound = _
    rw [retained.2, shape.2.2.1]
    rfl
  · change checked.source.annotation.focusCarrier = _
    rw [retained.2, shape.2.2.2.1]
    rfl

def codes : ModalInstanceCodes generated checked.schema :=
  schema_agrees_with_catalogue.symm ▸ Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.codes

def transportDecisions {output : Generated} {left right : Schema output.plan}
    (equal : left = right) (rightCodes : ModalInstanceCodes output right)
    (rightDecisions : ModalInstanceDecisions rightCodes) : ModalInstanceDecisions (equal.symm ▸ rightCodes) := by
  cases equal
  exact rightDecisions

def decisions : ModalInstanceDecisions codes :=
  transportDecisions schema_agrees_with_catalogue Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.codes
    Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.decisions

theorem finite_schema_admitted : generated.schemaAdmitted? checked.schema = true := by
  rw [schema_agrees_with_catalogue]
  exact generated_schema_admitted
    (List.getElem_mem Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.catalogue_nonempty)

theorem transported_readout {output : Generated} {left right : Schema output.plan}
    (equal : left = right) (rightCodes : ModalInstanceCodes output right)
    (rightDecisions : ModalInstanceDecisions rightCodes) (assignment : ScopedRuleMatching.Assignment)
    (term : Pattern) (budget conversionBudget : Nat) :
    (output.checkModalInstance left (equal.symm ▸ rightCodes)
      (transportDecisions equal rightCodes rightDecisions) assignment term budget conversionBudget).map
        (fun result => result.result) =
    (output.checkModalInstance right rightCodes rightDecisions assignment term budget conversionBudget).map
      (fun result => result.result) := by
  cases equal
  rfl

theorem actual_annotated_run_readout (budget conversionBudget : Nat) :
    (generated.checkAnnotatedModalInstance checked codes decisions
      Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.supplied source budget conversionBudget).map
        (fun result => result.result) =
      .ok (Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.actualRun budget conversionBudget).result := by
  rw [annotated_modal_check_eq_concrete checked codes decisions
    Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.supplied source budget conversionBudget finite_schema_admitted]
  dsimp only [codes, decisions]
  rw [transported_readout, Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.actual_generated_run]
  rfl

theorem actual_beta_answer :
    (generated.checkAnnotatedModalInstance checked codes decisions
      Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.supplied source 40 0).map (fun result => result.result) =
      .ok (.decided true) := by
  rw [actual_annotated_run_readout, Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.actual_generated_beta_query]

theorem paused_beta_unknown :
    (generated.checkAnnotatedModalInstance checked codes decisions
      Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.supplied source 0 0).map (fun result => result.result) =
      .ok .unknown := by
  rw [actual_annotated_run_readout, Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.zero_budget_instance_unknown]

theorem native_receipt_retained :
    Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.response.outcome.receipt =
      Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.actualAnswer.val :=
  Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.actual_receipt_is_preserved

theorem actual_annotated_beta_outcome :
    Nonempty (Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome checked.schema source
      Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.supplied codes.continuation) := by
  have positive := actual_beta_answer
  cases computed : generated.checkAnnotatedModalInstance checked codes decisions
      Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.supplied source 40 0 with
  | error issue => simp [computed, Except.map] at positive
  | ok result =>
      simp only [computed, Except.map] at positive
      exact generated_annotated_instance_positive_sound computed (Except.ok.inj positive)

end Mettapedia.OSLF.NativeTypes.Generation.Annotated.BetaChecking
