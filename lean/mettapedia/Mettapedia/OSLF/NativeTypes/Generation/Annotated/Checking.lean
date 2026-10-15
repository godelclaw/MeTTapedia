import Mettapedia.OSLF.NativeTypes.Generation.Annotated.Coverage
import Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingLaws

open Mettapedia.OSLF.Framework

/-!
# Executing modal judgments from annotated generated schemas

Checked source annotations extend concrete catalogue typing, not the
operational semantics. This route admits the same scoped assignment, calls
the same certified source and RHS frontier engine, and reads the same complete
native responses. It checks a specified full instance, not an unbounded
universal family of rely requests.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralOccurrenceFrontier GeneralOccurrenceSemantics
open Mettapedia.OSLF.NativeTypes.Modal.Rules

/-- The annotated input reaches the original operational instance engine.
Formation still obeys the selected logic and actual equation profile. -/
def Generated.checkAnnotatedModalInstance (generated : Generated) (checked : AnnotatedSchema generated)
    (codes : ModalInstanceCodes generated checked.schema) (decisions : ModalInstanceDecisions codes)
    (assignment : ScopedRuleMatching.Assignment) (term : Pattern) (budget conversionBudget : Nat) :
    Except ModalInstanceIssue (ModalInstanceRun codes assignment term) :=
  if (generated.annotatedModalFormer? checked codes.actualInputs).isSome then
    match admitModalInstance? codes decisions assignment term with
    | .error reason => .error reason
    | .ok request =>
      let sourceState := generated.execute checked.schema.bound checked.schema.programCarrier request.source budget
      let targetState := generated.execute checked.schema.bound checked.schema.programCarrier request.target conversionBudget
      .ok {
        request := request
        sourceState := sourceState
        targetState := targetState
        responses := modalResponses decisions request sourceState targetState
        result := modalInstanceReadout decisions request sourceState targetState}
  else .error .unavailableFormer

theorem generated_annotated_instance_positive_sound {generated : Generated}
    {checked : AnnotatedSchema generated} {codes : ModalInstanceCodes generated checked.schema}
    {decisions : ModalInstanceDecisions codes} {assignment : ScopedRuleMatching.Assignment}
    {term : Pattern} {budget conversionBudget : Nat} {result : ModalInstanceRun codes assignment term}
    (computed : generated.checkAnnotatedModalInstance checked codes decisions assignment term budget conversionBudget = .ok result)
    (positive : result.result = .decided true) :
    Nonempty (Outcome checked.schema term assignment codes.continuation) := by
  unfold Generated.checkAnnotatedModalInstance at computed
  split at computed
  · split at computed
    · cases computed
    · cases computed
      exact modal_instance_positive_sound _ decisions _ _ positive
  · cases computed

theorem generated_annotated_instance_negative_sound {generated : Generated}
    {checked : AnnotatedSchema generated} {codes : ModalInstanceCodes generated checked.schema}
    {decisions : ModalInstanceDecisions codes} {assignment : ScopedRuleMatching.Assignment}
    {term : Pattern} {budget conversionBudget : Nat} {result : ModalInstanceRun codes assignment term}
    (computed : generated.checkAnnotatedModalInstance checked codes decisions assignment term budget conversionBudget = .ok result)
    (negative : result.result = .decided false) :
    ¬ Nonempty (Outcome checked.schema term assignment codes.continuation) := by
  unfold Generated.checkAnnotatedModalInstance at computed
  split at computed
  · split at computed
    · cases computed
    · cases computed
      exact modal_instance_negative_sound _ decisions _ _ negative
  · cases computed

theorem modal_response_native_origin {generated : Generated} {schema : Schema generated.plan}
    {codes : ModalInstanceCodes generated schema} {assignment : ScopedRuleMatching.Assignment} {term : Pattern}
    (decisions : ModalInstanceDecisions codes) (request : ModalInstanceRequest codes assignment term)
    (sourceState : State request.sourceRequest) (targetState : State request.targetRequest)
    (response : CheckedModalInstance request)
    (member : response ∈ modalResponses decisions request sourceState targetState) :
    ∃ answer ∈ sourceState.answers, response.outcome.receipt = answer.val := by
  obtain ⟨answer, answerMember, responseAt⟩ := List.mem_filterMap.mp member
  refine ⟨answer, answerMember, ?_⟩
  unfold checkModalResponse? at responseAt
  split at responseAt
  · cases responseAt
  · split at responseAt
    · cases responseAt
      rfl
    · cases responseAt

/-- Every successful response retains the exact receipt from the actual
native source execution. Equal answer targets do not erase its origins. -/
theorem generated_annotated_response_native_origin {generated : Generated}
    {checked : AnnotatedSchema generated} {codes : ModalInstanceCodes generated checked.schema}
    {decisions : ModalInstanceDecisions codes} {assignment : ScopedRuleMatching.Assignment}
    {term : Pattern} {budget conversionBudget : Nat} {result : ModalInstanceRun codes assignment term}
    (computed : generated.checkAnnotatedModalInstance checked codes decisions assignment term budget conversionBudget = .ok result)
    (response : CheckedModalInstance result.request) (member : response ∈ result.responses) :
    ∃ answer ∈ result.sourceState.answers, response.outcome.receipt = answer.val := by
  unfold Generated.checkAnnotatedModalInstance at computed
  split at computed
  · split at computed
    · cases computed
    · cases computed
      exact modal_response_native_origin decisions _ _ _ response member
  · cases computed

private theorem start_answers_empty (request : Request) : (start request).answers = [] := by
  unfold start
  split <;> rfl

private theorem start_not_complete (request : Request) : complete request (start request) = false := by
  unfold start
  split
  · rfl
  · simp [complete]

/-- A zero source budget cannot become a negative instance when the selected
continuation accepts its exact RHS; it remains unknown at every RHS budget. -/
theorem generated_annotated_zero_budget_unknown {generated : Generated}
    {checked : AnnotatedSchema generated} {codes : ModalInstanceCodes generated checked.schema}
    {decisions : ModalInstanceDecisions codes} {assignment : ScopedRuleMatching.Assignment}
    {term : Pattern} {conversionBudget : Nat} {result : ModalInstanceRun codes assignment term}
    (computed : generated.checkAnnotatedModalInstance checked codes decisions assignment term 0 conversionBudget = .ok result)
    (accepts : (codes.inputs.2 assignment).meaning result.request.target) :
    result.result = .unknown := by
  unfold Generated.checkAnnotatedModalInstance at computed
  split at computed
  · split at computed
    · cases computed
    · cases computed
      apply unfinished_empty_instance_unknown _ decisions
      · exact start_answers_empty _
      · exact start_not_complete _
      · exact accepts
  · cases computed

/-- Missing actual operational admission remains unresolved after successful
source typing; it cannot masquerade as a completed modal query. -/
theorem unadmitted_annotated_source_unresolved {generated : Generated} {index : Nat}
    {annotation : SourceAnnotation} {source : AnnotatedSource generated}
    (produced : generated.instantiateAnnotatedSource? index annotation = .ok source)
    (missing : source.ruleEntry? = none) :
    generated.instantiateAnnotatedSchema? index annotation =
      .error (.unresolvedOperationalDeclaration source.site.declaration) := by
  unfold Generated.instantiateAnnotatedSchema?
  simp only [produced]
  have noSchema : source.engineSchema? = none := by
    unfold AnnotatedSource.engineSchema?
    split
    · rfl
    · rename_i entry found
      rw [missing] at found
      contradiction
  rw [noSchema]

/-- The checked annotation route agrees with concrete catalogue formation
where that finite catalogue also contains the exact schema. -/
theorem annotated_modal_former_status_eq_concrete {generated : Generated}
    (checked : AnnotatedSchema generated)
    (inputs : ModalInputs checked.schema (generated.modalParameters? checked.schema))
    (admitted : generated.schemaAdmitted? checked.schema = true) :
    (generated.annotatedModalFormer? checked inputs).isSome = (generated.modalFormer? checked.schema inputs).isSome := by
  unfold Generated.annotatedModalFormer? Generated.modalFormer?
  by_cases enabled : generated.equationAdmission = some true ∧ generated.logicFragment.core.modal = true
  · rw [if_pos enabled, if_pos ⟨enabled.1, enabled.2, admitted⟩]
    split
    · rename_i missing
      split
      · rfl
      · rename_i parameters found
        rw [missing] at found
        contradiction
    · rename_i parameters found
      split
      · rename_i missing
        rw [missing] at found
        contradiction
      · rfl
  · rw [if_neg enabled, if_neg (by intro valid; exact enabled ⟨valid.1, valid.2.1⟩)]

/-- Both typing admission routes call the identical engine on the identical
requests when the same schema is in the concrete catalogue. -/
theorem annotated_modal_check_eq_concrete {generated : Generated}
    (checked : AnnotatedSchema generated) (codes : ModalInstanceCodes generated checked.schema)
    (decisions : ModalInstanceDecisions codes) (assignment : ScopedRuleMatching.Assignment)
    (term : Pattern) (budget conversionBudget : Nat)
    (admitted : generated.schemaAdmitted? checked.schema = true) :
    generated.checkAnnotatedModalInstance checked codes decisions assignment term budget conversionBudget =
      generated.checkModalInstance checked.schema codes decisions assignment term budget conversionBudget := by
  unfold Generated.checkAnnotatedModalInstance Generated.checkModalInstance
  rw [annotated_modal_former_status_eq_concrete checked codes.actualInputs admitted]
  dsimp only [ModalInstanceRequest.sourceRequest, ModalInstanceRequest.targetRequest]
  split
  ·
    split
    · rename_i issue failed
      split
      · rename_i reason otherFailed
        have same : issue = reason := Except.error.inj (failed.symm.trans otherFailed)
        subst reason
        rfl
      · rename_i request accepted
        rw [failed] at accepted
        contradiction
    · rename_i request accepted
      split
      · rename_i issue failed
        rw [failed] at accepted
        contradiction
      · rename_i actual actualAt
        have same : request = actual := Except.ok.inj (accepted.symm.trans actualAt)
        subst actual
        rfl
  · rfl

end Mettapedia.OSLF.NativeTypes.Generation
