import Mettapedia.OSLF.NativeTypes.Generation.ModalChecking

open Mettapedia.OSLF.Framework

/-!
# Earned readouts of specified-contractum instance queries

A discovered response proves the exact authored RHS and the continuation
after its complete assignment is substituted. A negative answer either has
a false continuation at that RHS or retains checked source and target-class
coverage. An unfinished empty search does not rule out an instance.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralOccurrenceFrontier GeneralOccurrenceSemantics
open Mettapedia.OSLF.NativeTypes.Modal.Rules Mettapedia.OSLF.NativeTypes.Modal.Formation

section Instance

variable {generated : Generated} {schema : Schema generated.plan}
  {codes : ModalInstanceCodes generated schema}
  {assignment : ScopedRuleMatching.Assignment} {term : Pattern}
  (request : ModalInstanceRequest codes assignment term)

theorem contractum_path_complete (state : State request.targetRequest)
    (admitted : Admitted request.targetRequest)
    (checked : checkCertificate request.targetRequest state = true)
    (target : Pattern)
    (related : Relation.EqvGen (Equation generated.plan schema.bound schema.programCarrier)
      request.target target) :
    ∃ path, contractumPath? request state target = some path := by
  by_cases same : request.target = target
  · apply Option.isSome_iff_exists.mp
    simp only [contractumPath?, dif_pos same, Option.isSome_some]
  · have actual : Relation.EqvGen
        (Equation request.targetRequest.plan request.targetRequest.bound request.targetRequest.expected)
        request.targetRequest.root target := by
      change Relation.EqvGen (Equation generated.plan schema.bound schema.programCarrier)
        request.targetRequest.root target
      simpa only [request.target_root] using related
    have member := (certified_representatives_exact admitted checked target).mpr actual
    obtain ⟨representative, found⟩ := visitedAt_found request.targetRequest state target member
    apply Option.isSome_iff_exists.mp
    simp only [contractumPath?, dif_neg same, found, Option.isSome_some]

theorem instance_outcome_agreements
    (outcome : Outcome schema term assignment codes.continuation) :
    outcome.source = request.source ∧ outcome.target = request.target := by
  exact ⟨Option.some.inj (outcome.filling.symm.trans request.filling),
    Option.some.inj (outcome.rhs.symm.trans request.rhs)⟩

theorem instance_outcome_step
    (outcome : Outcome schema term assignment codes.continuation) :
    (gslt generated.plan schema.bound schema.programCarrier).Step request.source request.target := by
  have same := instance_outcome_agreements request outcome
  have step : (gslt generated.plan schema.bound schema.programCarrier).Step
      outcome.source outcome.target :=
    ⟨outcome.receipt.representative, outcome.receipt.firing,
      outcome.valid.1.equivalent, outcome.valid.2, outcome.targetConversion⟩
  simpa only [same.1, same.2] using step

theorem instance_outcome_continuation
    (outcome : Outcome schema term assignment codes.continuation) :
    (codes.inputs.2 assignment).meaning request.target := by
  have same := (instance_outcome_agreements request outcome).2
  have accepts : (codes.inputs.2 assignment).meaning outcome.target := outcome.certificate.down
  simpa only [same] using accepts

theorem modal_response_exists (decisions : ModalInstanceDecisions codes)
    (targetState : State request.targetRequest) (answer : Answer request.sourceRequest)
    (path : ∃ conversion, contractumPath? request targetState answer.val.target = some conversion)
    (accepts : (codes.inputs.2 assignment).meaning request.target) :
    ∃ response, checkModalResponse? decisions request targetState answer = some response := by
  obtain ⟨conversion, found⟩ := path
  have approved : @decide ((codes.inputs.2 assignment).meaning request.target)
      (decisions.continuation assignment request.target) = true :=
    @decide_eq_true ((codes.inputs.2 assignment).meaning request.target)
      (decisions.continuation assignment request.target) accepts
  apply Option.isSome_iff_exists.mp
  unfold checkModalResponse?
  split
  · rename_i missing
    simp only [found] at missing
    cases missing
  · simp only [dif_pos approved, Option.isSome_some]

/-- Instance completeness is earned from both actual coverage certificates.
It does not replace an arbitrary rely family with a finite provider table. -/
theorem modal_responses_complete (decisions : ModalInstanceDecisions codes)
    (sourceState : State request.sourceRequest) (targetState : State request.targetRequest)
    (sourceAdmitted : Admitted request.sourceRequest)
    (targetAdmitted : Admitted request.targetRequest)
    (sourceChecked : checkCertificate request.sourceRequest sourceState = true)
    (targetChecked : checkCertificate request.targetRequest targetState = true)
    (outcome : Outcome schema term assignment codes.continuation) :
    ∃ response, response ∈ modalResponses decisions request sourceState targetState := by
  have step := instance_outcome_step request outcome
  have actual : (gslt request.sourceRequest.plan request.sourceRequest.bound
      request.sourceRequest.expected).Step request.sourceRequest.root request.target := by
    change (gslt generated.plan schema.bound schema.programCarrier).Step
      request.sourceRequest.root request.target
    simpa only [request.source_root] using step
  obtain ⟨answer, member, after⟩ :=
    (certified_successor_classes sourceAdmitted sourceChecked request.target).mpr actual
  have converted := contractum_path_complete request targetState targetAdmitted targetChecked
    answer.val.target after.symm
  obtain ⟨response, observed⟩ := modal_response_exists request decisions targetState answer converted
    (instance_outcome_continuation request outcome)
  exact ⟨response, List.mem_filterMap.mpr ⟨answer, member, observed⟩⟩

theorem modal_instance_positive_sound (decisions : ModalInstanceDecisions codes)
    (sourceState : State request.sourceRequest) (targetState : State request.targetRequest)
    (positive : modalInstanceReadout decisions request sourceState targetState = .decided true) :
    Nonempty (Outcome schema term assignment codes.continuation) := by
  unfold modalInstanceReadout at positive
  split at positive
  · rename_i nonempty
    cases responses : modalResponses decisions request sourceState targetState with
    | nil =>
      simp only [responses, List.isEmpty_nil, Bool.not_true] at nonempty
      cases nonempty
    | cons response tail => exact ⟨response.outcome⟩
  · split at positive
    · cases positive
    · split at positive <;> cases positive

theorem modal_instance_positive_complete (decisions : ModalInstanceDecisions codes)
    (sourceState : State request.sourceRequest) (targetState : State request.targetRequest)
    (sourceAdmitted : Admitted request.sourceRequest)
    (targetAdmitted : Admitted request.targetRequest)
    (sourceChecked : checkCertificate request.sourceRequest sourceState = true)
    (targetChecked : checkCertificate request.targetRequest targetState = true)
    (outcome : Outcome schema term assignment codes.continuation) :
    modalInstanceReadout decisions request sourceState targetState = .decided true := by
  obtain ⟨response, member⟩ := modal_responses_complete request decisions sourceState targetState
    sourceAdmitted targetAdmitted sourceChecked targetChecked outcome
  cases responses : modalResponses decisions request sourceState targetState with
  | nil => simp only [responses, List.not_mem_nil] at member
  | cons head tail => simp [modalInstanceReadout, responses]

theorem modal_instance_negative_sound (decisions : ModalInstanceDecisions codes)
    (sourceState : State request.sourceRequest) (targetState : State request.targetRequest)
    (negative : modalInstanceReadout decisions request sourceState targetState = .decided false) :
    ¬ Nonempty (Outcome schema term assignment codes.continuation) := by
  rintro ⟨outcome⟩
  have original := negative
  unfold modalInstanceReadout at negative
  split at negative
  · cases negative
  · split at negative
    · rename_i rejected
      have accepts := instance_outcome_continuation request outcome
      have approved : @decide ((codes.inputs.2 assignment).meaning request.target)
          (decisions.continuation assignment request.target) = true :=
        @decide_eq_true ((codes.inputs.2 assignment).meaning request.target)
          (decisions.continuation assignment request.target) accepts
      simp only [approved, Bool.not_true, Bool.false_eq_true] at rejected
    · split at negative
      · rename_i certified
        simp only [Bool.and_eq_true] at certified
        have sourceAdmitted := sourceAdmission_sound certified.1.1.1 rfl
        have targetAdmitted := sourceAdmission_sound certified.1.2 rfl
        have positive := modal_instance_positive_complete request decisions sourceState targetState
          sourceAdmitted targetAdmitted certified.1.1.2 certified.2 outcome
        rw [original] at positive
        cases positive
      · cases negative

theorem unfinished_empty_instance_unknown (decisions : ModalInstanceDecisions codes)
    (sourceState : State request.sourceRequest) (targetState : State request.targetRequest)
    (empty : sourceState.answers = []) (unfinished : complete request.sourceRequest sourceState = false)
    (accepts : (codes.inputs.2 assignment).meaning request.target) :
    modalInstanceReadout decisions request sourceState targetState = .unknown := by
  have approved : @decide ((codes.inputs.2 assignment).meaning request.target)
      (decisions.continuation assignment request.target) = true :=
    @decide_eq_true ((codes.inputs.2 assignment).meaning request.target)
      (decisions.continuation assignment request.target) accepts
  simp [modalInstanceReadout, modalResponses, empty, approved,
    unfinished_certificate_rejected request.sourceRequest sourceState unfinished]

end Instance

/-- The public algorithm's result has the receipt semantics above; an
arbitrary value of the result record is not used as a correctness premise. -/
theorem generated_modal_instance_positive_sound {generated : Generated}
    {schema : Schema generated.plan} {codes : ModalInstanceCodes generated schema}
    {decisions : ModalInstanceDecisions codes} {assignment : ScopedRuleMatching.Assignment}
    {term : Pattern} {budget conversionBudget : Nat} {result : ModalInstanceRun codes assignment term}
    (computed : generated.checkModalInstance schema codes decisions assignment term budget conversionBudget = .ok result)
    (positive : result.result = .decided true) :
    Nonempty (Outcome schema term assignment codes.continuation) := by
  unfold Generated.checkModalInstance at computed
  split at computed
  · split at computed
    · cases computed
    · cases computed
      exact modal_instance_positive_sound _ decisions _ _ positive
  · cases computed

theorem generated_modal_instance_negative_sound {generated : Generated}
    {schema : Schema generated.plan} {codes : ModalInstanceCodes generated schema}
    {decisions : ModalInstanceDecisions codes} {assignment : ScopedRuleMatching.Assignment}
    {term : Pattern} {budget conversionBudget : Nat} {result : ModalInstanceRun codes assignment term}
    (computed : generated.checkModalInstance schema codes decisions assignment term budget conversionBudget = .ok result)
    (negative : result.result = .decided false) :
    ¬ Nonempty (Outcome schema term assignment codes.continuation) := by
  unfold Generated.checkModalInstance at computed
  split at computed
  · split at computed
    · cases computed
    · cases computed
      exact modal_instance_negative_sound _ decisions _ _ negative
  · cases computed

end Mettapedia.OSLF.NativeTypes.Generation
