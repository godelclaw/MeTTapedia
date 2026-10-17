import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceCertificate
import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobArchiveCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobCoverage

/-!
# Independent semantic meaning of a retained frontier certificate

The checker earns equation-class closure and full primitive occurrence
coverage from the actual archived executions. The semantic judgments are
independent of the machine; no completeness field is supplied by a caller.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralOccurrenceKeys GeneralOccurrenceSemantics
open Mettapedia.OSLF.Framework.GeneralFiniteTermUniverse

theorem Admitted.stratified {request : Request} (admitted : Admitted request) :
    GeneralPremise.checkStepStratification (GeneralPlanEnvironment.environment request.plan).language = true := by
  have accepted := admitted.compiled ▸ admitted.accepted
  rw [admitted.compiled, GeneralPlanEnvironment.compiled_environment]
  exact (GeneralExecutionAdmission.complete_snapshot_checks accepted).2.2.2

theorem certified_equation_occurrence {request : Request} {state : State request}
    (admitted : Admitted request) (checked : checkCertificate request state = true)
    (source : Pattern) (within : source ∈ request.universe) (receipt : GeneralEquationJobs.Receipt)
    (valid : GeneralEquationJobs.Completion request.plan request.bound request.expected source receipt) :
    ∃ edge ∈ state.edges, edge.source = source ∧ edge.receipt = receipt := by
  have fields := (checkCertificate_iff request state).mp checked
  have jobMember := (GeneralEquationJobs.jobs_iff _ _ _ _ _).mpr valid.job
  obtain ⟨archive, _, sameSource, sameKey, completed, read⟩ := fields.2.2.1 source within receipt.job jobMember
  subst source
  have sameJob := equationJob_injective valid.job archive.frame.licensed sameKey.symm
  have member := GeneralEquationJobExecution.completed_answers_complete archive.frame.reachable
    completed admitted.stratified receipt valid sameJob
  obtain ⟨answer, present, sameReceipt⟩ := List.mem_map.mp member
  have published := read answer present
  rw [sameReceipt] at published
  obtain ⟨edge, edgeMember, same⟩ := List.mem_map.mp published
  have sourceEq := congrArg Prod.fst same
  have keyEq := congrArg Prod.snd same
  change edge.source = archive.frame.source at sourceEq
  change equationReplayRecord edge.receipt = equationReplayRecord receipt at keyEq
  refine ⟨edge, edgeMember, sourceEq, ?_⟩
  apply equationReplayRecord_injective _ valid keyEq
  rw [← sourceEq]
  exact edge.valid

theorem certified_rule_occurrence {request : Request} {state : State request}
    (admitted : Admitted request) (checked : checkCertificate request state = true)
    (representative : Representative request) (visited : representative ∈ state.visited)
    (receipt : GeneralRuleJobs.Receipt)
    (valid : receipt.Valid request.plan request.bound request.expected representative.pattern) :
    ∃ answer ∈ state.answers,
      answer.val.representative = representative.pattern ∧ answer.val.firing = receipt := by
  have fields := (checkCertificate_iff request state).mp checked
  have jobMember := (GeneralRuleJobs.jobs_spec _ _ _ _ _).mpr valid.1
  obtain ⟨archive, _, sameSource, sameKey, completed, read⟩ :=
    fields.2.2.2.1 representative visited receipt.job jobMember
  have validAt : receipt.Valid request.plan request.bound request.expected archive.frame.representative.pattern := by
    rw [sameSource]
    exact valid
  have sameJob := ruleJob_injective validAt.1 archive.frame.licensed sameKey.symm
  have localMember : receipt ∈ archive.frame.state.answers.map Subtype.val := by
    rw [GeneralRuleJobExecution.completed_reachable_finishState archive.frame.reachable completed]
    exact (GeneralRuleJobExecution.finishState_receipt_iff
      (ruleRequest request archive.frame.representative archive.frame.job) archive.frame.licensed
      admitted.stratified receipt).mpr ⟨validAt, sameJob⟩
  obtain ⟨innerAnswer, present, sameReceipt⟩ := List.mem_map.mp localMember
  have published := read innerAnswer present
  rw [sameReceipt] at published
  obtain ⟨answer, answerMember, same⟩ := List.mem_map.mp published
  have sourceEq := congrArg Prod.fst same
  have keyEq := congrArg Prod.snd same
  change answer.val.representative = archive.frame.representative.pattern at sourceEq
  change ruleReplayRecord answer.val.firing = ruleReplayRecord receipt at keyEq
  refine ⟨answer, answerMember, sourceEq.trans sameSource, ?_⟩
  apply ruleReplayRecord_injective _ validAt keyEq
  rw [← sourceEq]
  exact answer.property.2

theorem represented_within {request : Request} (admitted : Admitted request)
    (state : State request) (source : Pattern) (member : source ∈ representedPatterns request state) :
    source ∈ request.universe := by
  obtain ⟨representative, _, same⟩ := List.mem_map.mp member
  subst source
  exact admitted.representative_within representative

theorem certified_representatives_closed {request : Request} {state : State request}
    (admitted : Admitted request) (checked : checkCertificate request state = true)
    (source : Pattern) (member : source ∈ representedPatterns request state) (target : Pattern)
    (edge : Equation request.plan request.bound request.expected source target ∨
      Equation request.plan request.bound request.expected target source) :
    target ∈ representedPatterns request state := by
  have adjacency := ((checkCertificate_iff request state).mp checked).2.2.2.2
  have sourceWithin := represented_within admitted state source member
  rcases edge with ⟨receipt, valid, targetEq⟩ | ⟨receipt, valid, sourceEq⟩
  · obtain ⟨actual, present, sameSource, sameReceipt⟩ :=
      certified_equation_occurrence admitted checked source sourceWithin receipt valid
    have answer := (adjacency actual present).1 (sameSource ▸ member)
    simpa only [sameReceipt, targetEq] using answer
  · have accepted := admitted.compiled ▸ admitted.accepted
    have validCompiled := admitted.compiled ▸ valid
    have targetWithin : target ∈ request.universe := by
      have upper : receipt.target ∈ request.universe := sourceEq ▸ sourceWithin
      have bound := GeneralEquationReverseBounds.compiled_reverse_universe_closed
        (root := request.root) accepted validCompiled upper
      simpa only [← admitted.compiled, Request.universe] using bound
    obtain ⟨actual, present, sameTarget, sameReceipt⟩ :=
      certified_equation_occurrence admitted checked target targetWithin receipt valid
    have current : actual.receipt.target ∈ representedPatterns request state := by
      simpa only [sameReceipt, sourceEq] using member
    simpa only [sameTarget] using (adjacency actual present).2 current

theorem certified_representatives_exact {request : Request} {state : State request}
    (admitted : Admitted request) (checked : checkCertificate request state = true) (source : Pattern) :
    source ∈ representedPatterns request state ↔
      Relation.EqvGen (Equation request.plan request.bound request.expected) request.root source := by
  constructor
  · intro member
    obtain ⟨representative, _, same⟩ := List.mem_map.mp member
    subst source
    exact representative.justified.equivalent
  · intro related
    have closure := Mettapedia.OSLF.Framework.FiniteEquationCoverage.eqvGen_membership_of_closed
      (Equation request.plan request.bound request.expected) (representedPatterns request state)
      (certified_representatives_closed admitted checked) related
    exact closure.mp ((checkCertificate_iff request state).mp checked).2.1

theorem certified_physical_occurrence {request : Request} {state : State request}
    (admitted : Admitted request) (checked : checkCertificate request state = true)
    (source : Pattern) (related : Relation.EqvGen
      (Equation request.plan request.bound request.expected) request.root source)
    (receipt : GeneralRuleJobs.Receipt)
    (valid : receipt.Valid request.plan request.bound request.expected source) :
    ∃ answer ∈ state.answers, answer.val.representative = source ∧ answer.val.firing = receipt := by
  have represented := (certified_representatives_exact admitted checked source).mpr related
  obtain ⟨representative, member, same⟩ := List.mem_map.mp represented
  subst source
  exact certified_rule_occurrence admitted checked representative member receipt valid

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
