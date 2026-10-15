import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceLocalCertificate
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceUniversalCompletion

/-!
# Effective completion from checked equation-free profiles

The checked static profile resolves the actual rule and premise computations.
Together with the constructive local work bound this earns a complete retained
frontier and its independently interpreted certificate for every admitted
source, including arbitrary binder contexts and finite provider snapshots.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier.LocalEquationFree

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem start_sources_typed (request : Request) : AgendaSourcesTyped request (start request) := by
  intro task member
  unfold start at member
  split at member
  · simp only [List.mem_singleton] at member
    subst task
    trivial
  · exact False.elim (List.not_mem_nil member)

theorem reachable_sources_typed {request : Request} (admitted : Admitted request)
    {state : State request} (reached : Reachable request state) : AgendaSourcesTyped request state := by
  induction reached with
  | start => exact start_sources_typed request
  | tick _ ih => exact GeneralOccurrenceFrontier.tick_sources_typed admitted ih

theorem no_equation_resolution {request : Request} (empty : request.plan.equations = []) :
    EquationResolution request := by
  intro source job _ licensed
  have selected := licensed.1
  rw [empty] at selected
  exact False.elim (List.not_mem_nil selected)

theorem start_resolved {request : Request} (admitted : Admitted request) :
    (start request).unresolved = [] := by
  have absent : request.plan.obligations = [] := List.isEmpty_iff.mp admitted.accepted
  have checked : sourceChecked request = true := checkOpenPatternWellSorted_complete admitted.rootSorted
  simp only [start, checked, if_true, absent, List.map_nil]

theorem reachable_resolved {request : Request} (admitted : Admitted request)
    (empty : request.plan.equations = []) (rules : RuleResolution request)
    {state : State request} (reached : Reachable request state) : state.unresolved = [] := by
  induction reached with
  | start => exact start_resolved admitted
  | tick reached ih =>
      exact GeneralOccurrenceFrontier.tick_resolved (no_equation_resolution empty) rules
        (reachable_sources_typed admitted reached) ih

theorem reachable_equation_coverage_trivial {request : Request} (admitted : Admitted request)
    (empty : request.plan.equations = []) {state : State request} (reached : Reachable request state) :
    state.universeScanned = true := by
  induction reached with
  | start =>
      have checked : sourceChecked request = true := checkOpenPatternWellSorted_complete admitted.rootSorted
      simp only [start, checked, if_true, empty, List.isEmpty_nil]
  | @tick state _ ih =>
      cases agenda : state.agenda <;> simp only [tick, agenda, ih, Bool.true_or]

theorem complete_at_workBound_of_rule_resolution {request : Request} (admitted : Admitted request)
    (empty : request.plan.equations = []) (rules : RuleResolution request) :
    complete request (run request (workBound request)) = true := by
  have reached := run_reachable request (workBound request)
  exact (complete_iff request _).mpr
    ⟨workBound_drains empty, reachable_resolved admitted empty rules reached,
      reachable_equation_coverage_trivial admitted empty reached⟩

theorem certificate_at_workBound_of_rule_resolution {request : Request} (admitted : Admitted request)
    (empty : request.plan.equations = []) (rules : RuleResolution request) :
    checkCertificate request (run request (workBound request)) = true :=
  completed_checkCertificate admitted empty (run_reachable request _)
    (complete_at_workBound_of_rule_resolution admitted empty rules)

/-- Static admission derives resolution from the actual provider, premise,
projection and child-stratum checks. No completeness law is an input. -/
theorem complete_at_workBound {request : Request} (admitted : Admitted request)
    (empty : request.plan.equations = [])
    (checked : GeneralExecutionTotalAdmission.checkGeneric request.plan = true) :
    complete request (run request (workBound request)) = true :=
  complete_at_workBound_of_rule_resolution admitted empty
    (GeneralOccurrenceFrontier.generic_rule_resolution admitted checked)

theorem certificate_at_workBound {request : Request} (admitted : Admitted request)
    (empty : request.plan.equations = [])
    (checked : GeneralExecutionTotalAdmission.checkGeneric request.plan = true) :
    checkCertificate request (run request (workBound request)) = true :=
  certificate_at_workBound_of_rule_resolution admitted empty
    (GeneralOccurrenceFrontier.generic_rule_resolution admitted checked)

/-- The admission decision retains source sorting, the compiled foundation,
the genuinely empty equation selection and the actual static execution gates. -/
def admittedProfile (request : Request) : Bool :=
  request.plan.complete && request.plan.equations.isEmpty &&
    GeneralExecutionTotalAdmission.checkGeneric request.plan && sourceChecked request

theorem admittedProfile_sound {request : Request}
    (compiled : request.plan = GeneralExecutionAdmission.compile request.plan.snapshot request.plan.permissions)
    (accepted : admittedProfile request = true) :
    Admitted request ∧ request.plan.equations = [] ∧
      GeneralExecutionTotalAdmission.checkGeneric request.plan = true := by
  simp only [admittedProfile, Bool.and_eq_true] at accepted
  exact ⟨⟨compiled, accepted.1.1.1, checkOpenPatternWellSorted_sound accepted.2⟩,
    List.isEmpty_iff.mp accepted.1.1.2, accepted.1.2⟩

theorem admitted_profile_effective_completion {request : Request}
    (compiled : request.plan = GeneralExecutionAdmission.compile request.plan.snapshot request.plan.permissions)
    (accepted : admittedProfile request = true) :
    complete request (run request (workBound request)) = true ∧
      checkCertificate request (run request (workBound request)) = true := by
  obtain ⟨admitted, empty, checked⟩ := admittedProfile_sound compiled accepted
  exact ⟨complete_at_workBound admitted empty checked, certificate_at_workBound admitted empty checked⟩

theorem admitted_profile_exact_successors {request : Request}
    (compiled : request.plan = GeneralExecutionAdmission.compile request.plan.snapshot request.plan.permissions)
    (accepted : admittedProfile request = true) (target : Pattern) :
    target ∈ targets request (run request (workBound request)) ↔
      (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected).Step request.root target := by
  obtain ⟨admitted, empty, checked⟩ := admittedProfile_sound compiled accepted
  exact completed_endpoint_coverage admitted empty (run_reachable request _)
    (complete_at_workBound admitted empty checked) target

/-- The complete ordered readout of all original rule jobs has exactly the
successors of the independently defined occurrence GSLT. Empty equation
generators make its equation classes literal here; larger equation profiles
continue to use the original conversion/frontier interface. -/
theorem completedReceipts_targets_iff_step (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (source target : Pattern)
    (empty : plan.equations = [])
    (checked : GeneralPremise.checkStepStratification
      (GeneralPlanEnvironment.environment plan).language = true) :
    target ∈ (GeneralRuleJobExecution.completedReceipts plan bound expected source).map
        GeneralRuleJobs.Receipt.target ↔
      (GeneralOccurrenceSemantics.gslt plan bound expected).Step source target := by
  let request : Request := ⟨plan, bound, expected, source⟩
  constructor
  · intro present
    obtain ⟨receipt, receiptPresent, rfl⟩ := List.mem_map.mp present
    exact ⟨source, receipt, .refl _,
      (GeneralRuleJobExecution.mem_completedReceipts_iff plan bound expected source checked receipt).mp receiptPresent,
      .refl _⟩
  · rintro ⟨representative, receipt, before, valid, after⟩
    have sameSource : source = representative :=
      equation_equivalence_is_equality (request := request) empty before
    have sameTarget : receipt.target = target :=
      equation_equivalence_is_equality (request := request) empty after
    cases sameSource
    exact List.mem_map.mpr ⟨receipt,
      (GeneralRuleJobExecution.mem_completedReceipts_iff plan bound expected source checked receipt).mpr valid,
      sameTarget⟩

/-- An outgoing universal question ranges over every licensed source step
exactly when it holds for the targets of the complete ordered job readout.
This concerns outgoing successors, not the adjoint past box. -/
theorem forall_completedReceipts_iff (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (empty : plan.equations = [])
    (checked : GeneralPremise.checkStepStratification
      (GeneralPlanEnvironment.environment plan).language = true)
    (property : Pattern → Prop) :
    (∀ receipt ∈ GeneralRuleJobExecution.completedReceipts plan bound expected source,
      property receipt.target) ↔
      (∀ target, (GeneralOccurrenceSemantics.gslt plan bound expected).Step source target →
        property target) := by
  constructor
  · intro allReceipts target step
    obtain ⟨receipt, member, rfl⟩ := List.mem_map.mp
      ((completedReceipts_targets_iff_step plan bound expected source target empty checked).mpr step)
    exact allReceipts receipt member
  · intro allSteps receipt member
    exact allSteps receipt.target
      ((completedReceipts_targets_iff_step plan bound expected source receipt.target empty checked).mp
        (List.mem_map.mpr ⟨receipt, member, rfl⟩))

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier.LocalEquationFree
