import Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingLaws
import Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobCoverage

open Mettapedia.OSLF.Framework

/-!
# Independent exclusion of a wrong specified beta contractum

The local coverage calculation drains every actual typed occurrence job,
using the independent premise semantics and its earned coverage theorem.
With no equation declarations, its target list characterizes every semantic
step. This rules out the wrong RHS without treating an incomplete frontier
as an absence certificate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingIsolation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralExecutionAdmission GeneralOccurrenceSemantics

def primitiveTargets (plan : Plan) (bound : List TypeExpr) (carrier : TypeExpr)
    (source : Pattern) : List Pattern :=
  (GeneralRuleJobs.jobs plan bound carrier source).attach.flatMap fun job =>
    let request : GeneralRuleJobExecution.Request := ⟨plan, bound, carrier, source, job.val⟩
    (GeneralRuleJobExecution.finishState request
      ((GeneralRuleJobs.jobs_spec plan bound carrier source job.val).mp job.property)).answers.map
        fun answer => answer.val.target

def primitiveTargetsAt (plan : Plan) (bound : List TypeExpr) (carrier : TypeExpr)
    (source : Pattern) (fuel : Nat) : List Pattern :=
  (GeneralRuleJobs.jobs plan bound carrier source).attach.flatMap fun job =>
    let request : GeneralRuleJobExecution.Request := ⟨plan, bound, carrier, source, job.val⟩
    let licensed := (GeneralRuleJobs.jobs_spec plan bound carrier source job.val).mp job.property
    (GeneralRuleJobExecution.run request fuel (GeneralRuleJobExecution.start request licensed)).answers.map
      fun answer => answer.val.target

def primitiveJobsComplete (plan : Plan) (bound : List TypeExpr) (carrier : TypeExpr)
    (source : Pattern) (fuel : Nat) : Bool :=
  (GeneralRuleJobs.jobs plan bound carrier source).attach.all fun job =>
    let request : GeneralRuleJobExecution.Request := ⟨plan, bound, carrier, source, job.val⟩
    let licensed := (GeneralRuleJobs.jobs_spec plan bound carrier source job.val).mp job.property
    GeneralRuleJobExecution.complete
      (GeneralRuleJobExecution.run request fuel (GeneralRuleJobExecution.start request licensed))

theorem complete_primitive_targets_exact (plan : Plan) (bound : List TypeExpr) (carrier : TypeExpr)
    (source : Pattern) (fuel : Nat) (checked : primitiveJobsComplete plan bound carrier source fuel = true) :
    primitiveTargetsAt plan bound carrier source fuel = primitiveTargets plan bound carrier source := by
  unfold primitiveTargetsAt primitiveTargets
  apply List.flatMap_congr
  intro job member
  let request : GeneralRuleJobExecution.Request := ⟨plan, bound, carrier, source, job.val⟩
  let licensed := (GeneralRuleJobs.jobs_spec plan bound carrier source job.val).mp job.property
  have completed := List.all_eq_true.mp checked job member
  have same := GeneralRuleJobExecution.completed_reachable_finishState
    (GeneralRuleJobExecution.reachable_run (GeneralRuleJobExecution.Reachable.start (licensed := licensed)) fuel)
    completed
  exact congrArg (fun state => state.answers.map fun answer => answer.val.target) same

theorem primitive_target_covered {plan : Plan} {bound : List TypeExpr} {carrier : TypeExpr}
    {source : Pattern} (ordered : GeneralPremise.checkStepStratification
      (GeneralPlanEnvironment.environment plan).language = true)
    (receipt : GeneralRuleJobs.Receipt) (valid : receipt.Valid plan bound carrier source) :
    receipt.target ∈ primitiveTargets plan bound carrier source := by
  let job : {job // job ∈ GeneralRuleJobs.jobs plan bound carrier source} :=
    ⟨receipt.job, (GeneralRuleJobs.jobs_spec plan bound carrier source receipt.job).mpr valid.1⟩
  let request : GeneralRuleJobExecution.Request := ⟨plan, bound, carrier, source, job.val⟩
  have licensed := (GeneralRuleJobs.jobs_spec plan bound carrier source job.val).mp job.property
  obtain ⟨answer, member, same⟩ :=
    GeneralRuleJobExecution.finishState_receipt_complete (request := request) licensed ordered valid rfl
  exact List.mem_flatMap.mpr ⟨job, List.mem_attach _ _,
    List.mem_map.mpr ⟨answer, member, congrArg GeneralRuleJobs.Receipt.target same⟩⟩

theorem no_equation_edges {plan : Plan} (empty : plan.equations = [])
    (bound : List TypeExpr) (carrier : TypeExpr) (first second : Pattern) :
    ¬ Equation plan bound carrier first second := by
  rintro ⟨receipt, completed, _⟩
  have origin := completed.job.1
  rw [empty] at origin
  exact List.not_mem_nil origin

theorem no_equation_comparison {plan : Plan} (empty : plan.equations = [])
    (bound : List TypeExpr) (carrier : TypeExpr) {first second : Pattern}
    (related : Relation.EqvGen (Equation plan bound carrier) first second) : first = second := by
  induction related with
  | rel first second edge => exact False.elim (no_equation_edges empty bound carrier first second edge)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem no_equation_step_target {plan : Plan} (empty : plan.equations = [])
    (bound : List TypeExpr) (carrier : TypeExpr)
    (ordered : GeneralPremise.checkStepStratification
      (GeneralPlanEnvironment.environment plan).language = true)
    (source target : Pattern) (step : (gslt plan bound carrier).Step source target) :
    target ∈ primitiveTargets plan bound carrier source := by
  obtain ⟨representative, receipt, before, valid, after⟩ := step
  have sourceSame := no_equation_comparison empty bound carrier before
  have targetSame := no_equation_comparison empty bound carrier after
  subst representative
  rw [← targetSame]
  exact primitive_target_covered ordered receipt valid

open Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer (generated source target argument term)

theorem actual_equations_absent : generated.plan.equations = [] := by
  rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.runtime_plan_actual]
  rfl

theorem actual_ordered : GeneralPremise.checkStepStratification
    (GeneralPlanEnvironment.environment generated.plan).language = true := by
  rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.runtime_plan_actual]
  cbv

theorem actual_native_targets : primitiveTargets generated.plan [] term source = [target] := by
  have actual := congrArg (fun plan => primitiveTargets plan [] term source)
    Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.runtime_plan_actual
  rw [actual]
  have complete : primitiveJobsComplete Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.runtimePlan [] term source 40 = true := by
    decide +kernel
  rw [← complete_primitive_targets_exact Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.runtimePlan [] term source 40 complete]
  decide +kernel

theorem every_actual_beta_target {endpoint : Pattern}
    (step : (gslt generated.plan [] term).Step source endpoint) : endpoint = target := by
  have member := no_equation_step_target actual_equations_absent [] term actual_ordered source endpoint step
  rw [actual_native_targets] at member
  exact List.mem_singleton.mp member

theorem wrong_beta_rhs_independently_excluded : ¬ (gslt generated.plan [] term).Step source argument := by
  intro step
  have same := every_actual_beta_target step
  have distinct : argument ≠ target := by decide +kernel
  exact distinct same

end Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingIsolation
