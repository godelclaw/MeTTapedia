import Mettapedia.OSLF.MeTTaIL.StructuralDescentCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment

/-!
# Generic structural-recursion admission for compiled authored plans

The original declaration compiler retains all typing, provider, binding,
canonical-syntax and equation obligations. Only its declaration-order child
stratification obligation may be discharged by the independent checked
structural-descent comparison. Recursive rule execution itself uses the new
all-declaration finite-depth interpreter, rather than the older stratified
premise machine.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.Plan

open Syntax GeneralExecutionAdmission

def structuralReady (plan : GeneralExecutionAdmission.Plan) : Bool :=
  checkEnvironment (GeneralPlanEnvironment.environment plan)

def refine (plan : GeneralExecutionAdmission.Plan) : GeneralExecutionAdmission.Plan :=
  if structuralReady plan then
    {plan with obligations := plan.obligations.filter (· != .childStratification)}
  else plan

def compile (snapshot : Snapshot) (permissions : Permissions) : GeneralExecutionAdmission.Plan :=
  refine (GeneralExecutionAdmission.compile snapshot permissions)

theorem rules_preserved (plan : GeneralExecutionAdmission.Plan) :
    (refine plan).rules = plan.rules := by
  unfold refine
  split <;> rfl

theorem snapshot_preserved (plan : GeneralExecutionAdmission.Plan) :
    (refine plan).snapshot = plan.snapshot := by
  unfold refine
  split <;> rfl

theorem permissions_preserved (plan : GeneralExecutionAdmission.Plan) :
    (refine plan).permissions = plan.permissions := by
  unfold refine
  split <;> rfl

theorem equations_preserved (plan : GeneralExecutionAdmission.Plan) :
    (refine plan).equations = plan.equations := by
  unfold refine
  split <;> rfl

theorem other_obligations_preserved (plan : GeneralExecutionAdmission.Plan)
    (obligation : Obligation) (other : obligation ≠ .childStratification) :
    obligation ∈ (refine plan).obligations ↔ obligation ∈ plan.obligations := by
  unfold refine
  split
  · simp only [List.mem_filter, bne_iff_ne]
    exact ⟨fun retained => retained.1, fun present => ⟨present, other⟩⟩
  · rfl

theorem child_obligation_discharged (plan : GeneralExecutionAdmission.Plan)
    (ready : structuralReady plan = true) :
    .childStratification ∉ (refine plan).obligations := by
  simp only [refine, ready, if_true, List.mem_filter, bne_self_eq_false, Bool.false_eq_true,
    and_false, not_false_eq_true]

theorem refinement_environment (plan : GeneralExecutionAdmission.Plan) :
    GeneralPlanEnvironment.environment (refine plan) = GeneralPlanEnvironment.environment plan := by
  unfold refine
  split <;> rfl

/-- Every original typed authored occurrence is covered by the refined plan's
generic recursive reference executor. This theorem changes no other admission
condition and constructs the source-node depth rather than accepting it. -/
theorem compiled_occurrence_coverage (snapshot : Snapshot) (permissions : Permissions)
    (ready : structuralReady (GeneralExecutionAdmission.compile snapshot permissions) = true)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (answer : Execution.RootAnswer
      (GeneralPlanEnvironment.environment (compile snapshot permissions)) bound type source) :
    answer ∈ Execution.exhaustive
      (GeneralPlanEnvironment.environment (compile snapshot permissions)) bound type source := by
  apply Execution.exhaustive_complete
  simpa only [compile, refinement_environment, structuralReady] using ready

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Plan
