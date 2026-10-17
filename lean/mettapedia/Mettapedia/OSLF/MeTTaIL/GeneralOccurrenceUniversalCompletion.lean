import Mettapedia.OSLF.MeTTaIL.GeneralExecutionTotalAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseStaticResolution
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceLocalSourceTyping
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceResolvedLifting
import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobResolution
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobResolution
import Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderJobTotality
import Mettapedia.OSLF.MeTTaIL.GeneralRhoTotality
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceModalReadouts

/-!
# Exhaustive occurrence execution from checked static admission

Actual compiled premise, provider, projection and child-stratum checks earn
the local resolution laws. Saturation then supplies the finite comparison
certificate for every admitted source size and binder depth. No completion
law, finite carrier or work ranking is an input of the admission algorithm.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem generic_equation_resolution {request : Request}
    (checked : GeneralExecutionTotalAdmission.checkGeneric request.plan = true) :
    EquationResolution request := by
  intro source job sourceTyped licensed
  apply GeneralEquationJobExecution.finishJob_resolved
    (equationRequest request source job) licensed sourceTyped
  intro trace captured matched typed
  have equationMember := List.fst_mem_of_mem_zipIdx licensed.1
  have equationChecked := GeneralExecutionTotalAdmission.checkGeneric_equation checked equationMember
  exact GeneralPremise.Static.premises_resolved
    (GeneralExecutionTotalAdmission.checkGeneric_readout checked).1
    (GeneralPremise.Static.DynamicAvailability.of_empty
      (GeneralExecutionTotalAdmission.checkGeneric_no_dynamic checked)) equationChecked
    (by
      change request.plan.rules.length ≤ (GeneralPlanEnvironment.environment request.plan).language.rewrites.length
      simp only [GeneralPlanEnvironment.environment, List.length_map]
      exact Nat.le_refl _)
    rfl rfl job.site.focus.eraseBinderMetadata_hasCanonicalBinderMetadata matched typed

theorem generic_rule_resolution {request : Request} (admitted : Admitted request)
    (checked : GeneralExecutionTotalAdmission.checkGeneric request.plan = true) :
    RuleResolution request := by
  intro representative job licensed
  apply GeneralRuleJobExecution.finishState_resolved
    (ruleRequest request representative job) licensed
  change (GeneralPremise.Execution.finish (GeneralPlanEnvironment.environment request.plan)
    (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).unresolved = []
  exact GeneralPremise.Static.root_resolved
    (GeneralExecutionTotalAdmission.checkGeneric_readout checked).1
    (GeneralPremise.Static.DynamicAvailability.of_empty
      (GeneralExecutionTotalAdmission.checkGeneric_no_dynamic checked))
    (GeneralRuleJobs.Job.selected_rule licensed)
    (admitted.rule_job_focus_open representative job licensed)

theorem finish_complete_of_generic_admission {request : Request} (admitted : Admitted request)
    (checked : GeneralExecutionTotalAdmission.checkGeneric request.plan = true) :
    complete request (finish request admitted) = true :=
  finish_complete_of_local_resolution admitted (generic_equation_resolution checked)
    (generic_rule_resolution admitted checked)

theorem finish_certificate_of_generic_admission {request : Request} (admitted : Admitted request)
    (checked : GeneralExecutionTotalAdmission.checkGeneric request.plan = true) :
    checkCertificate request (finish request admitted) = true :=
  finish_certificate_of_local_resolution admitted (generic_equation_resolution checked)
    (generic_rule_resolution admitted checked)

theorem guarded_plan_readout {request : Request} (admitted : Admitted request)
    (checked : GeneralGuardedBinderFamily.check request.plan.snapshot request.plan.permissions = true) :
    ∃ allowed, request.plan = GeneralGuardedBinderExecution.plan allowed := by
  obtain ⟨allowed, snapshot, permissions⟩ :=
    (GeneralGuardedBinderFamily.check_iff _ _).mp checked
  refine ⟨allowed, ?_⟩
  rw [admitted.compiled, snapshot, permissions]
  rfl

theorem guarded_equation_resolution {request : Request} (admitted : Admitted request)
    (checked : GeneralGuardedBinderFamily.check request.plan.snapshot request.plan.permissions = true) :
    EquationResolution request := by
  cases request with
  | mk plan bound expected raw =>
      obtain ⟨allowed, planSame⟩ := guarded_plan_readout admitted checked
      change plan = GeneralGuardedBinderExecution.plan allowed at planSame
      subst plan
      intro source job sourceTyped licensed
      have typed : OpenPatternWellSorted EquationFrontierBinderProfile.language FreeTypeContext.empty
          bound expected source := by
        change OpenPatternWellSorted EquationFrontierBinderProfile.language
          (GeneralGuardedBinderAdmission.snapshot allowed).free bound expected source at sourceTyped
        rw [GeneralGuardedBinderAdmission.free_context] at sourceTyped
        exact sourceTyped
      exact GeneralGuardedBinderExecution.equation_job_resolved typed licensed

theorem guarded_rule_resolution {request : Request} (admitted : Admitted request)
    (checked : GeneralGuardedBinderFamily.check request.plan.snapshot request.plan.permissions = true) :
    RuleResolution request := by
  cases request with
  | mk plan bound expected raw =>
      obtain ⟨allowed, planSame⟩ := guarded_plan_readout admitted checked
      change plan = GeneralGuardedBinderExecution.plan allowed at planSame
      subst plan
      intro representative job licensed
      have sourceTyped := admitted.representative_source_typed representative
      have typed : OpenPatternWellSorted EquationFrontierBinderProfile.language FreeTypeContext.empty
          bound expected representative.pattern := by
        change OpenPatternWellSorted EquationFrontierBinderProfile.language
          (GeneralGuardedBinderAdmission.snapshot allowed).free bound expected representative.pattern at sourceTyped
        rw [GeneralGuardedBinderAdmission.free_context] at sourceTyped
        exact sourceTyped
      exact GeneralGuardedBinderExecution.rule_job_resolved typed licensed

theorem finish_complete_of_guarded_admission {request : Request} (admitted : Admitted request)
    (checked : GeneralGuardedBinderFamily.check request.plan.snapshot request.plan.permissions = true) :
    complete request (finish request admitted) = true :=
  finish_complete_of_local_resolution admitted (guarded_equation_resolution admitted checked)
    (guarded_rule_resolution admitted checked)

theorem finish_certificate_of_guarded_admission {request : Request} (admitted : Admitted request)
    (checked : GeneralGuardedBinderFamily.check request.plan.snapshot request.plan.permissions = true) :
    checkCertificate request (finish request admitted) = true :=
  finish_certificate_of_local_resolution admitted (guarded_equation_resolution admitted checked)
    (guarded_rule_resolution admitted checked)

theorem rho_plan_readout {request : Request} (admitted : Admitted request)
    (checked : GeneralRhoFamily.check request.plan.snapshot request.plan.permissions = true) :
    request.plan = GeneralRho.plan := by
  obtain ⟨snapshot, permissions⟩ := (GeneralRhoFamily.check_iff _ _).mp checked
  rw [admitted.compiled, snapshot, permissions]
  rfl

theorem rho_equation_resolution {request : Request} (admitted : Admitted request)
    (checked : GeneralRhoFamily.check request.plan.snapshot request.plan.permissions = true) :
    EquationResolution request := by
  cases request with
  | mk plan bound expected raw =>
      have planSame := rho_plan_readout admitted checked
      change plan = GeneralRho.plan at planSame
      subst plan
      intro source job sourceTyped licensed
      have occurrence := licensed.1
      change (job.equation, job.planPosition) ∈ GeneralRho.plan.equations.zipIdx at occurrence
      rw [GeneralRho.compilation_has_no_equations] at occurrence
      exact False.elim (List.not_mem_nil occurrence)

theorem rho_rule_resolution {request : Request} (admitted : Admitted request)
    (checked : GeneralRhoFamily.check request.plan.snapshot request.plan.permissions = true) :
    RuleResolution request := by
  cases request with
  | mk plan bound expected raw =>
      have planSame := rho_plan_readout admitted checked
      change plan = GeneralRho.plan at planSame
      subst plan
      intro representative job licensed
      have sourceTyped := admitted.representative_source_typed representative
      change OpenPatternWellSorted GeneralRho.language GeneralRho.snapshot.free
        bound expected representative.pattern at sourceTyped
      exact GeneralRho.rule_job_resolved sourceTyped licensed

theorem finish_complete_of_total_admission {request : Request} (admitted : Admitted request)
    (checked : GeneralExecutionTotalAdmission.checkTotality request.plan = true) :
    complete request (finish request admitted) = true := by
  rcases GeneralExecutionTotalAdmission.checkTotality_readout checked with generic | guarded | rho
  · exact finish_complete_of_generic_admission admitted generic
  · exact finish_complete_of_guarded_admission admitted guarded
  · exact finish_complete_of_local_resolution admitted (rho_equation_resolution admitted rho)
      (rho_rule_resolution admitted rho)

theorem finish_certificate_of_total_admission {request : Request} (admitted : Admitted request)
    (checked : GeneralExecutionTotalAdmission.checkTotality request.plan = true) :
    checkCertificate request (finish request admitted) = true := by
  rcases GeneralExecutionTotalAdmission.checkTotality_readout checked with generic | guarded | rho
  · exact finish_certificate_of_generic_admission admitted generic
  · exact finish_certificate_of_guarded_admission admitted guarded
  · exact finish_certificate_of_local_resolution admitted (rho_equation_resolution admitted rho)
      (rho_rule_resolution admitted rho)

theorem compiled_source_admitted {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (checked : (GeneralExecutionTotalAdmission.compile snapshot permissions).complete = true)
    (typed : HasType snapshot.language snapshot.free bound source expected)
    (object : isObjectPattern source = true) :
    Admitted (Request.fromSnapshot snapshot permissions bound expected source) :=
  fromSnapshot_admitted (GeneralExecutionTotalAdmission.compile_foundation_checked checked)
    typed object typed.isWellScopedAt

theorem compiled_total_finish_complete {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (checked : (GeneralExecutionTotalAdmission.compile snapshot permissions).complete = true)
    (typed : HasType snapshot.language snapshot.free bound source expected)
    (object : isObjectPattern source = true) :
    complete (Request.fromSnapshot snapshot permissions bound expected source)
      (finish _ (compiled_source_admitted checked typed object)) = true :=
  finish_complete_of_total_admission (compiled_source_admitted checked typed object)
    (GeneralExecutionTotalAdmission.compile_totality_checked checked)

theorem compiled_total_finish_certificate {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (checked : (GeneralExecutionTotalAdmission.compile snapshot permissions).complete = true)
    (typed : HasType snapshot.language snapshot.free bound source expected)
    (object : isObjectPattern source = true) :
    checkCertificate (Request.fromSnapshot snapshot permissions bound expected source)
      (finish _ (compiled_source_admitted checked typed object)) = true :=
  finish_certificate_of_total_admission (compiled_source_admitted checked typed object)
    (GeneralExecutionTotalAdmission.compile_totality_checked checked)

/-- Exhaustive execution admits its proof internally from the actual source
and compiled-profile checks. Ordinary bounded `run` retains pending work for
sources and profiles for which this exhaustive entry point returns `none`. -/
def executeCertified? (snapshot : GeneralExecutionAdmission.Snapshot)
    (permissions : GeneralExecutionAdmission.Permissions) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) :
    Option (State (Request.fromSnapshot snapshot permissions bound expected source)) :=
  let request := Request.fromSnapshot snapshot permissions bound expected source
  if accepted : (GeneralExecutionTotalAdmission.compile snapshot permissions).complete then
    if sourceChecked : checkOpenPatternWellSorted snapshot.language snapshot.free
        bound expected request.root then
      let admitted : Admitted request :=
        ⟨rfl, GeneralExecutionTotalAdmission.compile_foundation_checked accepted,
          checkOpenPatternWellSorted_sound sourceChecked⟩
      some (finish request admitted)
    else none
  else none

theorem executeCertified?_exists {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (checked : (GeneralExecutionTotalAdmission.compile snapshot permissions).complete = true)
    (typed : HasType snapshot.language snapshot.free bound source expected)
    (object : isObjectPattern source = true) :
    ∃ state, executeCertified? snapshot permissions bound expected source = some state := by
  have sourceChecked := checkOpenPatternWellSorted_complete
    (GeneralEquationCanonical.open_typed_erase typed object typed.isWellScopedAt)
  change checkOpenPatternWellSorted snapshot.language snapshot.free bound expected
    (Request.fromSnapshot snapshot permissions bound expected source).root = true at sourceChecked
  unfold executeCertified?
  rw [dif_pos checked, dif_pos sourceChecked]
  exact ⟨_, rfl⟩

theorem executeCertified?_complete {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    {state : State (Request.fromSnapshot snapshot permissions bound expected source)}
    (executed : executeCertified? snapshot permissions bound expected source = some state) :
    complete (Request.fromSnapshot snapshot permissions bound expected source) state = true ∧
      checkCertificate (Request.fromSnapshot snapshot permissions bound expected source) state = true := by
  unfold executeCertified? at executed
  dsimp only at executed
  split at executed
  · rename_i checked
    split at executed
    · rename_i sourceChecked
      cases Option.some.inj executed
      exact ⟨finish_complete_of_total_admission _
          (GeneralExecutionTotalAdmission.compile_totality_checked checked),
        finish_certificate_of_total_admission _
          (GeneralExecutionTotalAdmission.compile_totality_checked checked)⟩
    · cases executed
  · cases executed

#print axioms generic_equation_resolution
#print axioms finish_complete_of_generic_admission
#print axioms finish_certificate_of_generic_admission
#print axioms finish_certificate_of_guarded_admission
#print axioms compiled_total_finish_complete
#print axioms compiled_total_finish_certificate
#print axioms executeCertified?_complete

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
