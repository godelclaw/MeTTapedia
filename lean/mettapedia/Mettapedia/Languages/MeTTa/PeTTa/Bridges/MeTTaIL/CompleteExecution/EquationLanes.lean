import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.EquationLimits
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.StepRounds
import Mettapedia.OSLF.MeTTaIL.GeneralTypedSitesGenerator

/-!
# Equation jobs and their lanes

`gslt:equations:jobs` puts every equation of the plan at every licensed site of a term, as
`GeneralEquationJobs.jobs`; `gslt:equations:lanes` keeps, for each job, every typed match of the
equation's left side at the erased focus, as `Complete.EquationJob.lanes`. A lane deepens over the
equation's premises at its capture; `premisesWire` writes that family.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted (checkOpenPatternWellSorted FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise ScopedRuleMatching RuleBinding DerivedContexts GeneralTypedSites
open StructuralDescent.Scheduled (Goal Result Task Obligation)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open DescentCodec
open RuleInstantiationExecution.GeneralExecution (matcherRequestTerm matcherStateTerm matcherAnswerTerm)

theorem freeFvarNames_erase (pattern : Pattern) :
    pattern.eraseBinderMetadata.freeFvarNames = pattern.freeFvarNames := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [Pattern.eraseBinderMetadata, Pattern.freeFvarNames]
  | hfvar name => simp [Pattern.eraseBinderMetadata, Pattern.freeFvarNames]
  | happly label arguments ih =>
    simp only [Pattern.eraseBinderMetadata, Pattern.freeFvarNames, List.flatMap_map]
    exact List.flatMap_congr ih
  | hlambda binder body ih => simpa [Pattern.eraseBinderMetadata, Pattern.freeFvarNames] using ih
  | hmultiLambda arity binders body ih => simpa [Pattern.eraseBinderMetadata, Pattern.freeFvarNames] using ih
  | hsubst body replacement bodyIH replacementIH =>
    simp [Pattern.eraseBinderMetadata, Pattern.freeFvarNames, bodyIH, replacementIH]
  | hcollection kind elements rest ih =>
    simp only [Pattern.eraseBinderMetadata, Pattern.freeFvarNames, List.flatMap_map]
    rw [List.flatMap_congr ih]

/-- An equation job as MeTTa data: `(EquationJob position rule spec site)`. -/
def equationJobTerm (job : GeneralEquationJobs.Job) : Term :=
  .application "EquationJob" [.natural job.planPosition, InferenceCettaWire.AuthoredRule.rewriteTerm job.equation.rule,
    InferenceCettaWire.AuthoredRule.bindingSpecTerm job.equation.binding.spec,
    ScopedRuleJobReadoutExecution.siteTerm job.site]

/-- A lane as MeTTa data: `(EquationLane job answer)`. -/
def laneTerm (lane : Complete.EquationJob.Lane) : Term :=
  .application "EquationLane" [equationJobTerm lane.job, matcherAnswerTerm lane.answer]

variable (plan : GeneralExecutionAdmission.Plan)

@[metta_head "gslt:equations:cross-sites"]
theorem cross_sites_returns (state : State) (equation : GeneralExecutionAdmission.EquationPlan) (position : Nat) :
    ∀ sites : List SiteData,
      PureReturns runtime [] state
        (apply "gslt:equations:cross-sites" [encoded (CompletePlanWire.equationDeclarationTerm plan (equation, position)),
          encoded (encodeList ScopedRuleJobReadoutExecution.siteTerm sites)])
        state (encoded (encodeList equationJobTerm (sites.map fun site => ⟨position, equation, site⟩)))
  | [] => by
    metta_call complete_checked
    metta_eval unfolding [encodeList]
  | site :: rest => by
    have later := cross_sites_returns state equation position rest
    complete_eval [later] unfolding [encodeList, CompletePlanWire.equationDeclarationTerm, equationJobTerm]

@[metta_head "gslt:equations:jobs"]
theorem equations_jobs_returns (state : State) (sites : List SiteData) (unused : Nat) :
    ∀ pairs : List (GeneralExecutionAdmission.EquationPlan × Nat),
      PureReturns runtime [] state
        (apply "gslt:equations:jobs" [encoded (encodeList (CompletePlanWire.equationDeclarationTerm plan) pairs),
          encoded (encodeList ScopedRuleJobReadoutExecution.siteTerm sites), number unused])
        state (encoded (encodeList equationJobTerm
          (pairs.flatMap fun (equation, position) => sites.map fun site => ⟨position, equation, site⟩)))
  | [] => by
    metta_call complete_checked
    metta_eval unfolding [encodeList]
  | (equation, position) :: rest => by
    have here := cross_sites_returns plan state equation position sites
    have later := equations_jobs_returns state sites unused rest
    have joined := complete_append_returns equationJobTerm state
      (sites.map fun site => (⟨position, equation, site⟩ : GeneralEquationJobs.Job))
      (rest.flatMap fun (equation, position) => sites.map fun site => ⟨position, equation, site⟩)
    complete_eval [here, later, joined] unfolding [encodeList, List.flatMap_cons]

@[metta_head "gslt:equations:context"]
theorem equations_context_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (job : GeneralEquationJobs.Job) :
    PureReturns runtime [] state
      (apply "gslt:equations:context" [planValue plan table bound expected, encoded (equationJobTerm job)])
      state (encoded (PremiseOperationsExecution.GeneralExecution.contextTerm (job.context plan))) := by
  have count := complete_length_returns ScopedRuleJobReadoutExecution.rulePlanTerm state plan.rules
  complete_eval [count]
    unfolding [planValue, CompletePlanWire.planTerm, equationJobTerm, ScopedRuleJobReadoutExecution.siteTerm,
      PremiseOperationsExecution.GeneralExecution.contextTerm, GeneralEquationJobs.Job.context,
      PremiseOperationsExecution.GeneralExecution.Base.typesTerm]

theorem complete_check_assignment_returns (state : State) (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (rule : RewriteRule) (spec : RuleBindingSpec) (assignment : Assignment) :
    PureReturns runtime [] state
      (apply "gslt:premise:check-assignment"
        [encoded (encodeList InferenceCettaWire.AuthoredRule.typingDeclarationTerm language.terms),
         encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm free),
         encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm bound),
         encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule),
         encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), assignmentValue assignment])
      state (Effects.boolean (ConditionalEquationExecution.checkAssignment language
        (FreeTypeContext.ofList free) bound rule spec assignment)) := by
  metta_lift complete_checked ["declarations", "free", "bound", "rule", "spec", "assignment"]
    (descent_check_assignment_returns state language free bound rule spec assignment)

@[metta_head "gslt:equations:typed-lanes"]
theorem typed_lanes_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (job : GeneralEquationJobs.Job) (unused : Nat) :
    ∀ answers : List GeneralScopedMatchMachine.Answer,
      (∀ answer ∈ answers, assignmentFreeWithin footprint answer.assignment) →
      PureReturns runtime [] state
        (apply "gslt:equations:typed-lanes" [planValue plan table bound expected, encoded (equationJobTerm job),
          encoded (encodeList matcherAnswerTerm answers), number unused])
        state (encoded (encodeList laneTerm
          ((answers.filter fun answer => checkTypedAssignment (GeneralPlanEnvironment.environment plan) (job.context plan)
              answer.assignment).map fun answer => ⟨job, answer⟩)))
  | [], _ => by
    metta_call complete_checked
    metta_eval unfolding [encodeList]
  | answer :: rest, covered => by
    subst tabled
    have later := typed_lanes_returns state (plan.snapshot.free.entriesOn footprint) bound expected footprint rfl job
      unused rest (fun other member => covered other (by simp [member]))
    have check := complete_check_assignment_returns state (GeneralPlanEnvironment.environment plan).language
      (plan.snapshot.free.entriesOn footprint) job.site.focusBound job.equation.rule job.equation.binding.spec
      answer.assignment
    have snapshot := ConditionalEquationExecution.checkAssignment_snapshot
      (GeneralPlanEnvironment.environment plan).language plan.snapshot.free job.site.focusBound job.equation.rule
      job.equation.binding.spec answer.assignment footprint
      (ConditionalEquationExecution.assignment_free_names_covered footprint _ (covered answer (by simp)))
    by_cases typed : checkTypedAssignment (GeneralPlanEnvironment.environment plan) (job.context plan)
        answer.assignment = true
    · have answered : ConditionalEquationExecution.checkAssignment (GeneralPlanEnvironment.environment plan).language
          (FreeTypeContext.ofList (plan.snapshot.free.entriesOn footprint)) job.site.focusBound job.equation.rule
          job.equation.binding.spec answer.assignment = true := by
        rw [snapshot]; exact typed
      simp only [List.filter_cons, typed, ↓reduceIte]
      complete_eval [later, check]
        unfolding [encodeList, planValue, CompletePlanWire.planTerm, PremiseOperationsExecution.GeneralExecution.environmentTerm,
          equationJobTerm, ScopedRuleJobReadoutExecution.siteTerm, matcher_answer_term', laneTerm, answered,
          PremiseOperationsExecution.GeneralExecution.Base.typesTerm, List.map_cons]
    · have answered : ConditionalEquationExecution.checkAssignment (GeneralPlanEnvironment.environment plan).language
          (FreeTypeContext.ofList (plan.snapshot.free.entriesOn footprint)) job.site.focusBound job.equation.rule
          job.equation.binding.spec answer.assignment = false := by
        rw [snapshot]; exact Bool.eq_false_iff.mpr typed
      simp only [List.filter_cons, typed, Bool.false_eq_true, ↓reduceIte]
      complete_eval [later, check]
        unfolding [encodeList, planValue, CompletePlanWire.planTerm, PremiseOperationsExecution.GeneralExecution.environmentTerm,
          equationJobTerm, ScopedRuleJobReadoutExecution.siteTerm, matcher_answer_term', laneTerm, answered,
          PremiseOperationsExecution.GeneralExecution.Base.typesTerm]

/-- The typed matches of a job's left side at its erased focus, as lanes. -/
def jobLanes (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) (job : GeneralEquationJobs.Job) :
    List Complete.EquationJob.Lane :=
  ((Complete.EquationJob.leftMatches plan bound expected source job).filter fun answer =>
      checkTypedAssignment (GeneralPlanEnvironment.environment plan) (job.context plan) answer.assignment).map
    fun answer => ⟨job, answer⟩

theorem left_matches_within (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (job : GeneralEquationJobs.Job) (footprint : List String)
    (focused : ∀ name ∈ job.site.focus.freeFvarNames, name ∈ footprint) :
    ∀ answer ∈ Complete.EquationJob.leftMatches plan bound expected source job,
      assignmentFreeWithin footprint answer.assignment := by
  intro answer member
  exact GeneralScopedMatchMachine.matcher_answer_free_within _ _
    (GeneralEquationJobExecution.finishMatcher_reachable .start) answer member footprint
    (by intro entry inside; cases inside)
    (by intro name inside; exact focused name (by simpa [GeneralEquationJobExecution.Request.matcher,
      freeFvarNames_erase] using inside))

@[metta_head "gslt:equations:job-lanes"]
theorem job_lanes_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (source : Pattern) (job : GeneralEquationJobs.Job)
    (focused : ∀ name ∈ job.site.focus.freeFvarNames, name ∈ footprint) :
    PureReturns runtime [] state
      (apply "gslt:equations:job-lanes" [planValue plan table bound expected, encoded (equationJobTerm job)])
      state (encoded (encodeList laneTerm (jobLanes plan bound expected source job))) := by
  have ambient := complete_length_returns InferenceCettaWire.AuthoredRule.typeTerm state job.site.focusBound
  have erased := erase_returns state job.site.focus
  have answers := matcher_answers_returns state
    ⟨job.equation.rule, job.equation.binding.spec, job.site.focusBound.length, .left, [], 0, [], job.equation.rule.left,
      job.site.focus.eraseBinderMetadata⟩
  have lanes := typed_lanes_returns plan state table bound expected footprint tabled job 0
    (Complete.EquationJob.leftMatches plan bound expected source job)
    (left_matches_within plan bound expected source job footprint focused)
  complete_eval [ambient, erased, answers, lanes]
    unfolding [equationJobTerm, ScopedRuleJobReadoutExecution.siteTerm, InferenceCettaWire.AuthoredRule.rewriteTerm,
      root_request_term, requestValue, jobLanes, Complete.EquationJob.leftMatches, Complete.EquationJob.matcher,
      GeneralEquationJobExecution.Request.matcher, finishedAnswers, patternValue]

@[metta_head "gslt:equations:jobs-lanes"]
theorem jobs_lanes_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (source : Pattern) :
    ∀ jobs : List GeneralEquationJobs.Job, (∀ job ∈ jobs, ∀ name ∈ job.site.focus.freeFvarNames, name ∈ footprint) →
      PureReturns runtime [] state
        (apply "gslt:equations:jobs-lanes" [planValue plan table bound expected, encoded (encodeList equationJobTerm jobs)])
        state (encoded (encodeList laneTerm (jobs.flatMap (jobLanes plan bound expected source))))
  | [], _ => by
    metta_call complete_checked
    metta_eval unfolding [encodeList]
  | job :: rest, focused => by
    have here := job_lanes_returns plan state table bound expected footprint tabled source job (focused job (by simp))
    have later := jobs_lanes_returns state table bound expected footprint tabled source rest
      (fun other member => focused other (by simp [member]))
    have joined := complete_append_returns laneTerm state (jobLanes plan bound expected source job)
      (rest.flatMap (jobLanes plan bound expected source))
    complete_eval [here, later, joined] unfolding [encodeList, List.flatMap_cons]

theorem typed_generate_agreement : ProgramAgreementOn GeneralTypedSiteExecution.executionHeads
    GeneralTypedSiteExecution.program typedLibrary.runtime := typed_agreement

/-- `gslt:sites:generate` lists a term's licensed sites, in the complete machine's runtime. -/
theorem complete_generate_returns (state : State) (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (footprint : List String) (covers : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    PureReturns runtime [] state
      (apply "gslt:sites:generate"
        [encoded (PremiseOperationsExecution.DeclarationTyping.declarationsTerm
            (GeneralPlanEnvironment.environment plan).language.terms),
         encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm (plan.snapshot.free.entriesOn footprint)),
         encoded (InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites),
         encoded (PremiseOperationsExecution.DeclarationTyping.boundContextTerm bound),
         encoded (InferenceCettaWire.AuthoredRule.typeTerm expected), encoded (InferenceCettaWire.encodePattern source)])
      state (encoded (encodeList ScopedRuleJobReadoutExecution.siteTerm
        (generate (GeneralPlanEnvironment.environment plan).language plan.snapshot.free plan.permissions.sites bound
          expected source))) := by
  rw [← generate_snapshot _ _ _ _ _ _ footprint covers]
  metta_lift complete_checked ["declarations", "free", "permissions", "bound", "expected", "source"]
    (by metta_lift descent_checked ["declarations", "free", "permissions", "bound", "expected", "source"]
      (transport_call GeneralTypedSiteExecution.program_closed typed_agreement (by decide +kernel) (by decide)
        (by decide +kernel) (by decide) ["declarations", "free", "permissions", "bound", "expected", "source"]
        (by decide) rfl (by decide +kernel)
        (GeneralTypedSiteExecution.generate_returns state (GeneralPlanEnvironment.environment plan).language
          (plan.snapshot.free.entriesOn footprint) plan.permissions.sites bound expected source)))

theorem complete_sorted_returns (state : State) (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (type : TypeExpr) (pattern : Pattern) :
    PureReturns runtime [] state
      (apply "gslt:premise:open-well-sorted"
        [encoded (encodeList InferenceCettaWire.AuthoredRule.typingDeclarationTerm language.terms),
         encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm free),
         encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm bound),
         encoded (InferenceCettaWire.AuthoredRule.typeTerm type), encoded (InferenceCettaWire.encodePattern pattern)])
      state (Effects.boolean (checkOpenPatternWellSorted language (FreeTypeContext.ofList free) bound type pattern)) := by
  metta_lift complete_checked ["declarations", "free", "bound", "type", "pattern"]
    (Lowered.sorted state language free bound type pattern)

theorem job_focus_within {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {footprint : List String}
    (covers : ∀ name ∈ source.freeFvarNames, name ∈ footprint) {job : GeneralEquationJobs.Job}
    (member : job ∈ GeneralEquationJobs.jobs plan bound expected source) :
    ∀ name ∈ job.site.focus.freeFvarNames, name ∈ footprint := by
  intro name inside
  apply covers
  rw [← Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed.source_eq
    ((GeneralEquationJobs.jobs_iff plan bound expected source job).mp member).2]
  exact (Mettapedia.OSLF.Framework.DisplayedContextProfile.mem_freeFvarNames_fill_iff _ _ _).mpr (.inr inside)

@[metta_head "gslt:equations:lanes"]
theorem lanes_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (source : Pattern) (covers : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    PureReturns runtime [] state
      (apply "gslt:equations:lanes" [planValue plan table bound expected, patternValue source])
      state (encoded (encodeList laneTerm (Complete.EquationJob.lanes plan bound expected source))) := by
  have sorted := complete_sorted_returns state (GeneralPlanEnvironment.environment plan).language table bound expected
    source
  have snapshot := Mettapedia.GSLT.LanguageDef.WellSorted.check_open_pattern_snapshot
    (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected source footprint covers
  subst tabled
  rw [snapshot] at sorted
  by_cases typed : checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
      bound expected source = true
  · have sites := complete_generate_returns plan state bound expected source footprint covers
    have jobs := equations_jobs_returns plan state
      (generate (GeneralPlanEnvironment.environment plan).language plan.snapshot.free plan.permissions.sites bound
        expected source) 0 plan.equations.zipIdx
    have lanes := jobs_lanes_returns plan state (plan.snapshot.free.entriesOn footprint) bound expected footprint rfl
      source (GeneralEquationJobs.jobs plan bound expected source)
      (fun job member => job_focus_within plan covers member)
    rw [show Complete.EquationJob.lanes plan bound expected source =
        (GeneralEquationJobs.jobs plan bound expected source).flatMap (jobLanes plan bound expected source) by
      rw [Complete.EquationJob.lanes, if_pos typed]; rfl]
    complete_eval [sorted, sites, jobs, lanes]
      unfolding [planValue, CompletePlanWire.planTerm, PremiseOperationsExecution.GeneralExecution.environmentTerm,
        PremiseOperationsExecution.DeclarationTyping.declarationsTerm,
        PremiseOperationsExecution.DeclarationTyping.boundContextTerm, typed, GeneralEquationJobs.jobs, patternValue]
  · have untyped : checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
        bound expected source = false := Bool.eq_false_iff.mpr typed
    rw [show Complete.EquationJob.lanes plan bound expected source = [] by simp [Complete.EquationJob.lanes, untyped]]
    complete_eval [sorted]
      unfolding [planValue, CompletePlanWire.planTerm, PremiseOperationsExecution.GeneralExecution.environmentTerm,
        untyped, encodeList, patternValue]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
