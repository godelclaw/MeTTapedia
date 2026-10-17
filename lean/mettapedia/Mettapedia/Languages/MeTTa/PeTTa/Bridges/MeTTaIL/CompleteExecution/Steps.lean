import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.RootFamily
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralTypedSiteExecution.Traversal
import Mettapedia.OSLF.MeTTaIL.Complete.DeepFootprint

/-!
# Every rule job of a term, in fair rounds

`gslt:step:*` runs `Complete.Step`: the rule jobs of a term, each with its deepening search, one
unit of work per job per round, the receipts of newly published firings appended to the log.
The plan's free-type table is the environment's snapshot on a footprint that covers the term.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise GeneralRuleJobs
open StructuralDescent.Scheduled (Goal Result Task Obligation)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open DescentCodec

theorem typed_agreement : ProgramAgreementOn GeneralTypedSiteExecution.executionHeads GeneralTypedSiteExecution.program
    typedLibrary.runtime :=
  agreement_trans GeneralTypedSiteExecution.scoped_program_agreement
    (programAgreementOn_of_retained_rows _ _ _ rfl rfl)

/-- `gslt:sites:jobs` lists the plan's rule jobs at a term, in the complete machine's runtime. -/
theorem complete_jobs_returns (state : State) (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (footprint : List String)
    (covers : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    PureReturns runtime [] state
      (apply "gslt:sites:jobs"
        [encoded (PremiseOperationsExecution.DeclarationTyping.declarationsTerm
            (GeneralPlanEnvironment.environment plan).language.terms),
         encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm (plan.snapshot.free.entriesOn footprint)),
         encoded (InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites),
         encoded (PremiseOperationsExecution.DeclarationTyping.boundContextTerm bound),
         encoded (InferenceCettaWire.AuthoredRule.typeTerm expected), encoded (InferenceCettaWire.encodePattern source),
         encoded (encodeList ScopedRuleJobReadoutExecution.rulePlanTerm plan.rules)])
      state (encoded (encodeList ScopedRuleJobReadoutExecution.jobTerm (jobs plan bound expected source))) := by
  metta_lift complete_checked ["declarations", "free", "permissions", "bound", "expected", "source", "rules"]
    (by metta_lift descent_checked ["declarations", "free", "permissions", "bound", "expected", "source", "rules"]
      (transport_call GeneralTypedSiteExecution.program_closed typed_agreement (by decide +kernel) (by decide)
        (by decide +kernel) (by decide) ["declarations", "free", "permissions", "bound", "expected", "source", "rules"]
        (by decide) rfl (by decide +kernel)
        (GeneralTypedSiteExecution.jobs_plan_returns state plan bound expected source footprint covers)))

variable (plan : GeneralExecutionAdmission.Plan)

/-- A job's lane: the job and its deepening search. -/
def entryTerm (entry : Complete.Rounds.Entry (Complete.Step.family plan)) : Term :=
  .application "StepEntry" [ScopedRuleJobReadoutExecution.jobTerm entry.1,
    deepStateTerm (rootWire (Complete.Step.request plan entry.1)) entry.2]

/-- The step search as MeTTa data: `(StepState entries log)`. -/
def stepStateTerm (state : Complete.Step.State plan) : Term :=
  .application "StepState" [encodeList (entryTerm plan) state.entries,
    encodeList ScopedRuleJobReadoutExecution.receiptTerm state.log]

abbrev admittedValue : Atom :=
  encoded (CompletePlanWire.admittedTerm (StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan)))

@[metta_head "gslt:step:family"]
theorem step_family_returns (state : State) (job : Job) :
    PureReturns runtime [] state
      (apply "gslt:step:family" [admittedValue plan, encoded (ScopedRuleJobReadoutExecution.jobTerm job)]) state
      (encoded (rootFamilyTerm (Complete.Step.request plan job))) := by
  metta_call complete_checked
  metta_eval unfolding [admittedValue, ScopedRuleJobReadoutExecution.jobTerm, ScopedRuleJobReadoutExecution.siteTerm,
    rootFamilyTerm, Complete.Step.request]

@[metta_head "gslt:step:entries"]
theorem step_entries_returns (state : State) : ∀ jobs : List Job,
    PureReturns runtime [] state
      (apply "gslt:step:entries" [admittedValue plan, encoded (encodeList ScopedRuleJobReadoutExecution.jobTerm jobs)])
      state (encoded (encodeList (entryTerm plan)
        (jobs.map fun job => (⟨job, Complete.Deep.start (Complete.Step.family plan job)⟩ :
          Complete.Rounds.Entry (Complete.Step.family plan)))))
  | [] => by
    metta_call complete_checked
    metta_eval unfolding [encodeList]
  | job :: rest => by
    have family := step_family_returns plan state job
    have started := deep_start_returns (rootWire (Complete.Step.request plan job)) state
    have later := step_entries_returns state rest
    metta_call complete_checked
    metta_eval [family, started, later] with complete_checked
      unfolding [encodeList, entryTerm, rootWire]

@[metta_head "gslt:step:begin"]
theorem step_begin_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (source : Pattern) (covers : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    PureReturns runtime [] state (apply "gslt:step:begin" [planValue plan table bound expected, patternValue source])
      state (encoded (stepStateTerm plan (Complete.Step.begin plan bound expected source))) := by
  subst tabled
  have listed := complete_jobs_returns state plan bound expected source footprint covers
  have entries := step_entries_returns plan state (jobs plan bound expected source)
  metta_call complete_checked
  metta_eval [listed, entries] with complete_checked
    unfolding [planValue, CompletePlanWire.planTerm, PremiseOperationsExecution.GeneralExecution.environmentTerm,
      PremiseOperationsExecution.DeclarationTyping.declarationsTerm, PremiseOperationsExecution.DeclarationTyping.boundContextTerm,
      admittedValue, stepStateTerm, Complete.Step.begin, Complete.Rounds.begin, encodeList, patternValue,
      GeneralPlanEnvironment.environment]

/-- A firing's receipt at its job's site is `Step.lift`, as `finishRoot` computes it. -/
theorem finish_root_lift (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) (job : Job)
    (licensed : job.Valid plan bound expected source) (firing : Complete.DeepRoot.Firing)
    (valid : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) job.site.focusBound job.site.focusType
      job.site.focus job.ordinal firing.trace firing.captured firing.completed firing.history firing.target) :
    encodeOption (fun answer : GeneralRuleJobExecution.Answer ⟨plan, bound, expected, source, job⟩ =>
        ScopedRuleJobReadoutExecution.receiptTerm answer.val)
      (GeneralRuleJobExecution.finishRoot ⟨plan, bound, expected, source, job⟩ licensed firing.trace firing.captured
        firing.completed firing.history firing.target valid) =
      encodeOption ScopedRuleJobReadoutExecution.receiptTerm (Complete.Step.lift plan bound expected job firing) := by
  unfold GeneralRuleJobExecution.finishRoot Complete.Step.lift
  dsimp only [GeneralRuleJobExecution.Request.environment]
  have freeSame : (GeneralPlanEnvironment.environment plan).free = plan.snapshot.free := rfl
  by_cases represented : job.site.acceptsReplacementRepresentation (GeneralPlanEnvironment.environment plan).language
      firing.target = true
  · by_cases typed : Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted
        (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected
        (job.site.context.fill firing.target) = true
    · simp [represented, typed, freeSame]
    · simp [represented, typed, freeSame]
  · simp [represented]

/-- `gslt:rule:job-finish-root`, in the complete machine's runtime, is `Step.lift`. -/
theorem complete_finish_root_returns (state : State) (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (job : Job) (licensed : job.Valid plan bound expected source) (footprint : List String)
    (firing : Complete.DeepRoot.Firing)
    (valid : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) job.site.focusBound job.site.focusType
      job.site.focus job.ordinal firing.trace firing.captured firing.completed firing.history firing.target)
    (covered : ∀ name ∈ (job.site.context.fill firing.target).freeFvarNames, name ∈ footprint) :
    PureReturns runtime [] state
      (apply "gslt:rule:job-finish-root"
        [encoded (ScopedRuleJobReadoutExecution.requestProjectionTerm ⟨plan, bound, expected, source, job⟩ footprint),
         encoded (PremiseOperationsExecution.GeneralExecution.resultTerm
           (GeneralPremise.Execution.Result.root firing.trace firing.captured firing.completed firing.history
             firing.target valid))])
      state (encoded (encodeOption ScopedRuleJobReadoutExecution.receiptTerm (Complete.Step.lift plan bound expected job
        firing))) := by
  rw [← finish_root_lift plan bound expected source job licensed firing valid]
  metta_from_readout ["request", "result"]
    (ScopedRuleJobReadoutExecution.finish_root_finite_returns state ⟨plan, bound, expected, source, job⟩ licensed
      footprint firing.trace firing.captured firing.completed firing.history firing.target valid covered)

/-- What a firing needs for `gslt:step:lift`: it is a firing of the job's rule at the focus, and its
target, put back in the job's context, stays within the footprint. -/
def LiftReady (job : Job) (footprint : List String) (firing : Complete.DeepRoot.Firing) : Prop :=
  firing.Valid (Complete.Step.request plan job) ∧
    ∀ name ∈ (job.site.context.fill firing.target).freeFvarNames, name ∈ footprint

@[metta_head "gslt:step:lift"]
theorem step_lift_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (source : Pattern) (job : Job) (licensed : job.Valid plan bound expected source) :
    ∀ firings : List Complete.DeepRoot.Firing, (∀ firing ∈ firings, LiftReady plan job footprint firing) →
      PureReturns runtime [] state
        (apply "gslt:step:lift" [planValue plan table bound expected, patternValue source,
          encoded (ScopedRuleJobReadoutExecution.jobTerm job), encoded (encodeList firingTerm firings),
          encoded (InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites)])
        state (encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm
          (firings.filterMap (Complete.Step.lift plan bound expected job))))
  | [], _ => by
    metta_call complete_checked
    metta_eval unfolding [encodeList]
  | firing :: rest, ready => by
    subst tabled
    have later := step_lift_returns state (plan.snapshot.free.entriesOn footprint) bound expected footprint rfl source
      job licensed rest (fun other member => ready other (by simp [member]))
    have finished := complete_finish_root_returns plan state bound expected source job licensed footprint firing
      (ready firing (by simp)).1 (ready firing (by simp)).2
    have freeSame : (GeneralPlanEnvironment.environment plan).free = plan.snapshot.free := rfl
    cases lifted : Complete.Step.lift plan bound expected job firing with
    | none =>
      rw [List.filterMap_cons_none lifted]
      complete_eval [later, finished]
        unfolding [encodeList, planValue, CompletePlanWire.planTerm, lifted, ScopedRuleJobReadoutExecution.jobTerm,
          ScopedRuleJobReadoutExecution.siteTerm, ScopedRuleJobReadoutExecution.requestProjectionTerm,
          PremiseOperationsExecution.GeneralExecution.resultTerm, PremiseOperationsExecution.GeneralExecution.goalTerm,
          firingTerm, GeneralRuleJobExecution.Request.environment, GeneralRuleJobExecution.Request.goal,
          PremiseOperationsExecution.GeneralExecution.Base.typesTerm, freeSame, patternValue]
    | some receipt =>
      rw [List.filterMap_cons_some lifted]
      complete_eval [later, finished]
        unfolding [encodeList, planValue, CompletePlanWire.planTerm, lifted, ScopedRuleJobReadoutExecution.jobTerm,
          ScopedRuleJobReadoutExecution.siteTerm, ScopedRuleJobReadoutExecution.requestProjectionTerm,
          PremiseOperationsExecution.GeneralExecution.resultTerm, PremiseOperationsExecution.GeneralExecution.goalTerm,
          firingTerm, GeneralRuleJobExecution.Request.environment, GeneralRuleJobExecution.Request.goal,
          PremiseOperationsExecution.GeneralExecution.Base.typesTerm, freeSame, patternValue]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
