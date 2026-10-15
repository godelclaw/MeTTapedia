import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobFiniteWork
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionTermination

/-!
# Schema-derived finite work for every actual authored equation job

The finite inner continuation trees are constructed from the actual authored
premise syntax and selected declaration strata. The outer equation scheduler
therefore has an executable work bound with no finite carrier, execution rank,
answer list or completeness hypothesis supplied by its caller. Its result is
settled; unresolved obligations remain explicit and prevent completeness.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution

open GeneralPremise.Scheduler GeneralEquationJobs

def authoredPremiseForests (request : Request) : PremiseForests request :=
  fun captured => .cons
    (GeneralPremise.Execution.treeStart request.environment (request.premises captured)) .nil

def authoredWork (request : Request)
    (licensed : LicensedJob request.plan request.bound request.expected request.source request.job) : Nat :=
  workBound request licensed (authoredPremiseForests request)

def finishJob (request : Request)
    (licensed : LicensedJob request.plan request.bound request.expected request.source request.job) : State request :=
  run request (authoredWork request licensed) (start request licensed)

theorem finishJob_reachable (request : Request)
    (licensed : LicensedJob request.plan request.bound request.expected request.source request.job) :
    Reachable request licensed (finishJob request licensed) :=
  finishState_reachable request licensed (authoredPremiseForests request)

theorem finishJob_settled (request : Request)
    (licensed : LicensedJob request.plan request.bound request.expected request.source request.job) :
    settled (finishJob request licensed) = true :=
  finishState_settled request licensed (authoredPremiseForests request)

theorem finishJob_readouts (request : Request)
    (licensed : LicensedJob request.plan request.bound request.expected request.source request.job) :
    (finishJob request licensed).answers = (start request licensed).answers ++
      (startForest request licensed (authoredPremiseForests request)).answers ∧
    (finishJob request licensed).unresolved = (start request licensed).unresolved ++
      (startForest request licensed (authoredPremiseForests request)).obligations :=
  finishState_readouts request licensed (authoredPremiseForests request)

theorem authored_job_finiteDrain (request : Request)
    (licensed : LicensedJob request.plan request.bound request.expected request.source request.job) :
    ∃ fuel, settled (run request fuel (start request licensed)) = true :=
  ⟨authoredWork request licensed, finishJob_settled request licensed⟩

/-- The actual resumable state does not store or compute this forest.
Reachability inherits its existence through each real microstep. -/
theorem reachable_finiteWork {request : Request}
    {licensed : LicensedJob request.plan request.bound request.expected request.source request.job}
    {state : State request} (reached : Reachable request licensed state) :
    Nonempty (TaskForest (expand request) state.agenda) := by
  induction reached with
  | start => exact ⟨startForest request licensed (authoredPremiseForests request)⟩
  | tick reached ih =>
      obtain ⟨forest⟩ := ih
      exact ⟨forest.advance _⟩

theorem settled_reachable_finishJob {request : Request}
    {licensed : LicensedJob request.plan request.bound request.expected request.source request.job}
    {state : State request} (reached : Reachable request licensed state) (idle : settled state = true) :
    state = finishJob request licensed :=
  settled_reachable_unique reached idle (authoredPremiseForests request)

theorem completed_reachable_finishJob {request : Request}
    {licensed : LicensedJob request.plan request.bound request.expected request.source request.job}
    {state : State request} (reached : Reachable request licensed state) (finished : complete state = true) :
    state = finishJob request licensed :=
  settled_reachable_finishJob reached
    (List.isEmpty_iff.mpr ((complete_iff state).mp finished).1)

end Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution
