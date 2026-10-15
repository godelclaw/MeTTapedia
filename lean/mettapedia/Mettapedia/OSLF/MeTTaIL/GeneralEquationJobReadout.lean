import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobCertifiedWork

/-!
# Origin-preserving readouts of the actual equation scheduler

Every published receipt comes from the requested authored declaration and
licensed zipper. These readouts do not identify equal endpoints or erase
independent match and premise histories.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution

open GeneralPremise.Scheduler GeneralEquationJobs

theorem finish_receipt_job {plan : GeneralExecutionAdmission.Plan} {bound : List Syntax.TypeExpr}
    {expected : Syntax.TypeExpr} {job : Job} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    {receipt : Receipt}
    (finished : finish plan bound expected job trace captured completed history = some receipt) :
    receipt.job = job := by
  obtain ⟨_, _, raw, _, _, same⟩ := finish_readout _ _ _ _ _ _ _ _ _ finished
  exact congrArg Receipt.job same

theorem expand_answers_job (request : Request) (task : Task request)
    (answer : Answer request) (member : answer ∈ (expand request task).answers) :
    answer.val.job = request.job := by
  cases task with
  | matching frame =>
      simp only [expand, expandMatching] at member
      repeat' split at member
      all_goals simp only [List.not_mem_nil] at member
  | premises frame =>
      simp only [expand, expandPremises] at member
      repeat' split at member
      all_goals simp only [List.not_mem_nil, List.mem_singleton] at member
      all_goals
        subst answer
        exact finish_receipt_job (by assumption)

def RequestedAnswers {request : Request} (state : State request) : Prop :=
  ∀ answer, answer ∈ state.answers → answer.val.job = request.job

theorem tick_requested_answers (request : Request) (state : State request)
    (requested : RequestedAnswers state) : RequestedAnswers (tick request state) := by
  intro answer member
  cases agenda : state.agenda with
  | nil => exact requested answer (by simpa only [tick, GeneralPremise.Scheduler.tick, agenda] using member)
  | cons task tasks =>
      simp only [tick, GeneralPremise.Scheduler.tick, agenda, List.mem_append] at member
      exact member.elim (requested answer) (expand_answers_job request task answer)

theorem run_requested_answers (request : Request) (fuel : Nat) (state : State request)
    (requested : RequestedAnswers state) : RequestedAnswers (run request fuel state) := by
  induction fuel generalizing state with
  | zero => exact requested
  | succ fuel ih => exact ih _ (tick_requested_answers request state requested)

theorem reachable_requested_answers {request : Request}
    {licensed : LicensedJob request.plan request.bound request.expected request.source request.job}
    {state : State request} (reached : Reachable request licensed state) : RequestedAnswers state := by
  induction reached with
  | start =>
      intro answer member
      simp only [start] at member
      split at member <;> simp only [List.not_mem_nil] at member
  | tick reached ih => exact tick_requested_answers request _ ih

theorem emitted_requested_completion {request : Request}
    {licensed : LicensedJob request.plan request.bound request.expected request.source request.job}
    {state : State request} (reached : Reachable request licensed state)
    {answer : Answer request} (member : answer ∈ state.answers) :
    answer.val.job = request.job ∧
      Completion request.plan request.bound request.expected request.source answer.val :=
  ⟨reachable_requested_answers reached answer member, answer.property⟩

end Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution
