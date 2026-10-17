import Mettapedia.OSLF.MeTTaIL.Complete.DeepRoot
import Mettapedia.OSLF.MeTTaIL.Complete.Rounds
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics
import Mettapedia.Machines.ResumableSearchRunner

/-!
# Every rule job of a term, fairly

A term's rule jobs are its licensed sites paired with the plan's rules (`GeneralRuleJobs.jobs`).
Each job is a deepening search of its rule at its site's focus (`Complete.DeepRoot`). A round
gives every job one unit of work, so no job starves another, even when one job's search never
ends. Each firing a job publishes for the first time is checked at its site (replacement shape and
the typing of the filled term) and appended to a chronological log of receipts.

The log is the publication of a resumable search (`ResumableSearchRunner.Search`):

- `search_lawful`: more work never restarts it, its log only grows, and every logged receipt is a
  valid receipt of the plan at the term;
- `complete_in_limit`: every valid receipt is logged after finitely many rounds, for every plan,
  with no stratification or admission assumption;
- `exact_of_complete`: once every job is certified, the log holds every valid receipt.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Step

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Machines.ResumableSearchRunner (Search Status)

section

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)

/-- The deepening search of a job: its rule at its site's focus. -/
def request (job : GeneralRuleJobs.Job) : DeepRoot.Request :=
  ⟨GeneralPlanEnvironment.environment plan, job.site.focusBound, job.site.focusType, job.site.focus, job.ordinal⟩

/-- A firing of a job as a receipt at the term, when its target fits the site. -/
def lift (job : GeneralRuleJobs.Job) (firing : DeepRoot.Firing) : Option GeneralRuleJobs.Receipt :=
  if job.site.acceptsReplacementRepresentation (GeneralPlanEnvironment.environment plan).language firing.target &&
      checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected
        (job.site.context.fill firing.target) then
    some ⟨job, firing.trace, firing.captured, firing.completed, firing.history, firing.target,
      job.site.context.fill firing.target⟩
  else none

/-- The deepening search of each job, as a lane of the fair rounds. -/
abbrev family (job : GeneralRuleJobs.Job) : Deep.Family := DeepRoot.family (request plan job)

/-- The jobs of a term with their searches, and the receipt log. -/
abbrev State := Rounds.State (family plan) (Receipt := GeneralRuleJobs.Receipt)

/-- `work` rounds. -/
abbrev rounds (work : Nat) (state : State plan) : State plan :=
  Rounds.rounds (family plan) (lift plan bound expected) work state

/-- The jobs of a term, before any work. -/
abbrev begin (source : Pattern) : State plan :=
  Rounds.begin (family plan) (GeneralRuleJobs.jobs plan bound expected source)

/-- Complete when every job is certified and drained; otherwise pending. -/
def status (state : State plan) : Status :=
  if Rounds.complete (family plan) state then .complete else .pending

/-- The rule jobs of a term as a resumable search. -/
def search : Search Pattern (State plan) GeneralRuleJobs.Receipt where
  run source work := rounds plan bound expected work (begin plan bound expected source)
  resume state work := rounds plan bound expected work state
  publication := Rounds.State.log
  status := status plan
  target := GeneralRuleJobs.Receipt.target
  Valid source receipt := receipt.Valid plan bound expected source

theorem rounds_add (first second : Nat) (state : State plan) :
    rounds plan bound expected (first + second) state =
      rounds plan bound expected second (rounds plan bound expected first state) :=
  Rounds.rounds_add _ _ first second state

theorem rounds_log_prefix (work : Nat) (state : State plan) :
    state.log <+: (rounds plan bound expected work state).log :=
  Rounds.rounds_log_prefix _ _ work state

/-! ## Receipts and firings -/

/-- The firing a receipt records. -/
def firingOf (receipt : GeneralRuleJobs.Receipt) : DeepRoot.Firing :=
  ⟨receipt.matcherTrace, receipt.captured, receipt.completed, receipt.premiseHistory, receipt.localTarget⟩

theorem lift_valid {source : Pattern} {job : GeneralRuleJobs.Job} {firing : DeepRoot.Firing}
    {receipt : GeneralRuleJobs.Receipt} (licensed : job.Valid plan bound expected source)
    (valid : firing.Valid (request plan job)) (lifted : lift plan bound expected job firing = some receipt) :
    receipt.Valid plan bound expected source := by
  unfold lift at lifted
  split at lifted
  · rename_i checked
    cases lifted
    simp only [Bool.and_eq_true] at checked
    exact ⟨licensed, valid, checked.1, rfl, checkOpenPatternWellSorted_sound checked.2⟩
  · cases lifted

theorem lift_of_valid {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid plan bound expected source) :
    (firingOf receipt).Valid (request plan receipt.job) ∧
      lift plan bound expected receipt.job (firingOf receipt) = some receipt := by
  obtain ⟨_, fired, represented, endpoint, typed⟩ := valid
  refine ⟨fired, ?_⟩
  have checked : checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
      bound expected (receipt.job.site.context.fill receipt.localTarget) = true := by
    rw [← endpoint]
    exact checkOpenPatternWellSorted_complete typed
  unfold lift
  rw [if_pos (by simp only [firingOf, Bool.and_eq_true]; exact ⟨represented, checked⟩)]
  cases receipt
  simp only [firingOf] at endpoint ⊢
  rw [endpoint]

/-! ## The log -/

/-- The job publications after a number of rounds. -/
abbrev published (job : GeneralRuleJobs.Job) (work : Nat) : List DeepRoot.Firing :=
  Rounds.published (family plan) job work

theorem log_sound (source : Pattern) (work : Nat) :
    ∀ receipt ∈ (rounds plan bound expected work (begin plan bound expected source)).log,
      ∃ job ∈ GeneralRuleJobs.jobs plan bound expected source, ∃ firing ∈ published plan job work,
        lift plan bound expected job firing = some receipt :=
  Rounds.log_sound (family plan) (lift plan bound expected) (GeneralRuleJobs.jobs plan bound expected source) work

theorem log_complete (source : Pattern) (work : Nat) :
    ∀ job ∈ GeneralRuleJobs.jobs plan bound expected source, ∀ firing ∈ published plan job work,
      ∀ receipt, lift plan bound expected job firing = some receipt →
        receipt ∈ (rounds plan bound expected work (begin plan bound expected source)).log :=
  Rounds.log_complete (family plan) (lift plan bound expected) (GeneralRuleJobs.jobs plan bound expected source) work

/-! ## The search -/

/-- **Sound.** Every logged receipt is a valid receipt of the plan at the term. -/
theorem sound (source : Pattern) (work : Nat) :
    ∀ receipt ∈ (rounds plan bound expected work (begin plan bound expected source)).log,
      receipt.Valid plan bound expected source := by
  intro receipt member
  obtain ⟨job, present, firing, found, lifted⟩ := log_sound plan bound expected source work receipt member
  exact lift_valid plan bound expected ((GeneralRuleJobs.jobs_spec plan bound expected source job).mp present)
    (DeepRoot.sound (request plan job) work firing found) lifted

theorem search_lawful : (search plan bound expected).Lawful where
  resume_run source first extra := (rounds_add plan bound expected first extra _).symm
  publication_prefix source first extra := by
    change (rounds plan bound expected first _).log <+: (rounds plan bound expected (first + extra) _).log
    rw [rounds_add]
    exact rounds_log_prefix plan bound expected extra _
  sound source work receipt member := sound plan bound expected source work receipt member

/-- **Complete in the limit.** Every valid receipt of the plan at the term is logged after
finitely many rounds, for every plan. -/
theorem complete_in_limit {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid plan bound expected source) :
    ∃ work, receipt ∈ (rounds plan bound expected work (begin plan bound expected source)).log := by
  obtain ⟨fired, lifted⟩ := lift_of_valid plan bound expected valid
  obtain ⟨work, found⟩ := DeepRoot.complete_in_limit fired
  exact ⟨work, log_complete plan bound expected source work receipt.job
    ((GeneralRuleJobs.jobs_spec plan bound expected source receipt.job).mpr valid.1) _ found receipt lifted⟩

/-- **A complete search is exact.** Once every job is certified and drained, the log holds every
valid receipt of the plan at the term. -/
theorem exact_of_complete {source : Pattern} {work : Nat}
    (done : status plan (rounds plan bound expected work (begin plan bound expected source)) = .complete)
    {receipt : GeneralRuleJobs.Receipt} (valid : receipt.Valid plan bound expected source) :
    receipt ∈ (rounds plan bound expected work (begin plan bound expected source)).log := by
  obtain ⟨fired, lifted⟩ := lift_of_valid plan bound expected valid
  have present := (GeneralRuleJobs.jobs_spec plan bound expected source receipt.job).mpr valid.1
  have every : Rounds.complete (family plan) (rounds plan bound expected work (begin plan bound expected source)) = true := by
    unfold status at done
    split at done
    · assumption
    · cases done
  have certified := (Rounds.complete_iff (family plan) (lift plan bound expected)
    (GeneralRuleJobs.jobs plan bound expected source) work).mp every receipt.job present
  exact log_complete plan bound expected source work receipt.job present _
    (DeepRoot.exact_of_complete (request plan receipt.job) work certified fired) receipt lifted

/-! ## Admitted plans finish -/

theorem status_complete_iff (source : Pattern) (work : Nat) :
    status plan (rounds plan bound expected work (begin plan bound expected source)) = .complete ↔
      ∀ job ∈ GeneralRuleJobs.jobs plan bound expected source,
        (DeepRoot.run (request plan job) work (DeepRoot.start (request plan job))).complete = true := by
  rw [← Rounds.complete_iff (family plan) (lift plan bound expected) (GeneralRuleJobs.jobs plan bound expected source)]
  unfold status
  split <;> simp_all

/-- **Admitted plans finish.** When the plan's environment passes the structural admission check,
some finite number of rounds completes the search at every term. -/
theorem eventually_complete
    (admitted : StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan) = true)
    (source : Pattern) :
    ∃ work, status plan (rounds plan bound expected work (begin plan bound expected source)) = .complete := by
  obtain ⟨work, done⟩ := Rounds.eventually_complete (family plan) (lift plan bound expected)
    (GeneralRuleJobs.jobs plan bound expected source)
    (fun job _ => DeepRoot.eventually_complete (request plan job) admitted)
  exact ⟨work, (status_complete_iff plan bound expected source work).mpr
    ((Rounds.complete_iff (family plan) (lift plan bound expected)
      (GeneralRuleJobs.jobs plan bound expected source) work).mp done)⟩

/-- Completion is kept by more rounds. -/
theorem complete_mono {source : Pattern} {work : Nat}
    (done : status plan (rounds plan bound expected work (begin plan bound expected source)) = .complete)
    {later : Nat} (after : work ≤ later) :
    status plan (rounds plan bound expected later (begin plan bound expected source)) = .complete := by
  rw [status_complete_iff] at done ⊢
  exact fun job present => DeepRoot.complete_mono _ (done job present) after

end

end Mettapedia.OSLF.MeTTaIL.Complete.Step
