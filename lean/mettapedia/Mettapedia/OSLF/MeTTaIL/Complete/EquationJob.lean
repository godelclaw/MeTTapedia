import Mettapedia.OSLF.MeTTaIL.Complete.Rounds
import Mettapedia.OSLF.MeTTaIL.Complete.EquationDepth
import Mettapedia.OSLF.MeTTaIL.GeneralEquationMatcherWork
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseEventEquality

/-!
# The equation steps of a term, complete in the limit

An equation job is an oriented compiled equation at a licensed site of a term
(`GeneralEquationJobs.jobs`). Its left side is matched at the site's focus by the scoped matcher,
run to completion. Each accepted match starts a deepening search (`Complete.Deep`) of the
equation's premises; the premises may call any rule recursively. Each premise outcome is finished
by the job's local checks (`GeneralEquationJobs.finish`): typed assignments, the reduct, and the
replacement and filled-term sorting.

A lane is a job with one accepted match; all lanes of a term run in fair rounds (`Complete.Rounds`).

- `sound`: every logged receipt is a completed equation instance at the term;
- `complete_in_limit`: every completed equation instance at the term is logged after finitely
  many rounds;
- `exact_of_complete`: once every lane is certified, the log holds every completed instance.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.EquationJob

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted
open StructuralDescent (eventsDepth)
open StructuralDescent.Scheduled (Goal Result)

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)

/-- What a premise derivation produces: the completed assignment and the ordered history. -/
structure Outcome where
  completed : ScopedRuleMatching.Assignment
  history : List Event
  deriving DecidableEq

/-- The record of a premise-list result. -/
def readOutcome {environment : Environment} {depth : Nat} {context : Context} {premises : List Premise}
    {captured : ScopedRuleMatching.Assignment} :
    Result environment (.premises depth context premises captured) → Outcome
  | .premises completed events _ => ⟨completed, events⟩

/-- The depth every premise derivation of a job fits in, at a capture: when the environment's
rules and the equation's premises descend and the capture binds the left side
(`EquationDepth.premises_depth_le`). -/
def premisesBound (job : GeneralEquationJobs.Job) (captured : ScopedRuleMatching.Assignment) : Option Nat :=
  if (StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan) &&
      StructuralDescent.checkPremises job.equation.rule job.equation.binding.spec 0 job.equation.rule.premises) &&
      EquationDepth.capturesLeft job.equation.rule captured then
    some (EquationDepth.leftWeight job.equation.rule captured)
  else none

/-- The premises of an equation job at a captured assignment, as a deepening family. -/
abbrev premisesFamily (job : GeneralEquationJobs.Job) (captured : ScopedRuleMatching.Assignment) : Deep.Family where
  environment := GeneralPlanEnvironment.environment plan
  goal depth := .premises depth (job.context plan) job.equation.rule.premises captured
  Payload := Outcome
  read := readOutcome
  Valid outcome := PremisesHold (GeneralPlanEnvironment.environment plan) (job.context plan)
    job.equation.rule.premises captured outcome.completed outcome.history
  read_valid result := by
    cases result with
    | premises completed events valid => exact valid
  build outcome valid _ := .premises outcome.completed outcome.history valid
  read_build _ _ _ := rfl
  required outcome := eventsDepth outcome.history
  build_ordered outcome _ depth enough := by
    change decide (eventsDepth outcome.history ≤ depth) = true
    exact decide_eq_true enough
  bound := premisesBound plan job captured
  bound_sound limit bounded outcome valid := by
    unfold premisesBound at bounded
    split at bounded
    · rename_i checks
      cases bounded
      simp only [Bool.and_eq_true] at checks
      exact EquationDepth.premises_depth_le valid checks.1.2 rfl
        (EquationDepth.captures_of_capturesLeft checks.2) (GeneralScopedMatch.Extends.refl _) checks.1.1
    · cases bounded

/-- A lane: an equation job with one accepted match of its left side. -/
structure Lane where
  job : GeneralEquationJobs.Job
  answer : GeneralScopedMatchMachine.Answer

abbrev family (lane : Lane) : Deep.Family := premisesFamily plan lane.job lane.answer.assignment

/-- A premise outcome of a lane, finished by the job's local checks. -/
def lift (lane : Lane) (outcome : Outcome) : Option GeneralEquationJobs.Receipt :=
  GeneralEquationJobs.finish plan bound expected lane.job lane.answer.trace lane.answer.assignment
    outcome.completed outcome.history

/-- The matcher of a job's left side at its focus. -/
abbrev matcher (source : Pattern) (job : GeneralEquationJobs.Job) : GeneralScopedMatchMachine.Request :=
  GeneralEquationJobExecution.Request.matcher ⟨plan, bound, expected, source, job⟩

/-- All leftMatches of a job's left side, by the completed matcher. -/
def leftMatches (source : Pattern) (job : GeneralEquationJobs.Job) : List GeneralScopedMatchMachine.Answer :=
  (GeneralEquationJobExecution.finishMatcher (matcher plan bound expected source job)
    (GeneralScopedMatchMachine.start (matcher plan bound expected source job))).answers

/-- The lanes of a well-sorted term: every job with every typed match. -/
def lanes (source : Pattern) : List Lane :=
  if checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
      bound expected source then
    (GeneralEquationJobs.jobs plan bound expected source).flatMap fun job =>
      ((leftMatches plan bound expected source job).filter fun answer =>
        checkTypedAssignment (GeneralPlanEnvironment.environment plan) (job.context plan) answer.assignment).map
        fun answer => ⟨job, answer⟩
  else []

abbrev State := Rounds.State (family plan) (Receipt := GeneralEquationJobs.Receipt)

abbrev rounds (work : Nat) (state : State plan) : State plan :=
  Rounds.rounds (family plan) (lift plan bound expected) work state

abbrev begin (source : Pattern) : State plan :=
  Rounds.begin (family plan) (lanes plan bound expected source)

/-- The log after some rounds. -/
abbrev logAt (source : Pattern) (work : Nat) : List GeneralEquationJobs.Receipt :=
  (rounds plan bound expected work (begin plan bound expected source)).log

/-- The rounds are complete: every lane is certified and drained. -/
abbrev complete (source : Pattern) (work : Nat) : Bool :=
  Rounds.complete (family plan) (rounds plan bound expected work (begin plan bound expected source))

theorem mem_lanes {source : Pattern} {lane : Lane} :
    lane ∈ lanes plan bound expected source ↔
      checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
        bound expected source = true ∧
      lane.job ∈ GeneralEquationJobs.jobs plan bound expected source ∧
      lane.answer ∈ leftMatches plan bound expected source lane.job ∧
      checkTypedAssignment (GeneralPlanEnvironment.environment plan) (lane.job.context plan)
        lane.answer.assignment = true := by
  unfold lanes
  split
  · rename_i checked
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter, checked, true_and]
    constructor
    · rintro ⟨job, present, answer, ⟨found, typed⟩, rfl⟩
      exact ⟨present, found, typed⟩
    · rintro ⟨present, found, typed⟩
      exact ⟨lane.job, present, lane.answer, ⟨found, typed⟩, rfl⟩
  · rename_i unchecked
    simp [unchecked]

theorem mem_leftMatches {source : Pattern} {job : GeneralEquationJobs.Job} {answer : GeneralScopedMatchMachine.Answer} :
    answer ∈ leftMatches plan bound expected source job ↔
      GeneralScopedMatchMachine.TracedMatches job.equation.rule job.equation.binding.spec
        job.site.focusBound.length .left [] 0 [] job.equation.rule.left job.site.focus.eraseBinderMetadata
        answer.trace answer.assignment :=
  GeneralEquationJobExecution.finishMatcher_answers_iff .start answer

/-- **Sound.** Every logged receipt is a completed equation instance at the term. -/
theorem sound (source : Pattern) (work : Nat) :
    ∀ receipt ∈ logAt plan bound expected source work,
      GeneralEquationJobs.Completion plan bound expected source receipt := by
  intro receipt member
  obtain ⟨lane, present, outcome, found, lifted⟩ :=
    Rounds.log_sound (family plan) (lift plan bound expected) (lanes plan bound expected source) work receipt member
  obtain ⟨checked, job, matched, _⟩ := (mem_lanes plan bound expected).mp present
  exact GeneralEquationJobs.finish_sound ((GeneralEquationJobs.jobs_iff _ _ _ _ _).mp job)
    (checkOpenPatternWellSorted_sound checked) ((mem_leftMatches plan bound expected).mp matched)
    (Deep.sound (family plan lane) work outcome found) lifted

/-- The lane and outcome of a completed instance. -/
theorem lane_of_completion {source : Pattern} {receipt : GeneralEquationJobs.Receipt}
    (completion : GeneralEquationJobs.Completion plan bound expected source receipt) :
    (⟨receipt.job, ⟨receipt.captured, receipt.matcherTrace⟩⟩ : Lane) ∈ lanes plan bound expected source ∧
      (family plan ⟨receipt.job, ⟨receipt.captured, receipt.matcherTrace⟩⟩).Valid
        (⟨receipt.completed, receipt.premiseHistory⟩ : Outcome) ∧
      lift plan bound expected ⟨receipt.job, ⟨receipt.captured, receipt.matcherTrace⟩⟩
        ⟨receipt.completed, receipt.premiseHistory⟩ = some receipt := by
  refine ⟨(mem_lanes plan bound expected).mpr ⟨checkOpenPatternWellSorted_complete completion.sourceTyped,
      (GeneralEquationJobs.jobs_iff _ _ _ _ _).mpr completion.job,
      (mem_leftMatches plan bound expected).mpr completion.matched,
      checkTypedAssignment_complete completion.capturedTyped⟩, completion.premises, ?_⟩
  exact GeneralEquationJobs.finish_complete completion

/-- **Complete in the limit.** Every completed equation instance at the term is logged after
finitely many rounds. -/
theorem complete_in_limit {source : Pattern} {receipt : GeneralEquationJobs.Receipt}
    (completion : GeneralEquationJobs.Completion plan bound expected source receipt) :
    ∃ work, receipt ∈ logAt plan bound expected source work := by
  obtain ⟨present, valid, lifted⟩ := lane_of_completion plan bound expected completion
  obtain ⟨work, found⟩ := Deep.complete_in_limit (family plan _) valid
  exact ⟨work, Rounds.log_complete (family plan) (lift plan bound expected) (lanes plan bound expected source)
    work _ present _ found receipt lifted⟩

/-- **A complete search is exact.** -/
theorem exact_of_complete {source : Pattern} {work : Nat} (done : complete plan bound expected source work = true)
    {receipt : GeneralEquationJobs.Receipt}
    (completion : GeneralEquationJobs.Completion plan bound expected source receipt) :
    receipt ∈ logAt plan bound expected source work := by
  obtain ⟨present, valid, lifted⟩ := lane_of_completion plan bound expected completion
  have certified := (Rounds.complete_iff (family plan) (lift plan bound expected) (lanes plan bound expected source)
    work).mp done _ present
  exact Rounds.log_complete (family plan) (lift plan bound expected) (lanes plan bound expected source)
    work _ present _ (Deep.exact_of_complete (family plan _) work certified valid) receipt lifted

theorem log_prefix (source : Pattern) (work extra : Nat) :
    logAt plan bound expected source work <+: logAt plan bound expected source (work + extra) := by
  change (rounds plan bound expected work _).log <+: (rounds plan bound expected (work + extra) _).log
  rw [show rounds plan bound expected (work + extra) (begin plan bound expected source) =
      rounds plan bound expected extra (rounds plan bound expected work (begin plan bound expected source)) from
    Rounds.rounds_add _ _ work extra _]
  exact Rounds.rounds_log_prefix _ _ extra _

/-- A lane's finished outcome is a completed equation instance at the term. -/
theorem lift_sound {source : Pattern} {lane : Lane} (present : lane ∈ lanes plan bound expected source)
    {outcome : Outcome} (valid : (family plan lane).Valid outcome) {receipt : GeneralEquationJobs.Receipt}
    (lifted : lift plan bound expected lane outcome = some receipt) :
    GeneralEquationJobs.Completion plan bound expected source receipt := by
  obtain ⟨checked, job, matched, _⟩ := (mem_lanes plan bound expected).mp present
  exact GeneralEquationJobs.finish_sound ((GeneralEquationJobs.jobs_iff _ _ _ _ _).mp job)
    (checkOpenPatternWellSorted_sound checked) ((mem_leftMatches plan bound expected).mp matched) valid lifted

/-! ## Termination -/

/-- A lane's capture binds every variable of the equation's left side. -/
theorem capturesLeft_of_mem_lanes {source : Pattern} {lane : Lane} (present : lane ∈ lanes plan bound expected source) :
    EquationDepth.capturesLeft lane.job.equation.rule lane.answer.assignment = true := by
  obtain ⟨_, _, matched, _⟩ := (mem_lanes plan bound expected).mp present
  have captures := GeneralEquationCaptureDomain.matched_captures ((mem_leftMatches plan bound expected).mp matched).matching
  apply List.all_eq_true.mpr
  intro name member
  obtain ⟨value, found⟩ := captures name member
  simp only [found, Option.isSome_some]

/-- **A lane finishes** when the environment's rules and the equation's premises descend. -/
theorem lane_eventually_complete {source : Pattern} {lane : Lane} (present : lane ∈ lanes plan bound expected source)
    (admitted : StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan) = true)
    (descends : StructuralDescent.checkPremises lane.job.equation.rule lane.job.equation.binding.spec 0
      lane.job.equation.rule.premises = true) :
    ∃ work, (Deep.run (family plan lane) work (Deep.start (family plan lane))).complete = true :=
  Deep.eventually_complete (family plan lane) (limit := EquationDepth.leftWeight lane.job.equation.rule lane.answer.assignment)
    (by simp [premisesBound, admitted, descends,
      capturesLeft_of_mem_lanes plan bound expected present])

end Mettapedia.OSLF.MeTTaIL.Complete.EquationJob
