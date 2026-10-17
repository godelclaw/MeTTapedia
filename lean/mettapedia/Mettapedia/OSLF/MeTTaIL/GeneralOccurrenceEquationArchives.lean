import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceCertificate

/-!+# Retained equation work and complete cursor readouts

Each source-universe equation job remains represented by a pending scan,
an active cursor or a drained archive. Consumed cursor prefixes have their
complete receipts in the edge ledger; a paused cursor preserves the rest.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralOccurrenceKeys

def EquationPromise (request : Request) (source : Pattern) (job : GeneralEquationJobs.Job) :
    Task request → Prop
  | .universe => source ∈ request.universe
  | .scanUniverse remaining => source ∈ remaining
  | .equation frame => frame.source = source ∧ equationJob frame.job = equationJob job
  | _ => False

def EquationTracked (request : Request) (state : State request) (source : Pattern)
    (job : GeneralEquationJobs.Job) : Prop :=
  (∃ task ∈ state.agenda, EquationPromise request source job task) ∨
    ∃ archive ∈ state.checkedEquations,
      archive.frame.source = source ∧ equationJob archive.frame.job = equationJob job

def EquationCursorRead (request : Request) (state : State request) (frame : EquationFrame request) : Prop :=
  frame.cursor ≤ frame.state.answers.length ∧
    ∀ answer ∈ frame.state.answers.take frame.cursor,
      (frame.source, equationReplayRecord answer.val) ∈ edgeKeys request state

theorem edgeKeys_tick_mono (request : Request) (state : State request) :
    ∀ key ∈ edgeKeys request state, key ∈ edgeKeys request (tick request state) := by
  intro key member
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using member
  | cons task remaining =>
      simp only [edgeKeys, tick, agenda, List.map_append, List.mem_append]
      exact Or.inl member

theorem EquationCursorRead.mono {request : Request} {first second : State request}
    {frame : EquationFrame request} (read : EquationCursorRead request first frame)
    (inclusion : ∀ key ∈ edgeKeys request first, key ∈ edgeKeys request second) :
    EquationCursorRead request second frame :=
  ⟨read.1, fun answer member => inclusion _ (read.2 answer member)⟩

theorem EquationCursorRead.start (request : Request) (state : State request)
    (source : Pattern) (job : GeneralEquationJobs.Job)
    (licensed : GeneralEquationJobs.LicensedJob request.plan request.bound request.expected source job) :
    EquationCursorRead request state
      ⟨source, job, licensed, GeneralEquationJobExecution.start (equationRequest request source job) licensed,
        .start, 0⟩ := by
  constructor
  · exact Nat.zero_le _
  · intro answer member
    simp only [List.take_zero, List.not_mem_nil] at member

theorem EquationCursorRead.inner_tick {request : Request} {state : State request}
    {frame : EquationFrame request} (read : EquationCursorRead request state frame) :
    EquationCursorRead request state {frame with
      state := GeneralEquationJobExecution.tick (equationRequest request frame.source frame.job) frame.state
      reachable := .tick frame.reachable} := by
  obtain ⟨tail, same⟩ := GeneralPremise.Scheduler.tick_answers_prefix
    (GeneralEquationJobExecution.expand (equationRequest request frame.source frame.job)) frame.state
  have bound := read.1
  constructor
  · change frame.cursor ≤ (GeneralEquationJobExecution.tick _ frame.state).answers.length
    change frame.cursor ≤ (GeneralPremise.Scheduler.tick _ frame.state).answers.length
    rw [same, List.length_append]
    omega
  · intro answer member
    change answer ∈ (GeneralPremise.Scheduler.tick _ frame.state).answers.take frame.cursor at member
    rw [same, List.take_append_of_le_length read.1] at member
    exact read.2 answer member

theorem EquationCursorRead.deliver {request : Request} {first second : State request}
    {frame : EquationFrame request} (read : EquationCursorRead request first frame)
    (inclusion : ∀ key ∈ edgeKeys request first, key ∈ edgeKeys request second)
    (answer : GeneralEquationJobExecution.Answer (equationRequest request frame.source frame.job))
    (found : frame.state.answers[frame.cursor]? = some answer)
    (published : (frame.source, equationReplayRecord answer.val) ∈ edgeKeys request second) :
    EquationCursorRead request second {frame with cursor := frame.cursor + 1} := by
  constructor
  · have within := (List.getElem?_eq_some_iff.mp found).1
    exact within
  · intro next member
    change next ∈ frame.state.answers.take (frame.cursor + 1) at member
    rw [List.take_add_one, found] at member
    simp only [Option.toList_some, List.mem_append, List.mem_singleton] at member
    rcases member with prior | same
    · exact inclusion _ (read.2 next prior)
    · subst next
      exact published

theorem equationArchive_read {request : Request} {state : State request}
    (archive : EquationArchive request) (read : EquationCursorRead request state archive.frame) :
    equationArchiveRead request state archive = true := by
  apply List.all_eq_true.mpr
  intro answer member
  apply decide_eq_true_eq.mpr
  have after := List.getElem?_eq_none_iff.mp archive.readAll
  have bound := read.1
  have same : archive.frame.cursor = archive.frame.state.answers.length := by omega
  apply read.2 answer
  simpa only [same, List.take_length] using member

theorem equationTasks_promise (request : Request) (source : Pattern) (job : GeneralEquationJobs.Job)
    (member : job ∈ GeneralEquationJobs.jobs request.plan request.bound request.expected source) :
    ∃ task ∈ equationTasks request source, EquationPromise request source job task := by
  let item : {job // job ∈ GeneralEquationJobs.jobs request.plan request.bound request.expected source} := ⟨job, member⟩
  refine ⟨.equation ⟨source, job, (GeneralEquationJobs.jobs_iff _ _ _ _ _).mp member,
    GeneralEquationJobExecution.start (equationRequest request source job)
      ((GeneralEquationJobs.jobs_iff _ _ _ _ _).mp member), .start, 0⟩, ?_, rfl, rfl⟩
  exact List.mem_map.mpr ⟨item, List.mem_attach _ _, rfl⟩

theorem equationTracked_start {request : Request} (admitted : Admitted request)
    (source : Pattern) (job : GeneralEquationJobs.Job) (within : source ∈ request.universe) :
    EquationTracked request (start request) source job := by
  have checked := Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_complete admitted.rootSorted
  left
  refine ⟨.universe, ?_, within⟩
  simp [start, checked]

theorem equationTracked_tick (request : Request) (state : State request) (source : Pattern)
    (job : GeneralEquationJobs.Job)
    (member : job ∈ GeneralEquationJobs.jobs request.plan request.bound request.expected source)
    (tracked : EquationTracked request state source job) :
    EquationTracked request (tick request state) source job := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using tracked
  | cons task remaining =>
      rcases tracked with ⟨promised, pending, promise⟩ | ⟨archive, archived, same⟩
      · rw [agenda, List.mem_cons] at pending
        rcases pending with selected | later
        · subst promised
          cases task with
          | «universe» =>
              left
              refine ⟨.scanUniverse request.universe, ?_, promise⟩
              simp [tick, agenda, expand]
          | scanUniverse patterns =>
              cases patterns with
              | nil => simp only [EquationPromise, List.not_mem_nil] at promise
              | cons head tail =>
                  simp only [EquationPromise, List.mem_cons] at promise
                  left
                  rcases promise with same | later
                  · subst head
                    obtain ⟨next, present, promised⟩ := equationTasks_promise request source job member
                    refine ⟨next, ?_, promised⟩
                    simp only [tick, agenda, expand, List.mem_append]
                    exact Or.inl (Or.inl present)
                  · refine ⟨.scanUniverse tail, ?_, later⟩
                    simp [tick, agenda, expand]
          | equation frame =>
              cases found : frame.state.answers[frame.cursor]? with
              | none =>
                  by_cases closed : GeneralEquationJobExecution.settled frame.state = true
                  · right
                    refine ⟨⟨frame, closed, found⟩, ?_, promise⟩
                    simp only [tick, agenda, expand, expandEquation]
                    split
                    · split
                      · simp
                      · contradiction
                    · rename_i other value
                      rw [found] at value
                      cases value
                  · left
                    refine ⟨.equation {frame with
                      state := GeneralEquationJobExecution.tick (equationRequest request frame.source frame.job) frame.state
                      reachable := .tick frame.reachable}, ?_, promise⟩
                    simp only [tick, agenda, expand, expandEquation]
                    split
                    · split
                      · contradiction
                      · simp
                    · rename_i other value
                      rw [found] at value
                      cases value
              | some answer =>
                  left
                  refine ⟨.equation {frame with cursor := frame.cursor + 1}, ?_, promise⟩
                  simp only [tick, agenda, expand, expandEquation]
                  split
                  · rename_i value
                    rw [found] at value
                    cases value
                  · rename_i other value
                    have same := Option.some.inj (found.symm.trans value)
                    subst other
                    simp
          | visit _ => exact False.elim promise
          | incoming _ _ => exact False.elim promise
          | rule _ => exact False.elim promise
        · left
          exact ⟨promised, by simp only [tick, agenda, List.mem_append]; exact Or.inr later, promise⟩
      · right
        exact ⟨archive, by simp only [tick, agenda, List.mem_append]; exact Or.inl archived, same⟩

theorem reachable_equationTracked {request : Request} (admitted : Admitted request)
    {state : State request} (reached : Reachable request state)
    (source : Pattern) (job : GeneralEquationJobs.Job) (within : source ∈ request.universe)
    (member : job ∈ GeneralEquationJobs.jobs request.plan request.bound request.expected source) :
    EquationTracked request state source job := by
  induction reached with
  | start => exact equationTracked_start admitted source job within
  | tick reached ih => exact equationTracked_tick request _ source job member ih

theorem settled_equation_archived {request : Request} (admitted : Admitted request)
    {state : State request} (reached : Reachable request state) (idle : state.agenda = [])
    (source : Pattern) (job : GeneralEquationJobs.Job) (within : source ∈ request.universe)
    (member : job ∈ GeneralEquationJobs.jobs request.plan request.bound request.expected source) :
    ∃ archive ∈ state.checkedEquations,
      archive.frame.source = source ∧ equationJob archive.frame.job = equationJob job := by
  have tracked := reachable_equationTracked admitted reached source job within member
  rcases tracked with ⟨task, impossible, _⟩ | archived
  · simp only [idle, List.not_mem_nil] at impossible
  · exact archived

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
