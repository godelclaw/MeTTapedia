import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceCertificate
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceStepReadouts
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobCoverage

/-!
# Retained rule jobs and published occurrence receipts

Every generated rule job at a visited representative remains active or archived.
The outer cursor publishes the complete consumed prefix of actual rule answers,
including their primitive origins and the retained conversion history. An empty
agenda therefore has an archive for every generated job and publishes its entire
earned finite readout.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

open GeneralPremise.Scheduler GeneralOccurrenceKeys

def publishRuleAnswer (request : Request) (frame : RuleFrame request)
    (answer : GeneralRuleJobExecution.Answer (ruleRequest request frame.representative frame.job)) : Answer request :=
  ⟨⟨frame.representative.pattern, frame.representative.conversions, answer.val⟩,
    frame.representative.justified, answer.property⟩

def RuleTracked (request : Request) (state : State request) (frame : RuleFrame request) : Prop :=
  .rule frame ∈ state.agenda ∨ ∃ archive ∈ state.checkedRules, archive.frame = frame

def RuleCoverage (request : Request) (state : State request) : Prop :=
  ∀ representative ∈ state.visited,
    ∀ job ∈ GeneralRuleJobs.jobs request.plan request.bound request.expected representative.pattern,
      ∃ frame, frame.representative = representative ∧ frame.job = job ∧ RuleTracked request state frame

def RuleCursorPublished (request : Request) (answers : List (Answer request))
    (frame : RuleFrame request) : Prop :=
  frame.cursor ≤ frame.state.answers.length ∧
    ∀ answer ∈ frame.state.answers.take frame.cursor, publishRuleAnswer request frame answer ∈ answers

def RulePublication (request : Request) (state : State request) : Prop :=
  ∀ frame, RuleTracked request state frame → RuleCursorPublished request state.answers frame

theorem prefix_mem {A : Type} {first second : List A} (earlier : Prefix first second)
    {item : A} (member : item ∈ first) : item ∈ second := by
  obtain ⟨tail, rfl⟩ := earlier
  exact List.mem_append_left _ member

theorem tick_visited_prefix (request : Request) (state : State request) :
    Prefix state.visited (tick request state).visited := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using Prefix.refl state.visited
  | cons task remaining => exact ⟨(expand request state task).visits, by simp only [tick, agenda]⟩

theorem visited_prefix (request : Request) (fuel : Nat) (state : State request) :
    Prefix state.visited (run request fuel state).visited := by
  induction fuel generalizing state with
  | zero => exact .refl _
  | succ fuel ih => exact (tick_visited_prefix request state).trans (ih (tick request state))

theorem tick_checkedRules_prefix (request : Request) (state : State request) :
    Prefix state.checkedRules (tick request state).checkedRules := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using Prefix.refl state.checkedRules
  | cons task remaining => exact ⟨(expand request state task).checkedRules, by simp only [tick, agenda]⟩

theorem checkedRules_prefix (request : Request) (fuel : Nat) (state : State request) :
    Prefix state.checkedRules (run request fuel state).checkedRules := by
  induction fuel generalizing state with
  | zero => exact .refl _
  | succ fuel ih => exact (tick_checkedRules_prefix request state).trans (ih (tick request state))

theorem RuleCursorPublished.mono {request : Request} {first second : List (Answer request)}
    {frame : RuleFrame request} (read : RuleCursorPublished request first frame)
    (inclusion : ∀ answer ∈ first, answer ∈ second) : RuleCursorPublished request second frame :=
  ⟨read.1, fun answer member => inclusion _ (read.2 answer member)⟩

theorem RuleCursorPublished.start (request : Request) (answers : List (Answer request))
    (representative : Representative request) (job : GeneralRuleJobs.Job)
    (licensed : job.Valid request.plan request.bound request.expected representative.pattern) :
    RuleCursorPublished request answers
      ⟨representative, job, licensed,
        GeneralRuleJobExecution.start (ruleRequest request representative job) licensed, .start, 0⟩ := by
  constructor
  · exact Nat.zero_le _
  · intro answer member
    simp only [List.take_zero, List.not_mem_nil] at member

theorem RuleCursorPublished.inner_tick {request : Request} {answers : List (Answer request)}
    {frame : RuleFrame request} (read : RuleCursorPublished request answers frame) :
    RuleCursorPublished request answers {frame with
      state := GeneralRuleJobExecution.tick (ruleRequest request frame.representative frame.job) frame.state
      reachable := .tick frame.reachable} := by
  obtain ⟨tail, same⟩ := GeneralPremise.Scheduler.tick_answers_prefix
    (GeneralRuleJobExecution.expand (ruleRequest request frame.representative frame.job)) frame.state
  have bound := read.1
  constructor
  · change frame.cursor ≤ (GeneralPremise.Scheduler.tick _ frame.state).answers.length
    rw [same, List.length_append]
    omega
  · intro answer member
    change answer ∈ (GeneralPremise.Scheduler.tick _ frame.state).answers.take frame.cursor at member
    rw [same, List.take_append_of_le_length read.1] at member
    exact read.2 answer member

theorem RuleCursorPublished.deliver {request : Request} {first second : List (Answer request)}
    {frame : RuleFrame request} (read : RuleCursorPublished request first frame)
    (inclusion : ∀ answer ∈ first, answer ∈ second)
    (answer : GeneralRuleJobExecution.Answer (ruleRequest request frame.representative frame.job))
    (found : frame.state.answers[frame.cursor]? = some answer)
    (published : publishRuleAnswer request frame answer ∈ second) :
    RuleCursorPublished request second {frame with cursor := frame.cursor + 1} := by
  constructor
  · exact (List.getElem?_eq_some_iff.mp found).1
  · intro next member
    change next ∈ frame.state.answers.take (frame.cursor + 1) at member
    rw [List.take_add_one, found] at member
    simp only [Option.toList_some, List.mem_append, List.mem_singleton] at member
    rcases member with prior | same
    · exact inclusion _ (read.2 next prior)
    · subst next
      exact published

theorem ruleTasks_frame (request : Request) (representative : Representative request)
    (job : GeneralRuleJobs.Job)
    (member : job ∈ GeneralRuleJobs.jobs request.plan request.bound request.expected representative.pattern) :
    ∃ frame, frame.representative = representative ∧ frame.job = job ∧ .rule frame ∈ ruleTasks request representative := by
  let item : {job // job ∈ GeneralRuleJobs.jobs request.plan request.bound request.expected representative.pattern} :=
    ⟨job, member⟩
  refine ⟨⟨representative, job, (GeneralRuleJobs.jobs_spec _ _ _ _ _).mp member,
    GeneralRuleJobExecution.start (ruleRequest request representative job)
      ((GeneralRuleJobs.jobs_spec _ _ _ _ _).mp member), .start, 0⟩, rfl, rfl, ?_⟩
  exact List.mem_map.mpr ⟨item, List.mem_attach _ _, rfl⟩

theorem ruleTracked_tick (request : Request) (state : State request) (frame : RuleFrame request)
    (tracked : RuleTracked request state frame) :
    ∃ next, next.representative = frame.representative ∧ next.job = frame.job ∧
      RuleTracked request (tick request state) next := by
  cases agenda : state.agenda with
  | nil => exact ⟨frame, rfl, rfl, by simpa only [tick, agenda] using tracked⟩
  | cons task remaining =>
      rcases tracked with active | ⟨archive, archived, same⟩
      · rw [agenda, List.mem_cons] at active
        rcases active with selected | later
        · subst task
          cases found : frame.state.answers[frame.cursor]? with
          | none =>
              by_cases closed : GeneralRuleJobExecution.settled frame.state = true
              · refine ⟨frame, rfl, rfl, Or.inr ⟨⟨frame, closed, found⟩, ?_, rfl⟩⟩
                simp only [tick, agenda, expand, expandRule_closed request frame found closed,
                  List.mem_append, List.mem_singleton]
                exact Or.inr trivial
              · refine ⟨{frame with
                    state := GeneralRuleJobExecution.tick (ruleRequest request frame.representative frame.job) frame.state
                    reachable := .tick frame.reachable}, rfl, rfl, Or.inl ?_⟩
                simp only [tick, agenda, expand, expandRule_pending request frame found closed,
                  List.mem_append, List.mem_singleton]
                exact Or.inl trivial
          | some answer =>
              refine ⟨{frame with cursor := frame.cursor + 1}, rfl, rfl, Or.inl ?_⟩
              simp only [tick, agenda, expand, expandRule_found request frame answer found,
                List.mem_append, List.mem_singleton]
              exact Or.inl trivial
        · refine ⟨frame, rfl, rfl, Or.inl ?_⟩
          simp only [tick, agenda, List.mem_append]
          exact Or.inr later
      · refine ⟨frame, rfl, rfl, Or.inr ⟨archive, ?_, same⟩⟩
        exact prefix_mem (tick_checkedRules_prefix request state) archived

theorem expandEquation_visits (request : Request) (state : State request) (frame : EquationFrame request) :
    (expandEquation request state frame).visits = [] := by
  unfold expandEquation
  split
  · split <;> rfl
  · rfl

theorem expandRule_visits (request : Request) (frame : RuleFrame request) :
    (expandRule request frame).visits = [] := by
  unfold expandRule
  split
  · split <;> rfl
  · rfl

theorem expansion_visit_jobs (request : Request) (state : State request) (task : Task request)
    (representative : Representative request) (visited : representative ∈ (expand request state task).visits)
    (job : GeneralRuleJobs.Job)
    (member : job ∈ GeneralRuleJobs.jobs request.plan request.bound request.expected representative.pattern) :
    ∃ frame, frame.representative = representative ∧ frame.job = job ∧
      .rule frame ∈ (expand request state task).tasks := by
  cases task with
  | visit candidate =>
      simp only [expand] at visited ⊢
      split at visited
      · simp only [List.not_mem_nil] at visited
      · rename_i fresh
        simp only [List.mem_singleton] at visited
        subst candidate
        rw [if_neg fresh]
        obtain ⟨frame, same, jobSame, active⟩ := ruleTasks_frame request representative job member
        exact ⟨frame, same, jobSame, by simp only [List.mem_append]; exact Or.inl (Or.inl active)⟩
  | incoming candidate edges =>
      cases edges with
      | nil => simp only [expand, List.not_mem_nil] at visited
      | cons edge remaining =>
          simp only [expand] at visited
          split at visited
          · simp only [List.not_mem_nil] at visited
          · split at visited <;> simp only [List.not_mem_nil] at visited
  | «universe» => simp only [expand, List.not_mem_nil] at visited
  | scanUniverse patterns => cases patterns <;> simp only [expand, List.not_mem_nil] at visited
  | equation frame => simp only [expand, expandEquation_visits, List.not_mem_nil] at visited
  | rule frame => simp only [expand, expandRule_visits, List.not_mem_nil] at visited

theorem ruleCoverage_start (request : Request) : RuleCoverage request (start request) := by
  intro representative visited
  unfold start at visited
  split at visited <;> simp only [List.not_mem_nil] at visited

theorem ruleCoverage_tick (request : Request) (state : State request)
    (coverage : RuleCoverage request state) : RuleCoverage request (tick request state) := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using coverage
  | cons task remaining =>
      intro representative visited job member
      simp only [tick, agenda, List.mem_append] at visited
      rcases visited with old | new
      · obtain ⟨frame, same, jobSame, tracked⟩ := coverage representative old job member
        obtain ⟨next, kept, jobKept, nextTracked⟩ := ruleTracked_tick request state frame tracked
        exact ⟨next, kept.trans same, jobKept.trans jobSame, nextTracked⟩
      · obtain ⟨frame, same, jobSame, active⟩ := expansion_visit_jobs request state task representative new job member
        refine ⟨frame, same, jobSame, Or.inl ?_⟩
        simp only [tick, agenda, List.mem_append]
        exact Or.inl active

theorem reachable_ruleCoverage {request : Request} {state : State request}
    (reached : Reachable request state) : RuleCoverage request state := by
  induction reached with
  | start => exact ruleCoverage_start request
  | tick reached ih => exact ruleCoverage_tick request _ ih

theorem settled_rule_archived {request : Request} {state : State request}
    (reached : Reachable request state) (idle : state.agenda = [])
    (representative : Representative request) (visited : representative ∈ state.visited)
    (job : GeneralRuleJobs.Job)
    (member : job ∈ GeneralRuleJobs.jobs request.plan request.bound request.expected representative.pattern) :
    ∃ archive ∈ state.checkedRules, archive.frame.representative = representative ∧ archive.frame.job = job := by
  obtain ⟨frame, same, jobSame, tracked⟩ := reachable_ruleCoverage reached representative visited job member
  rcases tracked with active | ⟨archive, archived, exactFrame⟩
  · simp only [idle, List.not_mem_nil] at active
  · exact ⟨archive, archived, exactFrame ▸ same, exactFrame ▸ jobSame⟩

theorem equationTasks_no_rule (request : Request) (source : Syntax.Pattern) (frame : RuleFrame request) :
    .rule frame ∉ equationTasks request source := by
  intro member
  obtain ⟨item, _, same⟩ := List.mem_map.mp member
  cases same

theorem edgeDiscoveries_no_rule (request : Request) (state : State request)
    (edge : Edge request) (frame : RuleFrame request) : .rule frame ∉ edgeDiscoveries request state edge := by
  cases source : visitedAt request state edge.source <;>
    cases target : visitedAt request state edge.receipt.target <;>
    simp [edgeDiscoveries, source, target]

theorem expandEquation_no_rule (request : Request) (state : State request)
    (equation : EquationFrame request) (frame : RuleFrame request) :
    .rule frame ∉ (expandEquation request state equation).tasks := by
  cases found : equation.state.answers[equation.cursor]? with
  | none =>
      by_cases closed : GeneralEquationJobExecution.settled equation.state = true
      · rw [expandEquation_closed request state equation found closed]
        simp
      · rw [expandEquation_pending request state equation found closed]
        simp
  | some answer =>
      rw [expandEquation_found request state equation answer found]
      intro member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with discovery | impossible
      · exact edgeDiscoveries_no_rule request state _ frame discovery
      · cases impossible

theorem expandEquation_checkedRules (request : Request) (state : State request)
    (frame : EquationFrame request) : (expandEquation request state frame).checkedRules = [] := by
  unfold expandEquation
  split
  · split <;> rfl
  · rfl

theorem ruleTasks_published (request : Request) (answers : List (Answer request))
    (representative : Representative request) (frame : RuleFrame request)
    (member : .rule frame ∈ ruleTasks request representative) : RuleCursorPublished request answers frame := by
  obtain ⟨item, _, same⟩ := List.mem_map.mp member
  have sameFrame := Task.rule.inj same
  cases sameFrame
  exact RuleCursorPublished.start request answers _ _ _

def RuleExpansionPublished (request : Request) (answers : List (Answer request))
    (next : Expansion request) : Prop :=
  (∀ frame, .rule frame ∈ next.tasks → RuleCursorPublished request (answers ++ next.answers) frame) ∧
    ∀ archive ∈ next.checkedRules, RuleCursorPublished request (answers ++ next.answers) archive.frame

theorem expandRule_published (request : Request) (answers : List (Answer request))
    (frame : RuleFrame request) (read : RuleCursorPublished request answers frame) :
    RuleExpansionPublished request answers (expandRule request frame) := by
  cases found : frame.state.answers[frame.cursor]? with
  | none =>
      by_cases closed : GeneralRuleJobExecution.settled frame.state = true
      · rw [expandRule_closed request frame found closed]
        constructor
        · intro next member
          simp only [List.not_mem_nil] at member
        · intro archive member
          simp only [List.mem_singleton] at member
          subst archive
          simpa only [List.append_nil] using read
      · rw [expandRule_pending request frame found closed]
        constructor
        · intro next member
          simp only [List.mem_singleton, Task.rule.injEq] at member
          subst next
          simpa only [List.append_nil] using read.inner_tick
        · intro archive member
          simp only [List.not_mem_nil] at member
  | some answer =>
      rw [expandRule_found request frame answer found]
      constructor
      · intro next member
        simp only [List.mem_singleton, Task.rule.injEq] at member
        subst next
        apply read.deliver (fun _ member => List.mem_append_left _ member) answer found
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      · intro archive member
        simp only [List.not_mem_nil] at member

theorem expansion_rule_published (request : Request) (state : State request) (task : Task request)
    (pending : task ∈ state.agenda) (publication : RulePublication request state) :
    RuleExpansionPublished request state.answers (expand request state task) := by
  cases task with
  | visit representative =>
      simp only [expand]
      split
      · constructor
        · intro frame member
          simp only [List.not_mem_nil] at member
        · intro archive member
          simp only [List.not_mem_nil] at member
      · constructor
        · intro frame member
          simp only [List.mem_append, List.mem_singleton] at member
          rcases member with (ruleMember | equationMember) | incoming
          · exact ruleTasks_published request _ representative frame ruleMember
          · exact False.elim (equationTasks_no_rule request _ frame equationMember)
          · cases incoming
        · intro archive member
          simp only [List.not_mem_nil] at member
  | incoming representative edges =>
      cases edges with
      | nil =>
          constructor
          · intro frame member
            simp only [expand, List.not_mem_nil] at member
          · intro archive member
            simp only [expand, List.not_mem_nil] at member
      | cons edge remaining =>
          simp only [expand]
          split
          · constructor <;> intro value member <;> simp at member
          · split <;> constructor <;> intro value member <;> simp at member
  | «universe» =>
      constructor <;> intro value member <;> simp [expand] at member
  | scanUniverse patterns =>
      cases patterns with
      | nil => constructor <;> intro value member <;> simp [expand] at member
      | cons source remaining =>
          constructor
          · intro frame member
            simp only [expand, List.mem_append, List.mem_singleton] at member
            rcases member with equationMember | scanning
            · exact False.elim (equationTasks_no_rule request source frame equationMember)
            · cases scanning
          · intro archive member
            simp only [expand, List.not_mem_nil] at member
  | equation frame =>
      constructor
      · intro next member
        exact False.elim (expandEquation_no_rule request state frame next member)
      · intro archive member
        simp only [expand, expandEquation_checkedRules, List.not_mem_nil] at member
  | rule frame =>
      exact expandRule_published request state.answers frame (publication frame (Or.inl pending))

theorem rulePublication_start (request : Request) : RulePublication request (start request) := by
  intro frame tracked
  unfold RuleTracked start at tracked
  split at tracked <;> simp at tracked

theorem rulePublication_tick (request : Request) (state : State request)
    (publication : RulePublication request state) : RulePublication request (tick request state) := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using publication
  | cons task remaining =>
      have expansion := expansion_rule_published request state task (by simp [agenda]) publication
      intro frame tracked
      rcases tracked with active | ⟨archive, archived, same⟩
      · simp only [tick, agenda, List.mem_append] at active
        rcases active with generated | later
        · simpa only [tick, agenda] using expansion.1 frame generated
        · apply (publication frame (Or.inl (by rw [agenda]; exact List.mem_cons_of_mem _ later))).mono
          exact fun _ member => prefix_mem (tick_answers_prefix request state) member
      · simp only [tick, agenda, List.mem_append] at archived
        rcases archived with prior | fresh
        · apply (publication frame (Or.inr ⟨archive, prior, same⟩)).mono
          exact fun _ member => prefix_mem (tick_answers_prefix request state) member
        · rw [← same]
          simpa only [tick, agenda] using expansion.2 archive fresh

theorem reachable_rulePublication {request : Request} {state : State request}
    (reached : Reachable request state) : RulePublication request state := by
  induction reached with
  | start => exact rulePublication_start request
  | tick reached ih => exact rulePublication_tick request _ ih

theorem ruleArchive_answers_published {request : Request} {state : State request}
    (archive : RuleArchive request) (read : RuleCursorPublished request state.answers archive.frame)
    (answer : GeneralRuleJobExecution.Answer (ruleRequest request archive.frame.representative archive.frame.job))
    (member : answer ∈ archive.frame.state.answers) : publishRuleAnswer request archive.frame answer ∈ state.answers := by
  have after := List.getElem?_eq_none_iff.mp archive.readAll
  have bound := read.1
  have same : archive.frame.cursor = archive.frame.state.answers.length := by omega
  apply read.2 answer
  simpa only [same, List.take_length] using member

theorem ruleArchive_read {request : Request} {state : State request}
    (archive : RuleArchive request) (read : RuleCursorPublished request state.answers archive.frame) :
    ruleArchiveRead request state archive = true := by
  apply List.all_eq_true.mpr
  intro answer member
  apply decide_eq_true_eq.mpr
  have published := ruleArchive_answers_published archive read answer member
  exact List.mem_map.mpr ⟨publishRuleAnswer request archive.frame answer, published, rfl⟩

def RuleArchiveUnresolved (request : Request) (state : State request) : Prop :=
  ∀ archive ∈ state.checkedRules, ∀ reason ∈ archive.frame.state.unresolved,
    Obligation.rule reason ∈ state.unresolved

theorem expandRule_archive_unresolved (request : Request) (frame : RuleFrame request)
    (archive : RuleArchive request) (archived : archive ∈ (expandRule request frame).checkedRules)
    (reason : GeneralRuleJobExecution.Obligation) (member : reason ∈ archive.frame.state.unresolved) :
    Obligation.rule reason ∈ (expandRule request frame).unresolved := by
  cases found : frame.state.answers[frame.cursor]? with
  | none =>
      by_cases closed : GeneralRuleJobExecution.settled frame.state = true
      · rw [expandRule_closed request frame found closed] at archived ⊢
        simp only [List.mem_singleton] at archived
        subst archive
        exact List.mem_map.mpr ⟨reason, member, rfl⟩
      · rw [expandRule_pending request frame found closed] at archived
        simp only [List.not_mem_nil] at archived
  | some answer =>
      rw [expandRule_found request frame answer found] at archived
      simp only [List.not_mem_nil] at archived

theorem expansion_rule_archive_unresolved (request : Request) (state : State request) (task : Task request)
    (archive : RuleArchive request) (archived : archive ∈ (expand request state task).checkedRules)
    (reason : GeneralRuleJobExecution.Obligation) (member : reason ∈ archive.frame.state.unresolved) :
    Obligation.rule reason ∈ (expand request state task).unresolved := by
  cases task with
  | visit representative =>
      simp only [expand] at archived
      split at archived <;> simp only [List.not_mem_nil] at archived
  | incoming representative edges =>
      cases edges with
      | nil => simp only [expand, List.not_mem_nil] at archived
      | cons edge remaining =>
          simp only [expand] at archived
          split at archived
          · simp only [List.not_mem_nil] at archived
          · split at archived <;> simp only [List.not_mem_nil] at archived
  | «universe» => simp only [expand, List.not_mem_nil] at archived
  | scanUniverse remaining => cases remaining <;> simp only [expand, List.not_mem_nil] at archived
  | equation frame => simp only [expand, expandEquation_checkedRules, List.not_mem_nil] at archived
  | rule frame => exact expandRule_archive_unresolved request frame archive archived reason member

theorem ruleArchiveUnresolved_start (request : Request) : RuleArchiveUnresolved request (start request) := by
  intro archive archived
  unfold start at archived
  split at archived <;> simp only [List.not_mem_nil] at archived

theorem ruleArchiveUnresolved_tick (request : Request) (state : State request)
    (retained : RuleArchiveUnresolved request state) : RuleArchiveUnresolved request (tick request state) := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using retained
  | cons task remaining =>
      intro archive archived reason member
      simp only [tick, agenda, List.mem_append] at archived ⊢
      rcases archived with prior | fresh
      · exact Or.inl (retained archive prior reason member)
      · exact Or.inr (expansion_rule_archive_unresolved request state task archive fresh reason member)

theorem reachable_ruleArchiveUnresolved {request : Request} {state : State request}
    (reached : Reachable request state) : RuleArchiveUnresolved request state := by
  induction reached with
  | start => exact ruleArchiveUnresolved_start request
  | tick reached ih => exact ruleArchiveUnresolved_tick request _ ih

theorem ruleArchive_complete {request : Request} {state : State request}
    (reached : Reachable request state) (resolved : state.unresolved = [])
    (archive : RuleArchive request) (archived : archive ∈ state.checkedRules) :
    GeneralRuleJobExecution.complete archive.frame.state = true := by
  apply (GeneralRuleJobExecution.complete_iff archive.frame.state).mpr
  refine ⟨List.isEmpty_iff.mp archive.settled, ?_⟩
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro reason member
  have global := reachable_ruleArchiveUnresolved reached archive archived reason member
  simp only [resolved, List.not_mem_nil] at global

theorem completed_ruleJobCertified {request : Request} {state : State request}
    (reached : Reachable request state) (completed : complete request state = true)
    (representative : Representative request) (visited : representative ∈ state.visited)
    (job : GeneralRuleJobs.Job)
    (member : job ∈ GeneralRuleJobs.jobs request.plan request.bound request.expected representative.pattern) :
    RuleJobCertified request state representative job := by
  have facts := (complete_iff request state).mp completed
  obtain ⟨archive, archived, same, jobSame⟩ := settled_rule_archived reached facts.1 representative visited job member
  refine ⟨archive, archived, congrArg Representative.pattern same, congrArg ruleJob jobSame,
    ruleArchive_complete reached facts.2.1 archive archived, ?_⟩
  intro answer emitted
  have read := reachable_rulePublication reached archive.frame (Or.inr ⟨archive, archived, rfl⟩)
  have published := ruleArchive_answers_published archive read answer emitted
  exact List.mem_map.mpr ⟨publishRuleAnswer request archive.frame answer, published, rfl⟩

theorem completed_representedJobsChecked {request : Request} {state : State request}
    (reached : Reachable request state) (completed : complete request state = true) :
    representedJobsChecked request state = true := by
  apply List.all_eq_true.mpr
  intro representative visited
  apply List.all_eq_true.mpr
  intro job member
  exact (ruleJobChecked_iff request state representative job).mpr
    (completed_ruleJobCertified reached completed representative visited job member)

theorem Admitted.rule_stratification {request : Request} (admitted : Admitted request) :
    GeneralPremise.checkStepStratification (GeneralPlanEnvironment.environment request.plan).language = true := by
  have accepted : (GeneralExecutionAdmission.compile request.plan.snapshot request.plan.permissions).complete = true :=
    admitted.compiled ▸ admitted.accepted
  rw [admitted.compiled]
  exact (GeneralExecutionAdmission.complete_snapshot_checks accepted).2.2.2

theorem completed_rule_receipt_published {request : Request} (admitted : Admitted request)
    {state : State request} (reached : Reachable request state) (completed : complete request state = true)
    (representative : Representative request) (visited : representative ∈ state.visited)
    (receipt : GeneralRuleJobs.Receipt)
    (valid : receipt.Valid request.plan request.bound request.expected representative.pattern) :
    ∃ answer ∈ state.answers,
      answer.val = ⟨representative.pattern, representative.conversions, receipt⟩ := by
  have member := (GeneralRuleJobs.jobs_spec request.plan request.bound request.expected
    representative.pattern receipt.job).mpr valid.1
  obtain ⟨archive, archived, same, jobSame⟩ := settled_rule_archived reached
    ((complete_iff request state).mp completed).1 representative visited receipt.job member
  have validAtFrame : receipt.Valid request.plan request.bound request.expected archive.frame.representative.pattern := by
    rw [same]
    exact valid
  obtain ⟨inner, emitted, value⟩ := GeneralRuleJobExecution.finishState_receipt_complete
    (request := ruleRequest request archive.frame.representative archive.frame.job)
    archive.frame.licensed admitted.rule_stratification validAtFrame jobSame.symm
  have final := GeneralRuleJobExecution.settled_reachable_finishState archive.frame.reachable archive.settled
  rw [← final] at emitted
  have read := reachable_rulePublication reached archive.frame (Or.inr ⟨archive, archived, rfl⟩)
  refine ⟨publishRuleAnswer request archive.frame inner,
    ruleArchive_answers_published archive read inner emitted, ?_⟩
  change (⟨archive.frame.representative.pattern, archive.frame.representative.conversions, inner.val⟩ :
    GeneralOccurrenceSemantics.Receipt) = _
  rw [value, same]

#print axioms reachable_ruleCoverage
#print axioms reachable_rulePublication
#print axioms ruleArchive_read
#print axioms reachable_ruleArchiveUnresolved
#print axioms completed_representedJobsChecked
#print axioms completed_rule_receipt_published

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
