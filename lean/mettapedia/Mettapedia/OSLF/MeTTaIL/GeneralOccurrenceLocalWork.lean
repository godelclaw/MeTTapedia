import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobFiniteWork

/-!
# Local work for genuinely equation-free occurrence frontiers

All licensed typed sites and rule declarations are traversed by the existing
matcher and ordered premise machines. Local execution has no ambient-universe
task. Its effective work account is constructed from the actual rule-job
expansion forests and answer-delivery cursors.

Ordinary budgeted execution does not construct its future expansion forest.
The separate work-bound function computes an exhaustive budget when requested.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier.LocalEquationFree

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open GeneralPremise.Scheduler (TaskTree TaskForest)

def rootRepresentative (request : Request) : Representative request :=
  ⟨request.root, [], .nil _⟩

def sourceChecked (request : Request) : Bool :=
  checkOpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free
    request.bound request.expected request.root

/-- The coverage flag is set only when the compiled equation generators are
empty. Other profiles keep equation coverage unresolved. -/
def start (request : Request) : State request :=
  let obligations := request.plan.obligations.map Obligation.admission
  if sourceChecked request then
    {agenda := [.visit (rootRepresentative request)]
     unresolved := obligations
     universeScanned := request.plan.equations.isEmpty}
  else {unresolved := obligations ++ [.sourceRejected]}

def run (request : Request) (budget : Nat) : State request :=
  GeneralOccurrenceFrontier.run request budget (start request)

theorem run_resume (request : Request) (first second : Nat) :
    run request (first + second) =
      GeneralOccurrenceFrontier.run request second (run request first) :=
  GeneralOccurrenceFrontier.run_add request first second (start request)

theorem receipts_prefix (request : Request) (first second : Nat) :
    GeneralPremise.Scheduler.Prefix (run request first).answers
      (run request (first + second)).answers := by
  rw [run_resume]
  exact GeneralOccurrenceFrontier.answers_prefix request second _

def localExpansion (request : Request) : Task request →
    GeneralPremise.Scheduler.Expansion (Task request) (Answer request) Obligation
  | .rule frame =>
      let next := expandRule request frame
      {tasks := next.tasks, answers := next.answers, unresolved := next.unresolved}
  | _ => {}

inductive LocalTask (request : Request) : Task request → Prop where
  | rule (frame : RuleFrame request) : LocalTask request (.rule frame)
  | incoming (representative : Representative request) :
      LocalTask request (.incoming representative [])

def LocalAgenda (request : Request) (tasks : List (Task request)) : Prop :=
  ∀ task ∈ tasks, LocalTask request task

theorem local_expansion (request : Request) (state : State request) (task : Task request)
    (restricted : LocalTask request task) :
    (expand request state task).tasks = (localExpansion request task).tasks := by
  cases restricted <;> rfl

theorem local_next (request : Request) (task : Task request) (restricted : LocalTask request task) :
    LocalAgenda request (localExpansion request task).tasks := by
  cases restricted with
  | incoming representative => intro next member; simp [localExpansion] at member
  | rule frame =>
      change LocalAgenda request (expandRule request frame).tasks
      unfold expandRule
      split
      · split
        · intro next member; simp at member
        · intro next member
          simp only [List.mem_singleton] at member
          subst next
          exact .rule _
      · intro next member
        simp only [List.mem_singleton] at member
        subst next
        exact .rule _

theorem tick_local (request : Request) (state : State request)
    (restricted : LocalAgenda request state.agenda) : LocalAgenda request (tick request state).agenda := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using restricted
  | cons task rest =>
      intro next member
      have first := restricted task (by simp [agenda])
      simp only [tick, agenda, List.mem_append] at member
      rcases member with generated | later
      · rw [local_expansion request state task first] at generated
        exact local_next request task first next generated
      · exact restricted next (by rw [agenda]; exact List.mem_cons_of_mem _ later)

theorem tick_agenda (request : Request) (state : State request)
    (restricted : LocalAgenda request state.agenda) :
    (tick request state).agenda = GeneralPremise.Scheduler.advanceTasks (localExpansion request) state.agenda := by
  cases agenda : state.agenda with
  | nil => simp only [tick, agenda, GeneralPremise.Scheduler.advanceTasks]
  | cons task rest =>
      simp only [tick, agenda, GeneralPremise.Scheduler.advanceTasks]
      rw [local_expansion request state task (restricted task (by simp [agenda]))]

/-- Each outer rule frame advances the actual inner machine and then publishes
every answer in cursor order before archiving the drained job. -/
def ruleTree (request : Request) (frame : RuleFrame request)
    (forest : TaskForest (GeneralRuleJobExecution.expand
      (ruleRequest request frame.representative frame.job)) frame.state.agenda) :
    TaskTree (localExpansion request) (.rule frame) := by
  apply TaskTree.branch
  simp only [localExpansion, expandRule]
  split
  · split
    · exact .nil
    · rename_i pending
      have nonempty : frame.state.agenda ≠ [] := by
        intro empty
        change ¬ frame.state.agenda.isEmpty = true at pending
        rw [empty] at pending
        exact pending rfl
      have decreased : (forest.advance frame.state).cost < forest.cost := by
        have equality := forest.advance_cost frame.state nonempty
        omega
      exact .cons (ruleTree request {frame with
          state := GeneralRuleJobExecution.tick (ruleRequest request frame.representative frame.job) frame.state
          reachable := .tick frame.reachable} (forest.advance frame.state)) .nil
  · rename_i answer found
    have within := (List.getElem?_eq_some_iff.mp found).1
    have decreased : frame.state.answers.length - (frame.cursor + 1) <
        frame.state.answers.length - frame.cursor := by omega
    exact .cons (ruleTree request {frame with cursor := frame.cursor + 1} forest) .nil
termination_by (forest.cost, frame.state.answers.length - frame.cursor)
decreasing_by
  all_goals simp only [Prod.lex_def]
  · exact Or.inl decreased
  · exact Or.inr ⟨trivial, decreased⟩

def mappedForest (request : Request) {A : Type} (items : List A) (task : A → Task request)
    (tree : ∀ item, TaskTree (localExpansion request) (task item)) :
    TaskForest (localExpansion request) (items.map task) :=
  match items with
  | [] => .nil
  | item :: rest => .cons (tree item) (mappedForest request rest task tree)

def initialFrame (request : Request) (representative : Representative request)
    (item : {job // job ∈ GeneralRuleJobs.jobs request.plan request.bound request.expected representative.pattern}) :
    RuleFrame request :=
  let licensed := (GeneralRuleJobs.jobs_spec _ _ _ _ _).mp item.property
  ⟨representative, item.val, licensed,
    GeneralRuleJobExecution.start (ruleRequest request representative item.val) licensed, .start, 0⟩

def ruleForest (request : Request) (representative : Representative request) :
    TaskForest (localExpansion request) (ruleTasks request representative) := by
  change TaskForest (localExpansion request)
    ((GeneralRuleJobs.jobs request.plan request.bound request.expected representative.pattern).attach.map
      (fun item => Task.rule (initialFrame request representative item)))
  exact mappedForest request _ _ (fun item => ruleTree request (initialFrame request representative item)
    (GeneralRuleJobExecution.startForest (ruleRequest request representative item.val)
      ((GeneralRuleJobs.jobs_spec _ _ _ _ _).mp item.property)))

def remainingForest (request : Request) :
    TaskForest (localExpansion request)
      (ruleTasks request (rootRepresentative request) ++ [.incoming (rootRepresentative request) []]) :=
  (ruleForest request (rootRepresentative request)).append
    (.cons (.branch .nil) .nil)

def workBound (request : Request) : Nat :=
  if sourceChecked request then (remainingForest request).cost + 1 else 0

def advanceForest (request : Request) (state : State request)
    (restricted : LocalAgenda request state.agenda)
    (forest : TaskForest (localExpansion request) state.agenda) :
    TaskForest (localExpansion request) (tick request state).agenda :=
  (tick_agenda request state restricted).symm ▸ forest.advanceAgenda

theorem advanceForest_cost (request : Request) (state : State request)
    (restricted : LocalAgenda request state.agenda)
    (forest : TaskForest (localExpansion request) state.agenda) (pending : state.agenda ≠ []) :
    (advanceForest request state restricted forest).cost + 1 = forest.cost := by
  simp only [advanceForest, TaskForest.cost_cast]
  exact forest.advanceAgenda_cost pending

theorem run_idle (request : Request) (fuel : Nat) (state : State request) (idle : state.agenda = []) :
    GeneralOccurrenceFrontier.run request fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [GeneralOccurrenceFrontier.run, tick, idle] using ih

theorem forest_positive {request : Request} {tasks : List (Task request)}
    (forest : TaskForest (localExpansion request) tasks) (pending : tasks ≠ []) :
    0 < forest.cost := by
  cases forest with
  | nil => exact False.elim (pending rfl)
  | cons head tail =>
      cases head
      simp only [TaskForest.cost, TaskTree.cost]
      omega

theorem finite_work_drains (request : Request) (fuel : Nat) (state : State request)
    (restricted : LocalAgenda request state.agenda)
    (forest : TaskForest (localExpansion request) state.agenda) (enough : forest.cost ≤ fuel) :
    (GeneralOccurrenceFrontier.run request fuel state).agenda = [] := by
  induction fuel generalizing state with
  | zero =>
      change state.agenda = []
      by_contra pending
      have positive := forest_positive forest pending
      omega
  | succ fuel ih =>
      by_cases idle : state.agenda = []
      · rw [run_idle request (fuel + 1) state idle]
        exact idle
      · have decreased := advanceForest_cost request state restricted forest idle
        exact ih (tick request state) (tick_local request state restricted)
          (advanceForest request state restricted forest) (by omega)

theorem equationTasks_empty {request : Request} (empty : request.plan.equations = []) (source : Pattern) :
    equationTasks request source = [] := by
  have jobsEmpty : GeneralEquationJobs.jobs request.plan request.bound request.expected source = [] := by
    unfold GeneralEquationJobs.jobs
    rw [empty]
    rfl
  unfold equationTasks
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro task member
  obtain ⟨item, _, _⟩ := List.mem_map.mp member
  rcases item with ⟨job, present⟩
  rw [jobsEmpty] at present
  exact List.not_mem_nil present

theorem first_tick_agenda {request : Request} (empty : request.plan.equations = [])
    (checked : sourceChecked request = true) :
    (tick request (start request)).agenda =
      ruleTasks request (rootRepresentative request) ++ [.incoming (rootRepresentative request) []] := by
  simp only [start, checked, if_true, tick, expand, List.map_nil, List.contains_nil,
    Bool.false_eq_true, if_false, equationTasks_empty empty, List.append_nil]

theorem ruleTasks_local (request : Request) (representative : Representative request) :
    LocalAgenda request (ruleTasks request representative) := by
  intro task member
  obtain ⟨item, _, same⟩ := List.mem_map.mp member
  subst task
  exact .rule _

theorem first_tick_local {request : Request} (empty : request.plan.equations = [])
    (checked : sourceChecked request = true) : LocalAgenda request (tick request (start request)).agenda := by
  rw [first_tick_agenda empty checked]
  intro task member
  rcases List.mem_append.mp member with rule | incoming
  · exact ruleTasks_local request _ task rule
  · simp only [List.mem_singleton] at incoming
    subst task
    exact .incoming _

/-- The computed budget drains every site, typed matching branch and ordered
premise alternative. It does not enumerate any ambient term universe. -/
theorem workBound_drains {request : Request} (empty : request.plan.equations = []) :
    (run request (workBound request)).agenda = [] := by
  by_cases checked : sourceChecked request = true
  · unfold run workBound
    rw [if_pos checked, GeneralOccurrenceFrontier.run]
    let forest : TaskForest (localExpansion request) (tick request (start request)).agenda :=
      (first_tick_agenda empty checked).symm ▸ remainingForest request
    apply finite_work_drains request _ _ (first_tick_local empty checked) forest
    simp only [forest, TaskForest.cost_cast]
    exact Nat.le_refl _
  · unfold run workBound
    rw [if_neg checked]
    simp only [GeneralOccurrenceFrontier.run, start, if_neg checked]

theorem run_stable {request : Request} (empty : request.plan.equations = [])
    (budget : Nat) (enough : workBound request ≤ budget) :
    run request budget = run request (workBound request) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
  rw [run_resume]
  exact run_idle request extra _ (workBound_drains empty)

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier.LocalEquationFree
