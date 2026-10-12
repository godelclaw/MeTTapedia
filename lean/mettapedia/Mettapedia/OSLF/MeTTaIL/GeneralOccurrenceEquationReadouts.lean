import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceEquationArchives
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceStepReadouts

/-!
# Publication of every consumed equation receipt

Active cursor prefixes and drained archives are checked against the actual
global edge ledger. The invariant follows each outer microstep, including
inner pauses and finite-universe scans.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

open GeneralOccurrenceKeys

def EquationTaskRead (request : Request) (state : State request) : Task request → Prop
  | .equation frame => EquationCursorRead request state frame
  | _ => True

def EquationReads (request : Request) (state : State request) : Prop :=
  (∀ task ∈ state.agenda, EquationTaskRead request state task) ∧
    ∀ archive ∈ state.checkedEquations, EquationCursorRead request state archive.frame

theorem EquationTaskRead.mono {request : Request} {first second : State request}
    {task : Task request} (read : EquationTaskRead request first task)
    (inclusion : ∀ key ∈ edgeKeys request first, key ∈ edgeKeys request second) :
    EquationTaskRead request second task := by
  cases task with
  | equation frame => exact EquationCursorRead.mono read inclusion
  | visit _ | incoming _ _ | «universe» | scanUniverse _ | rule _ => trivial

theorem equationTasks_read (request : Request) (state : State request) (source : Syntax.Pattern) :
    ∀ task ∈ equationTasks request source, EquationTaskRead request state task := by
  intro task member
  simp only [equationTasks, List.mem_map] at member
  obtain ⟨item, _, same⟩ := member
  subst task
  exact EquationCursorRead.start request state source item.val _

theorem ruleTasks_equationRead (request : Request) (state : State request)
    (representative : Representative request) :
    ∀ task ∈ ruleTasks request representative, EquationTaskRead request state task := by
  intro task member
  simp only [ruleTasks, List.mem_map] at member
  obtain ⟨item, _, same⟩ := member
  subst task
  trivial

theorem edgeDiscoveries_equationRead (request : Request) (first second : State request) (edge : Edge request) :
    ∀ task ∈ edgeDiscoveries request first edge, EquationTaskRead request second task := by
  intro task member
  simp only [edgeDiscoveries] at member
  split at member <;> split at member
  all_goals simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or] at member
  all_goals rcases member with rfl | rfl <;> trivial

theorem expand_equationTasks_read (request : Request) (state : State request) (task : Task request)
    (remaining : List (Task request)) (agenda : state.agenda = task :: remaining)
    (read : EquationTaskRead request state task) :
    ∀ next ∈ (expand request state task).tasks, EquationTaskRead request (tick request state) next := by
  intro next member
  cases task with
  | visit representative =>
      simp only [expand] at member
      split at member
      · simp only [List.not_mem_nil] at member
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with (rule | equation) | same
        · exact ruleTasks_equationRead request _ representative next rule
        · exact equationTasks_read request _ representative.pattern next equation
        · subst next
          trivial
  | incoming representative edges =>
      cases edges with
      | nil => simp only [expand, List.not_mem_nil] at member
      | cons edge tail =>
          simp only [expand] at member
          repeat' split at member
          all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          all_goals rcases member with rfl | rfl <;> trivial
  | «universe» =>
      simp only [expand, List.mem_cons, List.not_mem_nil, or_false] at member
      subst next
      trivial
  | scanUniverse patterns =>
      cases patterns with
      | nil => simp only [expand, List.not_mem_nil] at member
      | cons source tail =>
          simp only [expand, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with equation | same
          · exact equationTasks_read request _ source next equation
          · subst next
            trivial
  | rule frame =>
      simp only [expand, expandRule] at member
      split at member
      · split at member
        · simp only [List.not_mem_nil] at member
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          subst next
          trivial
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        subst next
        trivial
  | equation frame =>
      cases found : frame.state.answers[frame.cursor]? with
      | none =>
          by_cases closed : GeneralEquationJobExecution.settled frame.state = true
          · rw [expand, expandEquation_closed request state frame found closed] at member
            simp only [List.not_mem_nil] at member
          · rw [expand, expandEquation_pending request state frame found closed] at member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            subst next
            exact EquationCursorRead.mono (EquationCursorRead.inner_tick read) (edgeKeys_tick_mono request state)
      | some answer =>
          rw [expand, expandEquation_found request state frame answer found] at member
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with discovered | same
          · exact edgeDiscoveries_equationRead request state _ _ next discovered
          · subst next
            apply EquationCursorRead.deliver read (edgeKeys_tick_mono request state) answer found
            simp only [edgeKeys, tick, agenda, expand]
            rw [expandEquation_found request state frame answer found]
            simp [edgeKey]

theorem expand_equationArchives_read (request : Request) (state : State request) (task : Task request)
    (read : EquationTaskRead request state task) :
    ∀ archive ∈ (expand request state task).checkedEquations,
      EquationCursorRead request (tick request state) archive.frame := by
  intro archive member
  cases task with
  | visit representative => simp only [expand] at member; split at member <;> simp_all
  | incoming representative edges =>
      cases edges with
      | nil => simp only [expand, List.not_mem_nil] at member
      | cons edge tail =>
          by_cases backward : representative.pattern = edge.receipt.target
          · simp only [expand, dif_pos backward, List.not_mem_nil] at member
          · by_cases forward : representative.pattern = edge.source
            · simp only [expand, dif_neg backward, dif_pos forward, List.not_mem_nil] at member
            · simp only [expand, dif_neg backward, dif_neg forward, List.not_mem_nil] at member
  | «universe» => simp only [expand, List.not_mem_nil] at member
  | scanUniverse patterns => cases patterns <;> simp only [expand, List.not_mem_nil] at member
  | rule frame =>
      simp only [expand, expandRule] at member
      split at member
      · split at member <;> simp_all
      · simp_all
  | equation frame =>
      cases found : frame.state.answers[frame.cursor]? with
      | none =>
          by_cases closed : GeneralEquationJobExecution.settled frame.state = true
          · rw [expand, expandEquation_closed request state frame found closed] at member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            subst archive
            exact EquationCursorRead.mono read (edgeKeys_tick_mono request state)
          · rw [expand, expandEquation_pending request state frame found closed] at member
            simp only [List.not_mem_nil] at member
      | some answer =>
          rw [expand, expandEquation_found request state frame answer found] at member
          simp only [List.not_mem_nil] at member

theorem equationReads_start (request : Request) : EquationReads request (start request) := by
  constructor
  · intro task member
    simp only [start] at member
    split at member
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> trivial
    · simp only [List.not_mem_nil] at member
  · intro archive member
    simp only [start] at member
    split at member <;> simp_all

theorem equationReads_tick {request : Request} {state : State request}
    (read : EquationReads request state) : EquationReads request (tick request state) := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using read
  | cons task remaining =>
      constructor
      · intro next member
        simp only [tick, agenda, List.mem_append] at member
        rcases member with expanded | later
        · exact expand_equationTasks_read request state task remaining agenda
            (read.1 task (by rw [agenda]; exact List.mem_cons_self)) next expanded
        · apply (read.1 next (by rw [agenda]; exact List.mem_cons_of_mem _ later)).mono
          exact edgeKeys_tick_mono request state
      · intro archive member
        simp only [tick, agenda, List.mem_append] at member
        rcases member with prior | added
        · exact EquationCursorRead.mono (read.2 archive prior) (edgeKeys_tick_mono request state)
        · exact expand_equationArchives_read request state task
            (read.1 task (by rw [agenda]; exact List.mem_cons_self)) archive added

theorem reachable_equationReads {request : Request} {state : State request}
    (reached : Reachable request state) : EquationReads request state := by
  induction reached with
  | start => exact equationReads_start request
  | tick reached ih => exact equationReads_tick ih

theorem reachable_equationArchiveRead {request : Request} {state : State request}
    (reached : Reachable request state) (archive : EquationArchive request)
    (member : archive ∈ state.checkedEquations) : equationArchiveRead request state archive = true :=
  equationArchive_read archive ((reachable_equationReads reached).2 archive member)

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
