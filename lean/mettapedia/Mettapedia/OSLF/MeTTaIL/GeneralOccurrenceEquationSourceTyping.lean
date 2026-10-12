import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceTermination
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceStepReadouts

/-!
# Whole-source typing of equation work

Equation jobs are created only by justified representative visits and the
source-derived typed universe scan. The scheduler preserves the whole-source
typing judgment when it pauses, publishes an answer, or advances a local
equation cursor. Site licensing alone does not establish this judgment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.GeneralFiniteTermUniverse

abbrev EquationSourceTyped (request : Request) (source : Pattern) : Prop :=
  OpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free
    request.bound request.expected source

def TaskSourcesTyped (request : Request) : Task request → Prop
  | .equation frame => EquationSourceTyped request frame.source
  | .scanUniverse remaining => ∀ source ∈ remaining, EquationSourceTyped request source
  | .visit _ | .incoming _ _ | .universe | .rule _ => True

def AgendaSourcesTyped (request : Request) (state : State request) : Prop :=
  ∀ task ∈ state.agenda, TaskSourcesTyped request task

theorem universe_source_typed (request : Request) (source : Pattern)
    (member : source ∈ request.universe) : EquationSourceTyped request source := by
  exact (typedUniverse_sound _ _ _ _ _ _ _ source member).2

theorem Admitted.representative_source_typed {request : Request} (admitted : Admitted request)
    (representative : Representative request) :
    EquationSourceTyped request representative.pattern :=
  universe_source_typed request representative.pattern (admitted.representative_within representative)

theorem equationTasks_sources_typed (request : Request) (source : Pattern)
    (typed : EquationSourceTyped request source) :
    ∀ task ∈ equationTasks request source, TaskSourcesTyped request task := by
  intro task member
  obtain ⟨item, _, same⟩ := List.mem_map.mp member
  subst task
  exact typed

theorem ruleTasks_sources_typed (request : Request) (representative : Representative request) :
    ∀ task ∈ ruleTasks request representative, TaskSourcesTyped request task := by
  intro task member
  obtain ⟨item, _, same⟩ := List.mem_map.mp member
  subst task
  trivial

theorem edgeDiscoveries_sources_typed (request : Request) (state : State request)
    (edge : Edge request) :
    ∀ task ∈ edgeDiscoveries request state edge, TaskSourcesTyped request task := by
  intro task member
  simp only [edgeDiscoveries, List.mem_append] at member
  rcases member with forward | backward
  · cases found : visitedAt request state edge.source with
    | none => simp only [found, List.not_mem_nil] at forward
    | some representative =>
        simp only [found, List.mem_singleton] at forward
        subst task
        trivial
  · cases found : visitedAt request state edge.receipt.target with
    | none => simp only [found, List.not_mem_nil] at backward
    | some representative =>
        simp only [found, List.mem_singleton] at backward
        subst task
        trivial

theorem expandEquation_sources_typed (request : Request) (state : State request)
    (frame : EquationFrame request) (typed : EquationSourceTyped request frame.source) :
    ∀ task ∈ (expandEquation request state frame).tasks, TaskSourcesTyped request task := by
  intro task member
  cases found : frame.state.answers[frame.cursor]? with
  | some answer =>
      rw [expandEquation_found request state frame answer found] at member
      rcases List.mem_append.mp member with discovered | retained
      · exact edgeDiscoveries_sources_typed request state _ task discovered
      · simp only [List.mem_singleton] at retained
        subst task
        exact typed
  | none =>
      by_cases idle : GeneralEquationJobExecution.settled frame.state = true
      · rw [expandEquation_closed request state frame found idle] at member
        exact False.elim (List.not_mem_nil member)
      · rw [expandEquation_pending request state frame found idle] at member
        simp only [List.mem_singleton] at member
        subst task
        exact typed

theorem expandRule_sources_typed (request : Request) (frame : RuleFrame request) :
    ∀ task ∈ (expandRule request frame).tasks, TaskSourcesTyped request task := by
  intro task member
  cases found : frame.state.answers[frame.cursor]? with
  | some answer =>
      rw [expandRule_found request frame answer found] at member
      simp only [List.mem_singleton] at member
      subst task
      trivial
  | none =>
      by_cases idle : GeneralRuleJobExecution.settled frame.state = true
      · rw [expandRule_closed request frame found idle] at member
        exact False.elim (List.not_mem_nil member)
      · rw [expandRule_pending request frame found idle] at member
        simp only [List.mem_singleton] at member
        subst task
        trivial

theorem expansion_sources_typed {request : Request} (admitted : Admitted request)
    (state : State request) (task : Task request) (typed : TaskSourcesTyped request task) :
    ∀ next ∈ (expand request state task).tasks, TaskSourcesTyped request next := by
  intro next member
  cases task with
  | visit representative =>
      by_cases visited : (state.visited.map Representative.pattern).contains representative.pattern = true
      · simp only [expand, visited, if_true, List.not_mem_nil] at member
      · simp only [expand, if_neg visited, List.mem_append, List.mem_singleton] at member
        rcases member with (rule | equation) | incoming
        · exact ruleTasks_sources_typed request representative next rule
        · exact equationTasks_sources_typed request representative.pattern
            (admitted.representative_source_typed representative) next equation
        · subst next
          trivial
  | incoming representative edges =>
      cases edges with
      | nil => exact False.elim (List.not_mem_nil member)
      | cons edge remaining =>
          simp only [expand] at member
          split at member
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with same | same <;> subst next <;> trivial
          · split at member
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with same | same <;> subst next <;> trivial
            · simp only [List.mem_singleton] at member
              subst next
              trivial
  | «universe» =>
      simp only [expand, List.mem_singleton] at member
      subst next
      exact universe_source_typed request
  | scanUniverse remaining =>
      cases remaining with
      | nil => exact False.elim (List.not_mem_nil member)
      | cons source remaining =>
          simp only [expand, List.mem_append, List.mem_singleton] at member
          rcases member with equation | later
          · exact equationTasks_sources_typed request source
              (typed source List.mem_cons_self) next equation
          · subst next
            intro source member
            exact typed source (List.mem_cons_of_mem _ member)
  | equation frame => exact expandEquation_sources_typed request state frame typed next member
  | rule frame => exact expandRule_sources_typed request frame next member

theorem start_sources_typed (request : Request) : AgendaSourcesTyped request (start request) := by
  intro task member
  unfold start at member
  split at member
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same <;> subst task <;> trivial
  · exact False.elim (List.not_mem_nil member)

theorem tick_sources_typed {request : Request} (admitted : Admitted request)
    {state : State request} (typed : AgendaSourcesTyped request state) :
    AgendaSourcesTyped request (tick request state) := by
  intro next member
  cases agenda : state.agenda with
  | nil => exact typed next (by simpa only [tick, agenda] using member)
  | cons task remaining =>
      simp only [tick, agenda, List.mem_append] at member
      rcases member with generated | retained
      · exact expansion_sources_typed admitted state task
          (typed task (agenda ▸ List.mem_cons_self)) next generated
      · exact typed next (agenda ▸ List.mem_cons_of_mem _ retained)

theorem reachable_sources_typed {request : Request} (admitted : Admitted request)
    {state : State request} (reached : Reachable request state) :
    AgendaSourcesTyped request state := by
  induction reached with
  | start => exact start_sources_typed request
  | tick reached ih => exact tick_sources_typed admitted ih

theorem reachable_equation_source_typed {request : Request} (admitted : Admitted request)
    {state : State request} (reached : Reachable request state) (frame : EquationFrame request)
    (member : .equation frame ∈ state.agenda) : EquationSourceTyped request frame.source :=
  reachable_sources_typed admitted reached (.equation frame) member

theorem expansion_archive_source_typed (request : Request) (state : State request)
    (task : Task request) (typed : TaskSourcesTyped request task)
    (archive : EquationArchive request) (member : archive ∈ (expand request state task).checkedEquations) :
    EquationSourceTyped request archive.frame.source := by
  cases task with
  | visit representative =>
      simp only [expand] at member
      split at member <;> exact False.elim (List.not_mem_nil member)
  | incoming representative edges =>
      cases edges with
      | nil => exact False.elim (List.not_mem_nil member)
      | cons edge remaining =>
          simp only [expand] at member
          split at member
          · exact False.elim (List.not_mem_nil member)
          · split at member <;> exact False.elim (List.not_mem_nil member)
  | «universe» => exact False.elim (List.not_mem_nil member)
  | scanUniverse remaining => cases remaining <;> exact False.elim (List.not_mem_nil member)
  | equation frame =>
      cases found : frame.state.answers[frame.cursor]? with
      | some answer =>
          rw [expand, expandEquation_found request state frame answer found] at member
          exact False.elim (List.not_mem_nil member)
      | none =>
          by_cases idle : GeneralEquationJobExecution.settled frame.state = true
          · rw [expand, expandEquation_closed request state frame found idle] at member
            simp only [List.mem_singleton] at member
            subst archive
            exact typed
          · rw [expand, expandEquation_pending request state frame found idle] at member
            exact False.elim (List.not_mem_nil member)
  | rule frame =>
      cases found : frame.state.answers[frame.cursor]? with
      | some answer =>
          rw [expand, expandRule_found request frame answer found] at member
          exact False.elim (List.not_mem_nil member)
      | none =>
          by_cases idle : GeneralRuleJobExecution.settled frame.state = true
          · rw [expand, expandRule_closed request frame found idle] at member
            exact False.elim (List.not_mem_nil member)
          · rw [expand, expandRule_pending request frame found idle] at member
            exact False.elim (List.not_mem_nil member)

theorem reachable_equation_archives_source_typed {request : Request} (admitted : Admitted request)
    {state : State request} (reached : Reachable request state) :
    ∀ archive ∈ state.checkedEquations, EquationSourceTyped request archive.frame.source := by
  induction reached with
  | start =>
      intro archive member
      unfold start at member
      split at member <;> exact False.elim (List.not_mem_nil member)
  | @tick state reached ih =>
      intro archive member
      cases agenda : state.agenda with
      | nil => exact ih archive (by simpa only [tick, agenda] using member)
      | cons task remaining =>
          simp only [tick, agenda, List.mem_append] at member
          rcases member with retained | added
          · exact ih archive retained
          · exact expansion_archive_source_typed request state task
              (reachable_sources_typed admitted reached task (agenda ▸ List.mem_cons_self)) archive added

#print axioms reachable_sources_typed
#print axioms reachable_equation_source_typed
#print axioms reachable_equation_archives_source_typed

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
