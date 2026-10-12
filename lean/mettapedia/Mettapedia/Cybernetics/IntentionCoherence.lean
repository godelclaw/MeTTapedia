import Mathlib.Data.Finset.Basic
import Mettapedia.Cybernetics.Individuation

/-!
# Standing intentions and dependency-respecting coordination

Intentions are kept as an indexed family of tasks.  They are not collapsed
into one utility, reward, or phenomenal valence.  A completion event retains
the selected task and its readiness evidence.  Completing a task inserts it
into the completed set; it cannot undo another completed task.

An ordered agenda is compiled into an actual proof-relevant process in the
existing individuation interface.  The compiler establishes continued
opportunities for the standing intentions after every prefix, and every
completion strictly reduces the outstanding task set.  The agenda is finite;
this is a coordination theorem, not an assertion that arbitrary learning
converges or that every intention can jointly be realized.

Explicit announcements are deliberately separate from standing intentions.
The two-task control performs its whole dependency-respecting agenda without
announcing either act.  A reversed agenda and a cyclic dependency exhibit
different ways that an intention set can fail to supply an executable plan.

This is a mathematical reconstruction inspired by Z. Goertzel's *The High
Intentionsality Stage of Development* (2024), especially its distinction
between implicit standing principles and deliberation before each act, and
by D. Weinbaum and V. Veitas, *Open Ended Intelligence: The Individuation of
Intelligent Agents* (2015), arXiv:1505.06366.  It makes no experiential or
moral assignment to task completion.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.IntentionCoherence

open Mettapedia.Cybernetics.Individuation

universe u

/-- A finite declared set of standing intentions with task dependencies. -/
structure Plan (Task : Type u) where
  standing : Finset Task
  predecessors : Task → Finset Task

namespace Plan

variable {Task : Type u} [DecidableEq Task]

/-- Completion is ready when all declared predecessors have completed. -/
def Ready (plan : Plan Task) (completed : Finset Task) (task : Task) : Prop :=
  plan.predecessors task ⊆ completed

omit [DecidableEq Task] in
/-- Positive dependencies remain enabled when the completed set grows. -/
theorem ready_mono (plan : Plan Task) {before after : Finset Task} {task : Task}
    (grows : before ⊆ after) (ready : plan.Ready before task) :
    plan.Ready after task := ready.trans grows

/-- The unfinished standing intentions, retaining their identities. -/
def outstanding (plan : Plan Task) (completed : Finset Task) : Finset Task :=
  plan.standing \ completed

/-- One actual completion, including the task, readiness and state update. -/
structure Completion (plan : Plan Task) (source target : Finset Task) where
  task : Task
  intended : task ∈ plan.standing
  unfinished : task ∉ source
  ready : plan.Ready source task
  result : target = insert task source

/-- The existing process interface supplies witnessed histories.  Its boundary
here names a task; the closure predicate means task completion, without an
interpretation as subject individuation. -/
def processTheory (plan : Plan Task) : Theory (Finset Task) Task where
  Step := plan.Completion
  Closed completed task := task ∈ completed
  Agrees source target task := task ∈ source ↔ task ∈ target

/-- There is an admitted continuation on which the selected intention is
realized.  This includes already realized intentions through the empty path. -/
def Opportunity (plan : Plan Task) (completed : Finset Task) (task : Task) : Prop :=
  ∃ steps target, Nonempty (Process plan.processTheory steps completed target) ∧
    task ∈ target

/-- Each standing intention retains an opportunity for realization.  This is
an operational criterion, not a goodness or consciousness criterion. -/
def CoherentAt (plan : Plan Task) (completed : Finset Task) : Prop :=
  ∀ task ∈ plan.standing, plan.Opportunity completed task

/-- Running an agenda performs insertions in chronological order. -/
def run (completed : Finset Task) : List Task → Finset Task
  | [] => completed
  | task :: tail => run (insert task completed) tail

/-- An agenda can execute when each selected intention is unfinished and its
predecessors have completed at that exact position in the agenda. -/
def Ordered (plan : Plan Task) (completed : Finset Task) : List Task → Prop
  | [] => completed ⊆ completed
  | task :: tail => task ∈ plan.standing ∧ task ∉ completed ∧
      plan.Ready completed task ∧ plan.Ordered (insert task completed) tail

@[simp] theorem mem_run (completed : Finset Task) (agenda : List Task) (task : Task) :
    task ∈ run completed agenda ↔ task ∈ completed ∨ task ∈ agenda := by
  induction agenda generalizing completed with
  | nil => simp [run]
  | cons head tail ih =>
      simp only [run, ih, Finset.mem_insert, List.mem_cons]
      tauto

theorem completed_subset_run (completed : Finset Task) (agenda : List Task) :
    completed ⊆ run completed agenda := by
  intro task member
  exact (mem_run completed agenda task).2 (.inl member)

@[simp] theorem run_append (completed : Finset Task) (first last : List Task) :
    run completed (first ++ last) = run (run completed first) last := by
  induction first generalizing completed with
  | nil => rfl
  | cons head tail ih => simpa only [run, List.cons_append] using ih (insert head completed)

theorem ordered_append_iff (plan : Plan Task) (completed : Finset Task)
    (first last : List Task) :
    plan.Ordered completed (first ++ last) ↔
      plan.Ordered completed first ∧ plan.Ordered (run completed first) last := by
  induction first generalizing completed with
  | nil => simp [Ordered, run]
  | cons head tail ih =>
      simp only [List.cons_append, Ordered, run, ih]
      tauto

/-- An executable agenda cannot complete a task that was already complete
at its initial state. -/
theorem ordered_excludes_completed (plan : Plan Task) (completed : Finset Task)
    (agenda : List Task) (ordered : plan.Ordered completed agenda) :
    ∀ task ∈ agenda, task ∉ completed := by
  induction agenda generalizing completed with
  | nil => simp
  | cons head tail ih =>
      intro task member
      rcases List.mem_cons.1 member with same | later
      · subst task
        exact ordered.2.1
      · intro already
        exact ih _ ordered.2.2.2 task later (Finset.mem_insert_of_mem already)

/-- No task completion is duplicated by the compiler's agenda. -/
theorem ordered_nodup (plan : Plan Task) (completed : Finset Task)
    (agenda : List Task) (ordered : plan.Ordered completed agenda) : agenda.Nodup := by
  induction agenda generalizing completed with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
      apply List.nodup_cons.2
      refine ⟨?_, ih _ ordered.2.2.2⟩
      intro repeated
      exact plan.ordered_excludes_completed _ tail ordered.2.2.2 head repeated
        (Finset.mem_insert_self _ _)

/-- The compiler constructs every completion rather than assuming a path to
the claimed endpoint. -/
def compile (plan : Plan Task) (completed : Finset Task) (agenda : List Task)
    (ordered : plan.Ordered completed agenda) :
    Process plan.processTheory agenda.length completed (run completed agenda) := by
  induction agenda generalizing completed with
  | nil => exact .refl completed
  | cons task tail ih =>
      let first : Process plan.processTheory 1 completed (insert task completed) :=
        .snoc (.refl completed) {
          task := task
          intended := ordered.1
          unfinished := ordered.2.1
          ready := ordered.2.2.1
          result := rfl }
      simpa [run, Nat.add_comm] using first.append (ih _ ordered.2.2.2)

/-- Executing an ordered agenda realizes every task it contains. -/
theorem agenda_realizes (plan : Plan Task) (completed : Finset Task)
    (agenda : List Task) (ordered : plan.Ordered completed agenda)
    {task : Task} (included : task ∈ agenda) : plan.Opportunity completed task := by
  exact ⟨agenda.length, run completed agenda, ⟨plan.compile completed agenda ordered⟩,
    (mem_run completed agenda task).2 (.inr included)⟩

/-- Covering the unfinished standing intentions by an executable agenda gives
coherence through a concrete common continuation. -/
theorem ordered_cover_is_coherent (plan : Plan Task) (completed : Finset Task)
    (agenda : List Task) (ordered : plan.Ordered completed agenda)
    (covers : ∀ task ∈ plan.standing, task ∈ completed ∨ task ∈ agenda) :
    plan.CoherentAt completed := by
  intro task intended
  exact ⟨agenda.length, run completed agenda, ⟨plan.compile completed agenda ordered⟩,
    (mem_run completed agenda task).2 (covers task intended)⟩

/-- Every prefix of the compiled coordination preserves opportunities for all
standing intentions, including intentions completed in an earlier prefix. -/
theorem prefix_preserves_opportunities (plan : Plan Task) (completed : Finset Task)
    (earlier remainder : List Task)
    (ordered : plan.Ordered completed (earlier ++ remainder))
    (covers : ∀ task ∈ plan.standing, task ∈ completed ∨ task ∈ earlier ++ remainder) :
    plan.CoherentAt (run completed earlier) := by
  apply plan.ordered_cover_is_coherent _ remainder
    ((ordered_append_iff plan completed earlier remainder).1 ordered).2
  intro task intended
  rcases covers task intended with already | scheduled
  · exact .inl ((mem_run completed earlier task).2 (.inl already))
  · rcases List.mem_append.1 scheduled with earlierMember | later
    · exact .inl ((mem_run completed earlier task).2 (.inr earlierMember))
    · exact .inr later

namespace Completion

variable {plan : Plan Task} {source target : Finset Task}

/-- A coordinated completion cannot erase any earlier completion. -/
theorem preserves_completed (event : plan.Completion source target) : source ⊆ target := by
  rw [event.result]
  exact Finset.subset_insert _ _

/-- A coordinated event does not disable another ready task.  This is the
frame property supplied by the positive-dependency model. -/
theorem preserves_ready (event : plan.Completion source target) {task : Task}
    (ready : plan.Ready source task) : plan.Ready target task :=
  plan.ready_mono event.preserves_completed ready

/-- Every admitted completion gives strict progress in the outstanding set;
the result is stronger than a decreasing scalar task count. -/
theorem strictly_reduces_outstanding (event : plan.Completion source target) :
    plan.outstanding target ⊂ plan.outstanding source := by
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro task member
    simp only [outstanding, Finset.mem_sdiff] at member ⊢
    exact ⟨member.1, fun old => member.2 (event.preserves_completed old)⟩
  · intro equal
    have old : event.task ∈ plan.outstanding source := by
      simp [outstanding, event.intended, event.unfinished]
    have new : event.task ∈ plan.outstanding target := equal ▸ old
    simp only [event.result, outstanding, Finset.mem_sdiff, Finset.mem_insert] at new
    exact new.2 (.inl trivial)

/-- Announcing an event is a separate observation.  The event's readiness and
progress evidence are available even when this observation is false. -/
structure Announcement (event : plan.Completion source target) where
  announced : Bool

end Completion

/-! ## Dependency, implicit-intention and deadlock controls -/

namespace Controls

inductive CoordinatedTask
  | prepare
  | deliver
  deriving DecidableEq, Repr

def coordinated : Plan CoordinatedTask where
  standing := {.prepare, .deliver}
  predecessors
    | .prepare => ∅
    | .deliver => {.prepare}

theorem forward_ordered : coordinated.Ordered ∅ [.prepare, .deliver] := by
  simp [Ordered, Ready, coordinated]

theorem reversed_not_ordered : ¬ coordinated.Ordered ∅ [.deliver, .prepare] := by
  simp [Ordered, Ready, coordinated]

def prepared : coordinated.Completion ∅ {.prepare} where
  task := .prepare
  intended := by simp [coordinated]
  unfinished := by simp
  ready := by simp [Ready, coordinated]
  result := by simp

def delivered : coordinated.Completion {.prepare} {.prepare, .deliver} where
  task := .deliver
  intended := by simp [coordinated]
  unfinished := by simp
  ready := by simp [Ready, coordinated]
  result := by ext task; cases task <;> simp

def unannouncedPreparation : Completion.Announcement prepared := ⟨false⟩

def unannouncedDelivery : Completion.Announcement delivered := ⟨false⟩

theorem unannounced_coordination_makes_progress :
    unannouncedPreparation.announced = false ∧
    unannouncedDelivery.announced = false ∧
    coordinated.outstanding {.prepare, .deliver} = ∅ ∧
    coordinated.outstanding {.prepare} ⊂ coordinated.outstanding ∅ := by
  refine ⟨rfl, rfl, ?_, prepared.strictly_reduces_outstanding⟩
  simp [outstanding, coordinated]

theorem delivery_opportunity_survives_preparation :
    coordinated.Opportunity {.prepare} .deliver := by
  have history : Process coordinated.processTheory 1
      {.prepare} {.prepare, .deliver} := .snoc (.refl _) delivered
  exact ⟨1, {.prepare, .deliver}, ⟨history⟩, by simp⟩

theorem full_agenda_is_coherent : coordinated.CoherentAt ∅ := by
  apply coordinated.ordered_cover_is_coherent ∅ [.prepare, .deliver] forward_ordered
  intro task intended
  exact .inr (by cases task <;> simp)

/-- Both requirements are present, but neither can be the first event. -/
def cyclic : Plan CoordinatedTask where
  standing := {.prepare, .deliver}
  predecessors
    | .prepare => {.deliver}
    | .deliver => {.prepare}

theorem cyclic_has_no_first_event {target : Finset CoordinatedTask} :
    ¬ Nonempty (cyclic.Completion ∅ target) := by
  rintro ⟨event⟩
  have ready := event.ready
  cases taskEqual : event.task <;> simp [Ready, cyclic, taskEqual] at ready

theorem cyclic_process_stays_empty {steps : Nat} {source target : Finset CoordinatedTask}
    (history : Process cyclic.processTheory steps source target) (empty : source = ∅) :
    target = ∅ := by
  induction history with
  | refl state => exact empty
  | @snoc steps first middle last history event ih =>
      have middleEmpty := ih empty
      subst middle
      exact False.elim (cyclic_has_no_first_event ⟨event⟩)

/-- A consistent enumeration of intentions does not by itself give an
opportunity to realize them.  Dependency structure matters. -/
theorem cyclic_is_not_coherent : ¬ cyclic.CoherentAt ∅ := by
  intro coherent
  rcases coherent .prepare (by simp [cyclic]) with ⟨steps, target, ⟨history⟩, realized⟩
  have empty := cyclic_process_stays_empty history rfl
  simp [empty] at realized

end Controls
end Plan
end Mettapedia.Cybernetics.IntentionCoherence
