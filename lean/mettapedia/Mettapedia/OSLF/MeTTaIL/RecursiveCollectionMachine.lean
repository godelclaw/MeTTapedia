import Mettapedia.OSLF.MeTTaIL.EquationalScopedReceipts
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineTermination

/-!
# Retained recursive collection matching

The machine reuses the original scoped tasks and their ordinary expansion.
Only unordered collection expansion changes: it supplies finite consume/retain
allocations and records their authored paths. Every branch retains its actual
pending scoped tasks. The outer search runner and explorer are not duplicated.

Allocation enumeration at a collection node is eager. A tick bounds task
expansions, not allocation construction cost. No source-admission authority is
granted by these machine definitions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.RecursiveCollectionMachine

open Syntax RuleBinding ScopedRuleMatching CanonicalBags CollectionSelection
open EquationalScopedReceipts (Event)

abbrev Request := GeneralScopedMatchMachine.Request
abbrev Task := GeneralScopedMatchMachine.Task

structure Answer where
  assignment : Assignment
  trace : List Event
  deriving DecidableEq, Repr

structure Work where
  assignment : Assignment
  tasks : List Task
  trace : List Event := []
  deriving Repr

structure State where
  agenda : List Work
  answers : List Answer := []
  deriving Repr

/-- Noncollection expansion uses the established scoped machine. Its ordinary
bag cursors are not introduced by this machine. -/
def inheritWork (work : GeneralScopedMatchMachine.Work) : Work :=
  ⟨work.assignment, work.tasks, []⟩

def allocationWork (path : List Nat) (depth : Nat) (initial : Assignment)
    (kind : CollType) (schemas : List Pattern) (rest : Option String)
    (allocation : Allocation Pattern) : Option Work :=
  let arguments : Task := .arguments path depth 0 schemas allocation.values
  let residual := arrange kind allocation.residual
  let trace := [⟨path, kind, allocation.decisions⟩]
  match rest with
  | none => if residual.isEmpty then some ⟨initial, [arguments], trace⟩ else none
  | some name => some ⟨initial, [arguments,
      .restCapture (path ++ [schemas.length]) depth name kind residual], trace⟩

def expand (request : Request) (initial : Assignment) (task : Task) : List Work :=
  match task with
  | .tree path depth (.collection kind schemas rest) (.collection actual targets actualRest) =>
      if kind = actual ∧ actualRest = none then
        if kind = .vec then (GeneralScopedMatchMachine.expand request initial task).map inheritWork
        else (tracedAllocations (kind == .hashSet) schemas.length (arrange kind targets)).filterMap
          (allocationWork path depth initial kind schemas rest)
      else []
  | .tree .. | .arguments .. | .restCapture .. =>
      (GeneralScopedMatchMachine.expand request initial task).map inheritWork
  | .bag .. | .bagSelect .. => []

def start (request : Request) : State :=
  ⟨[⟨request.initial, [.tree request.path request.depth request.schema request.target], []⟩], []⟩

def advance (request : Request) (work : Work) : List Work :=
  match work.tasks with
  | [] => []
  | task :: tasks => (expand request work.assignment task).map fun branch =>
      ⟨branch.assignment, branch.tasks ++ tasks, work.trace ++ branch.trace⟩

def tick (request : Request) (state : State) : State :=
  match state.agenda with
  | [] => state
  | work :: agenda =>
      match work.tasks with
      | [] => ⟨agenda, state.answers ++ [⟨work.assignment, work.trace⟩]⟩
      | _ :: _ => ⟨advance request work ++ agenda, state.answers⟩

def run (request : Request) : Nat → State → State
  | 0, state => state
  | work + 1, state => run request work (tick request state)

def complete (state : State) : Bool := state.agenda.isEmpty

theorem run_add (request : Request) (first extra : Nat) (state : State) :
    run request (first + extra) state = run request extra (run request first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, run]
  | succ first ih => simpa only [Nat.succ_add, run] using ih (tick request state)

theorem tick_answers_prefix (request : Request) (state : State) :
    state.answers <+: (tick request state).answers := by
  cases agenda : state.agenda with
  | nil => simp [tick, agenda]
  | cons work rest =>
    cases tasks : work.tasks with
    | nil => simp [tick, agenda, tasks]
    | cons task tasks => simp [tick, agenda, tasks]

theorem run_answers_prefix (request : Request) (work : Nat) (state : State) :
    state.answers <+: (run request work state).answers := by
  induction work generalizing state with
  | zero => exact List.prefix_refl _
  | succ work ih => exact (tick_answers_prefix request state).trans (ih _)

theorem tick_complete (request : Request) {state : State}
    (done : complete state = true) : tick request state = state := by
  have empty := List.isEmpty_iff.mp done
  simp [tick, empty]

theorem run_complete (request : Request) (work : Nat) {state : State}
    (done : complete state = true) : run request work state = state := by
  induction work with
  | zero => rfl
  | succ work ih => simp only [run, tick_complete request done, ih]

/-- A parent allocation's event is attached once when the node expands. Its
children inherit it as a prefix; scheduling does not recreate the event. -/
theorem advance_trace_prefix (request : Request) {work branch : Work}
    (member : branch ∈ advance request work) : work.trace <+: branch.trace := by
  cases tasks : work.tasks with
  | nil => simp [advance, tasks] at member
  | cons task tasks =>
    simp only [advance, tasks] at member
    obtain ⟨expanded, _, rfl⟩ := List.mem_map.mp member
    exact List.prefix_append _ _

/-- A completed branch contributes exactly one full answer record. Equal
assignments at different histories remain separate list occurrences. -/
theorem tick_publication_account (request : Request) (work : Work)
    (tail : List Work) (answers : List Answer) (finished : work.tasks = []) :
    tick request ⟨work :: tail, answers⟩ =
      ⟨tail, answers ++ [⟨work.assignment, work.trace⟩]⟩ := by
  simp only [tick, finished]

/-- A recursive matching tick publishes at most one complete answer record. -/
theorem tick_answers_length (request : Request) (state : State) :
    (tick request state).answers.length ≤ state.answers.length + 1 := by
  cases agenda : state.agenda with
  | nil => simp only [tick, agenda]; omega
  | cons work rest =>
    cases tasks : work.tasks with
    | nil => simp only [tick, agenda, tasks, List.length_append, List.length_singleton]; omega
    | cons task tasks => simp only [tick, agenda, tasks]; omega

end Mettapedia.OSLF.MeTTaIL.RecursiveCollectionMachine
