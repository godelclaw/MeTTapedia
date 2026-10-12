import Mettapedia.GSLT.Distinction.OrderedSimulation
import Mettapedia.GSLT.Distinction.SpanTransport
import Mettapedia.Machines.Cursor.Scheduling
import Mettapedia.Machines.Cursor.FairObservation
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Order

/-!
# Ordered simulations as span relations

`OrderedSimulation` relates nondeterministic machines whose successors come
as ordered lists, position by position.  `ProductiveBlocks.CostSimulation`
relates deterministic machines that publish events, within a cost bound, and
its span reading is the segment relation of `SpanTransport`.  This module gives
the ordered relation the same reading, so that both relations are instances of
the source laws of `SpanTransport.SpanRelation` and inherit its transfer
theorems.

* **Successor occurrences** (`OrderedSystem.Occurrence`,
  `OrderedSystem.occurrenceSpan`).  An occurrence is a state and a position in
  its successor list; the occurrence span runs from the state to the successor
  at that position.  Labelled by positions, with halting as the atom, it is a
  `SpanTransport.Labelled` reduction span (`OrderedSystem.occurrences`).
* **The occurrence relation** (`occurrenceRelation`): occurrences at the same
  position from related states to related successors.  It keeps positions
  (`occurrenceRelation_keeps`), and the composite of two occurrence relations
  lies in the occurrence relation of the composite relation
  (`occurrenceRelation_comp_events`).
* **Fibre matching** (`OrderedSimulation.outFibresMatch`).  Position-by-position
  relation of successor lists is exactly a one-to-one correspondence of the
  outgoing occurrences, so an ordered simulation has both source laws
  (`OrderedSimulation.sourceForthOcc`, `OrderedSimulation.sourceBackOcc`),
  keeps the number of successor occurrences (`OrderedSimulation.successor_card_eq`),
  and preserves and reflects every future formula over positions and halting
  (`OrderedSimulation.future_related`).  A cost simulation each way gives the
  same two source laws on run segments (`CostSimulation.segment_sourceForthOcc`,
  `CostSimulation.segment_sourceBackOcc`), without fibre matching.

The lockstep limitation. `OrderedSimulation` advances every occurrence of a
frontier in lockstep; `CostSimulation` lets one source transition cost a
varying number of target transitions.  Matching each branch within a varying
number of target steps does not relate the frontiers position by position at
`cost` times the fuel (`OrderedSimulationSpansControls.stutter_misaligns`),
so these interfaces cannot be identified. `ScheduledFrontier` supplies retained
slots with one reserved boundary clock per occurrence. A scheduling quantum
consumes only that slot's remaining allocation; completed slots do not overrun
their boundary. The flattened view preserves original slot order, rather than
ordering answers by worker completion time. This construction assumes independent
owned slots; reordering shared effects requires an additional commuting contract.

General boundary correspondence takes explicit finite-realization evidence. It
does not discover the clocks of an arbitrary target computation. Allocation
fairness supplies sufficient service for finite reservations, without asserting
termination of the underlying language or identifying a spent budget with an answer.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.Distinction.SpanTransport

universe u v w

namespace OrderedSystem

variable {State : Type u} (system : OrderedSystem State)

/-- **A successor occurrence**: a state and a position in its successor list. -/
structure Occurrence where
  state : State
  position : ℕ
  inRange : position < (system.step state).length

variable {system}

/-- The successor at an occurrence. -/
def Occurrence.next (occurrence : system.Occurrence) : State :=
  (system.step occurrence.state).get ⟨occurrence.position, occurrence.inRange⟩

variable (system)

/-- **The occurrence span**: from a state to the successor at each position. -/
def occurrenceSpan : ReductionSpan.{u, u} State where
  Edge := system.Occurrence
  source := Occurrence.state
  target := Occurrence.next

/-- The occurrence span labelled by positions, observing halting. -/
def occurrences : Labelled.{u, u} State Bool ℕ where
  span := system.occurrenceSpan
  read := Occurrence.position
  observes halted state := system.halted state = halted

end OrderedSystem

/-- **The occurrence relation of a state relation**: occurrences at one position
from related states to related successors. -/
def occurrenceRelation {S : Type u} {T : Type v} (source : OrderedSystem S) (target : OrderedSystem T)
    (related : S → T → Prop) : SpanRelation source.occurrenceSpan target.occurrenceSpan where
  states := related
  events first second := related first.state second.state ∧ first.position = second.position ∧
    related first.next second.next
  source_rel _ _ matched := matched.1
  target_rel _ _ matched := matched.2.2

section Occurrences

variable {S : Type u} {T : Type v} {W : Type w} {source : OrderedSystem S} {target : OrderedSystem T}
  {third : OrderedSystem W} {related : S → T → Prop} {next : T → W → Prop}

theorem occurrenceRelation_keeps :
    (occurrenceRelation source target related).Keeps OrderedSystem.Occurrence.position
      OrderedSystem.Occurrence.position :=
  fun _ _ matched => matched.2.1

/-- The composite of two occurrence relations relates occurrences of the
composite relation. -/
theorem occurrenceRelation_comp_events {first : source.Occurrence} {last : third.Occurrence}
    (matched : ((occurrenceRelation source target related).comp
      (occurrenceRelation target third next)).events first last) :
    (occurrenceRelation source third (Relation.Comp related next)).events first last := by
  obtain ⟨middle, ⟨starts, positions, nexts⟩, starts', positions', nexts'⟩ := matched
  exact ⟨⟨middle.state, starts, starts'⟩, positions.trans positions', ⟨middle.next, nexts, nexts'⟩⟩

namespace OrderedSimulation

/-- **Position-by-position relation of successor lists is a one-to-one
correspondence of outgoing occurrences.** -/
theorem outFibresMatch (simulation : OrderedSimulation source target related) :
    (occurrenceRelation source target related).OutFibresMatch := by
  intro state state' relatedStates
  have lists := simulation.step relatedStates
  have lengths := lists.length_eq
  refine ⟨{
    toFun := fun occurrence => ⟨⟨state', occurrence.1.position, by
        have inRange := occurrence.1.inRange
        have stateEq : occurrence.1.state = state := occurrence.2
        rw [stateEq, lengths] at inRange
        exact inRange⟩, rfl⟩
    invFun := fun occurrence => ⟨⟨state, occurrence.1.position, by
        have inRange := occurrence.1.inRange
        have stateEq : occurrence.1.state = state' := occurrence.2
        rw [stateEq, ← lengths] at inRange
        exact inRange⟩, rfl⟩
    left_inv := by
      rintro ⟨⟨_, position, inRange⟩, rfl⟩
      rfl
    right_inv := by
      rintro ⟨⟨_, position, inRange⟩, rfl⟩
      rfl }, ?_⟩
  rintro ⟨⟨_, position, inRange⟩, rfl⟩
  exact ⟨relatedStates, rfl, lists.get inRange _⟩

theorem sourceForthOcc (simulation : OrderedSimulation source target related) :
    (occurrenceRelation source target related).SourceForthOcc :=
  simulation.outFibresMatch.sourceForthOcc

theorem sourceBackOcc (simulation : OrderedSimulation source target related) :
    (occurrenceRelation source target related).SourceBackOcc :=
  simulation.outFibresMatch.sourceBackOcc

/-- **Related states have equally many successor occurrences at each
position.** -/
theorem successor_card_eq (simulation : OrderedSimulation source target related) {state : S}
    {state' : T} (relatedStates : related state state') (position : ℕ) :
    Nat.card {occurrence : source.Occurrence // occurrence.state = state ∧
        occurrence.position = position} =
      Nat.card {occurrence : target.Occurrence // occurrence.state = state' ∧
        occurrence.position = position} :=
  outgoing_card_eq (occurrenceRelation source target related) simulation.outFibresMatch
    occurrenceRelation_keeps relatedStates position

/-- **Every future formula over positions and halting agrees on related
states.** -/
theorem future_related (simulation : OrderedSimulation source target related)
    {formula : Tense Bool ℕ} (future : formula.IsFuture) :
    Related related (Tense.sat source.occurrences formula) (Tense.sat target.occurrences formula) :=
  sat_related_future source.occurrences target.occurrences (occurrenceRelation source target related)
    occurrenceRelation_keeps
    (fun halted _ _ relatedStates => by
      change source.halted _ = halted ↔ target.halted _ = halted
      rw [simulation.halted relatedStates])
    simulation.sourceForthOcc simulation.sourceBackOcc future

end OrderedSimulation

end Occurrences

/-! ## Occurrence-retaining execution with local boundary clocks -/

namespace ScheduledFrontier

open Mettapedia.Machines.Cursor

variable {State : Type u} {State' : Type v} {n : ℕ}

/-- A slot retains its whole local frontier and allocation account. Reaching
zero remaining allocation is a declared boundary, not a successful answer. -/
@[ext] structure Slot (State : Type u) where
  worked : ℕ
  remaining : ℕ
  states : List State

variable (system : OrderedSystem State)

/-- Advance up to this slot's reserved boundary. Surplus service cannot move a
completed branch past the boundary while another branch is still pending. -/
def Slot.serve (quantum : ℕ) (slot : Slot State) : Slot State :=
  let used := min quantum slot.remaining
  ⟨slot.worked + used, slot.remaining - used, system.runFrontier used slot.states⟩

@[simp] theorem Slot.serve_zero (slot : Slot State) : slot.serve system 0 = slot := by
  cases slot
  simp only [Slot.serve, Nat.zero_min, Nat.add_zero, Nat.sub_zero, OrderedSystem.runFrontier]

theorem Slot.serve_finished (quantum : ℕ) (slot : Slot State)
    (finished : slot.remaining = 0) : slot.serve system quantum = slot := by
  cases slot
  simp_all only [Slot.serve, Nat.min_zero, Nat.add_zero, Nat.sub_zero, OrderedSystem.runFrontier]

/-- Local round allocation composes at its retained state, including its
unused reservation and already allocated rounds. -/
theorem Slot.serve_add (first second : ℕ) (slot : Slot State) :
    slot.serve system (first + second) = (slot.serve system first).serve system second := by
  have uses : min (first + second) slot.remaining =
      min first slot.remaining + min second (slot.remaining - min first slot.remaining) := by omega
  apply Slot.ext
  · simp only [Slot.serve, uses]
    omega
  · simp only [Slot.serve, uses]
    omega
  · simp only [Slot.serve, uses, system.runFrontier_add]

theorem Slot.serve_account (quantum : ℕ) (slot : Slot State) :
    (slot.serve system quantum).worked + (slot.serve system quantum).remaining =
      slot.worked + slot.remaining := by
  simp only [Slot.serve]
  omega

/-- Original occurrence positions are owners. Equal-looking states at different
positions remain separate slots and receive separate allocations. -/
abbrev Slots (n : ℕ) (State : Type u) := Fin n → Slot State

abbrev Command (n : ℕ) := Scheduling.Command (Fin n)

def dispatch (command : Command n) (slots : Slots n State) : Slots n State :=
  Function.update slots command.1 ((slots command.1).serve system command.2)

def execute : List (Command n) → Slots n State → Slots n State
  | [], slots => slots
  | command :: rest, slots => execute rest (dispatch system command slots)

@[simp] theorem dispatch_selected (command : Command n) (slots : Slots n State) :
    dispatch system command slots command.1 = (slots command.1).serve system command.2 := by
  simp [dispatch]

theorem dispatch_other (command : Command n) (slots : Slots n State) (id : Fin n)
    (different : id ≠ command.1) : dispatch system command slots id = slots id := by
  simp only [dispatch, Function.update_of_ne different]

/-- Every finite schedule is exactly its independent per-occurrence allocation.
The allocation is the existing cursor scheduler's operation, not a second count. -/
theorem execute_at (schedule : List (Command n)) (slots : Slots n State) (id : Fin n) :
    execute system schedule slots id =
      (slots id).serve system (Scheduling.allocation id schedule) := by
  induction schedule generalizing slots with
  | nil => simp only [execute, Scheduling.allocation, Slot.serve_zero]
  | cons command rest ih =>
      rw [execute, ih]
      by_cases selected : command.1 = id
      · subst id
        simp only [Scheduling.allocation, if_true, dispatch_selected]
        exact (Slot.serve_add system command.2 (Scheduling.allocation command.1 rest) _).symm
      · simp only [Scheduling.allocation, selected, if_false, Nat.zero_add,
          dispatch_other system command slots id (Ne.symm selected)]

/-- Pause and resume keeps all slots, including completed reservations. -/
theorem execute_append (first second : List (Command n)) (slots : Slots n State) :
    execute system (first ++ second) slots = execute system second (execute system first slots) := by
  induction first generalizing slots with
  | nil => rfl
  | cons command rest ih => simp only [List.cons_append, execute, ih]

theorem execute_eq_of_allocation_eq (first second : List (Command n))
    (allocations : ∀ id, Scheduling.allocation id first = Scheduling.allocation id second)
    (slots : Slots n State) : execute system first slots = execute system second slots := by
  funext id
  simp only [execute_at, allocations id]

theorem execute_perm {first second : List (Command n)} (permutation : first.Perm second)
    (slots : Slots n State) : execute system first slots = execute system second slots :=
  execute_eq_of_allocation_eq system first second
    (fun id => Scheduling.allocation_perm permutation id) slots

theorem execute_account (schedule : List (Command n)) (slots : Slots n State) (id : Fin n) :
    (execute system schedule slots id).worked + (execute system schedule slots id).remaining =
      (slots id).worked + (slots id).remaining := by
  rw [execute_at]
  exact Slot.serve_account system _ _

/-- View blocks in their retained occurrence order. Scheduler chronology does
not become the order of answers in this observation. -/
def view (slots : Slots n State) : List State :=
  (List.ofFn (fun id => (slots id).states)).flatten

/-- The owner tag distinguishes duplicate occurrences even when their state
values or their produced answers coincide. -/
def taggedView (slots : Slots n State) : List (Fin n × State) :=
  (List.ofFn (fun id => (slots id).states.map (fun state => (id, state)))).flatten

theorem taggedView_forget (slots : Slots n State) :
    (taggedView slots).map Prod.snd = view slots := by
  simp [taggedView, view, List.map_flatten, List.map_ofFn, Function.comp_def]

/-- Reserved clocks are supplied with their semantic evidence separately. -/
def reserve (clocks : Fin n → ℕ) (states : Fin n → List State) : Slots n State :=
  fun id => ⟨0, clocks id, states id⟩

theorem execute_reservation (schedule : List (Command n)) (clocks : Fin n → ℕ)
    (states : Fin n → List State) (id : Fin n) :
    execute system schedule (reserve clocks states) id =
      ⟨min (Scheduling.allocation id schedule) (clocks id),
        clocks id - min (Scheduling.allocation id schedule) (clocks id),
        system.runFrontier (min (Scheduling.allocation id schedule) (clocks id)) (states id)⟩ := by
  simp only [execute_at, reserve, Slot.serve, Nat.zero_add]

theorem execute_enough (schedule : List (Command n)) (clocks : Fin n → ℕ)
    (states : Fin n → List State) (enough : ∀ id, clocks id ≤ Scheduling.allocation id schedule) :
    execute system schedule (reserve clocks states) =
      fun id => ⟨clocks id, 0, system.runFrontier (clocks id) (states id)⟩ := by
  funext id
  rw [execute_reservation, Nat.min_eq_right (enough id), Nat.sub_self]

theorem reservation_complete_iff (schedule : List (Command n)) (clocks : Fin n → ℕ)
    (states : Fin n → List State) :
    (∀ id, (execute system schedule (reserve clocks states) id).remaining = 0) ↔
      ∀ id, clocks id ≤ Scheduling.allocation id schedule := by
  simp only [execute_reservation]
  constructor
  · intro completed id
    have reached := completed id
    omega
  · intro enough id
    rw [Nat.min_eq_right (enough id), Nat.sub_self]

theorem view_enough (schedule : List (Command n)) (clocks : Fin n → ℕ)
    (states : Fin n → List State) (enough : ∀ id, clocks id ≤ Scheduling.allocation id schedule) :
    view (execute system schedule (reserve clocks states)) =
      (List.ofFn (fun id => system.runFrontier (clocks id) (states id))).flatten := by
  rw [execute_enough system schedule clocks states enough]
  rfl

theorem ofFn_related {A : Type u} {B : Type v} {relation : A → B → Prop}
    (first : Fin n → A) (second : Fin n → B) (matching : ∀ id, relation (first id) (second id)) :
    List.Forall₂ relation (List.ofFn first) (List.ofFn second) := by
  induction n with
  | zero => simp only [List.ofFn_zero]; exact .nil
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      exact .cons (matching 0) (ih _ _ (fun id => matching id.succ))

/-- A supplied finite boundary realization lifts from each branch to the
complete ordered frontier. The source and target clocks may differ by slot. -/
theorem boundaries_related {source : OrderedSystem State} {target : OrderedSystem State'}
    {related : State → State' → Prop} (sourceClocks targetClocks : Fin n → ℕ)
    (sourceStates : Fin n → List State) (targetStates : Fin n → List State')
    (realized : ∀ id, List.Forall₂ related
      (source.runFrontier (sourceClocks id) (sourceStates id))
      (target.runFrontier (targetClocks id) (targetStates id)))
    (sourceSchedule targetSchedule : List (Command n))
    (enoughSource : ∀ id, sourceClocks id ≤ Scheduling.allocation id sourceSchedule)
    (enoughTarget : ∀ id, targetClocks id ≤ Scheduling.allocation id targetSchedule) :
    List.Forall₂ related
      (view (execute source sourceSchedule (reserve sourceClocks sourceStates)))
      (view (execute target targetSchedule (reserve targetClocks targetStates))) := by
  rw [view_enough source sourceSchedule sourceClocks sourceStates enoughSource,
    view_enough target targetSchedule targetClocks targetStates enoughTarget]
  exact List.rel_flatten (ofFn_related _ _ realized)

/-- Branch boundaries retain occurrence count as well as order. Within a slot,
ordered branching may create further occurrences and their duplicates. -/
theorem boundaries_card_eq {source : OrderedSystem State} {target : OrderedSystem State'}
    {related : State → State' → Prop} (sourceClocks targetClocks : Fin n → ℕ)
    (sourceStates : Fin n → List State) (targetStates : Fin n → List State')
    (realized : ∀ id, List.Forall₂ related
      (source.runFrontier (sourceClocks id) (sourceStates id))
      (target.runFrontier (targetClocks id) (targetStates id)))
    (sourceSchedule targetSchedule : List (Command n))
    (enoughSource : ∀ id, sourceClocks id ≤ Scheduling.allocation id sourceSchedule)
    (enoughTarget : ∀ id, targetClocks id ≤ Scheduling.allocation id targetSchedule) :
    (view (execute source sourceSchedule (reserve sourceClocks sourceStates))).length =
      (view (execute target targetSchedule (reserve targetClocks targetStates))).length :=
  (boundaries_related sourceClocks targetClocks sourceStates targetStates realized
    sourceSchedule targetSchedule enoughSource enoughTarget).length_eq

/-- A checked source observation has a scheduled target realization with one
clock per retained occurrence. The target is compared at these local boundaries,
not at a common multiplier of the source fuel. -/
theorem source_frontier_related {source : OrderedSystem State} {target : OrderedSystem State'}
    {related : State → State' → Prop}
    (stable : ∀ state, source.halted state = true → source.step state = [])
    (fuel : ℕ) (sourceStates : Fin n → State) (targetStates : Fin n → State')
    (clocks : Fin n → ℕ)
    (realized : ∀ id, List.Forall₂ related (source.runFrontier fuel [sourceStates id])
      (target.runFrontier (clocks id) [targetStates id]))
    (schedule : List (Command n))
    (enough : ∀ id, clocks id ≤ Scheduling.allocation id schedule) :
    List.Forall₂ related (source.runFrontier fuel (List.ofFn sourceStates))
      (view (execute target schedule (reserve clocks (fun id => [targetStates id])))) := by
  rw [source.runFrontier_distribute stable, view_enough target schedule clocks _ enough]
  have blocks := List.rel_flatten (ofFn_related _ _ realized)
  simpa only [List.flatMap_def, List.map_ofFn, Function.comp_def] using blocks

/-- Allocation fairness is the existing cursor fairness contract. For finitely
many reserved observations it supplies a common finite horizon, after which
every slot and its exact local frontier are permanently unchanged. -/
theorem fair_eventually_boundary (schedule : ℕ → Command n)
    (fair : FairObservation.FairAllocation schedule)
    (clocks : Fin n → ℕ) (states : Fin n → List State) :
    ∃ horizon, ∀ extra,
      execute system (FairObservation.schedulePrefix schedule (horizon + extra))
        (reserve clocks states) =
          fun id => ⟨clocks id, 0, system.runFrontier (clocks id) (states id)⟩ := by
  classical
  choose horizons allocated using fun id => fair id (clocks id)
  obtain ⟨horizon, bounds⟩ := Finite.exists_le horizons
  refine ⟨horizon, fun extra => execute_enough system _ clocks states (fun id => ?_)⟩
  exact (allocated id).trans
    (FairObservation.allocation_prefix_mono schedule id
      ((bounds id).trans (Nat.le_add_right horizon extra)))

/-- The round-robin finite schedule services every occurrence, even equal
values, as a separate owner. Quantum zero intentionally supplies no progress. -/
def rounds (quantum : ℕ) : ℕ → List (Command n)
  | 0 => []
  | count + 1 => (List.finRange n).map (fun id => (id, quantum)) ++ rounds quantum count

theorem rounds_allocation (quantum count : ℕ) (id : Fin n) :
    Scheduling.allocation id (rounds quantum count) = count * quantum := by
  induction count with
  | zero => simp only [rounds, Scheduling.allocation, Nat.zero_mul]
  | succ count ih =>
      rw [rounds, FairObservation.allocation_append, Scheduling.allocation_uniform,
        List.count_finRange, Nat.one_mul, ih]
      simp only [Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- A concrete finite schedule executes any finite reservation. The whole
program may have arbitrarily many successive semantic observations. -/
theorem rounds_execute (clocks : Fin n → ℕ) (states : Fin n → List State)
    (count : ℕ) (bound : ∀ id, clocks id ≤ count) :
    execute system (rounds 1 count) (reserve clocks states) =
      fun id => ⟨clocks id, 0, system.runFrontier (clocks id) (states id)⟩ := by
  apply execute_enough
  intro id
  simpa only [rounds_allocation, Nat.mul_one] using bound id

theorem zero_quantum_preserves_reservations (count : ℕ) (slots : Slots n State) :
    execute system (rounds 0 count) slots = slots := by
  funext id
  simp only [execute_at, rounds_allocation, Nat.mul_zero, Slot.serve_zero]

end ScheduledFrontier

end Mettapedia.GSLT.Distinction
