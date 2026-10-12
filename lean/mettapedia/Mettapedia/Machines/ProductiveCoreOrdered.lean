import Mettapedia.Machines.ProductiveCoreAdapters
import Mettapedia.GSLT.Distinction.OrderedSimulationSpans
import Mettapedia.Machines.ResumableRegion

/-!
# Deterministic cores at the ordered-frontier seam

Optional successors produce ordered zero-or-one lists. Each frontier round
advances every unfinished occurrence by one core transition. A missing
transition is stable here; it is not classified as a successful answer.
The proved frontier account is a lockstep account and retains duplicate
state occurrences. It does not identify ordered simulation with a weak
branch simulation whose branches take different numbers of target steps.

The reserved-slot interface additionally realizes finite source observations
with independently derived branch clocks. `latencyCore` inserts a specified
number of administrative inspections before each original computational
transition. Its independently stated `LatencyStep` judgment distinguishes the
two kinds; a decreasing remaining count prevents infinite inserted administration.
This construction supplies a general machine-model instance, not a refinement
claim about native CEK, Krivine, MeTTa or C implementations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProductiveCoreOrdered

open Mettapedia.GSLT.Distinction
open ProductiveBlocks ProductiveCoreAdapters

variable {Term : Type}

def walk (core : MachineCore Term) : Nat → core.State → core.State
  | 0, state => state
  | fuel + 1, state => match core.step state with
      | none => state
      | some next => walk core fuel next

theorem walk_stopped (core : MachineCore Term) {state : core.State}
    (stopped : core.Final state) (fuel : Nat) : walk core fuel state = state := by
  change core.step state = none at stopped
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [walk, stopped]

theorem walk_reachable (core : MachineCore Term) (fuel : Nat) (state : core.State) :
    core.Steps state (walk core fuel state) := by
  induction fuel generalizing state with
  | zero => exact .refl
  | succ fuel ih =>
      cases step : core.step state with
      | none => simpa only [walk, step] using (Relation.ReflTransGen.refl : core.Steps state state)
      | some next =>
          exact Relation.ReflTransGen.head step (by simpa only [walk, step] using ih next)

theorem walk_add (core : MachineCore Term) (first second : Nat) (state : core.State) :
    walk core (first + second) state = walk core second (walk core first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, walk]
  | succ first ih =>
      rw [show first + 1 + second = (first + second) + 1 by omega]
      cases step : core.step state with
      | none => simp only [walk, step, walk_stopped core step]
      | some next => simp only [walk, step, ih next]

def orderedCore (core : MachineCore Term) : OrderedSystem core.State where
  step state := (core.step state).toList
  halted state := (core.step state).isNone

theorem ordered_halted_iff (core : MachineCore Term) (state : core.State) :
    (orderedCore core).halted state = true ↔ core.Final state := by
  cases step : core.step state <;> simp [orderedCore, MachineCore.Final, step]

theorem ordered_advance (core : MachineCore Term) (state : core.State) :
    (orderedCore core).advance state = [walk core 1 state] := by
  cases step : core.step state <;> simp [OrderedSystem.advance, orderedCore, walk, step]

theorem frontier_advance (core : MachineCore Term) (states : List core.State) :
    states.flatMap (orderedCore core).advance = states.map (walk core 1) := by
  induction states with
  | nil => rfl
  | cons state states ih => simp only [List.flatMap_cons, List.map_cons, ordered_advance, List.singleton_append, ih]

theorem halted_frontier_fixed (core : MachineCore Term) (fuel : Nat) (states : List core.State)
    (halted : states.all (orderedCore core).halted = true) : states.map (walk core fuel) = states := by
  induction states with
  | nil => rfl
  | cons state states ih =>
      simp only [List.all_cons, Bool.and_eq_true] at halted
      have stopped := (ordered_halted_iff core state).mp halted.1
      simp only [List.map_cons, walk_stopped core stopped, ih halted.2]

theorem ordered_frontier_walk (core : MachineCore Term) (fuel : Nat) (states : List core.State) :
    (orderedCore core).runFrontier fuel states = states.map (walk core fuel) := by
  induction fuel generalizing states with
  | zero => simp [OrderedSystem.runFrontier, walk]
  | succ fuel ih =>
      by_cases halted : states.all (orderedCore core).halted = true
      · simp only [OrderedSystem.runFrontier, halted, if_true]
        exact (halted_frontier_fixed core (fuel + 1) states halted).symm
      · simp only [OrderedSystem.runFrontier, halted, ih, frontier_advance, List.map_map]
        apply List.map_congr_left
        intro state _
        exact (walk_add core 1 fuel state).symm.trans (congrArg (fun n => walk core n state) (by omega))

theorem ordered_frontier_occurrences (core : MachineCore Term) (fuel : Nat) (states : List core.State) :
    ((orderedCore core).runFrontier fuel states).length = states.length := by
  rw [ordered_frontier_walk, List.length_map]

theorem ordered_frontier_resume (core : MachineCore Term) (first second : Nat) (states : List core.State) :
    (orderedCore core).runFrontier (first + second) states =
      (orderedCore core).runFrontier second ((orderedCore core).runFrontier first states) := by
  simp only [ordered_frontier_walk, List.map_map]
  apply List.map_congr_left
  intro state _
  exact walk_add core first second state

theorem frontier_computational_budget (core : MachineCore Term) (fuel : Nat) (states : List core.State) :
    (states.map (fun state => (coreMachine core).spent (fun _ => 1) fuel state)).sum ≤ fuel * states.length := by
  induction states with
  | nil => simp
  | cons state states ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
      have bounded := unit_account_le_budget (coreMachine core) fuel state
      omega

theorem core_run_endpoint (core : MachineCore Term) (fuel : Nat) (state : core.State) :
    ((coreMachine core).run fuel state).2 = .exhausted (walk core fuel state) ∨
      (((coreMachine core).run fuel state).2 = .stuck (walk core fuel state) ∧
        core.Final (walk core fuel state)) := by
  induction fuel generalizing state with
  | zero => exact .inl rfl
  | succ fuel ih =>
      cases step : core.step state with
      | none =>
          exact .inr ⟨by simp only [Machine.run, core_missing_step core step, walk, step],
            by change core.step (walk core (fuel + 1) state) = none; simp only [walk, step]⟩
      | some next =>
          have advanced := core_step core (show core.StepRel state next from step)
          simpa only [Machine.run, advanced, walk, step] using ih next

theorem singleton_frontier_execution (core : MachineCore Term) (fuel : Nat) (state : core.State) :
    ∃ final, (orderedCore core).runFrontier fuel [state] = [final] ∧ core.Steps state final ∧
      (((coreMachine core).run fuel state).2 = .exhausted final ∨
        (((coreMachine core).run fuel state).2 = .stuck final ∧ core.Final final)) :=
  ⟨walk core fuel state, by simp only [ordered_frontier_walk, List.map_cons, List.map_nil],
    walk_reachable core fuel state, core_run_endpoint core fuel state⟩

theorem walk_runSlice (core : MachineCore Term) (fuel : Nat) (state : core.State) :
    walk core fuel state = (core.runSlice fuel state).1 := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases found : core.step state with
      | none => simp only [walk, MachineCore.runSlice, found]
      | some next => simpa only [walk, MachineCore.runSlice, found] using ih next

theorem core_run_trace (core : MachineCore Term) (fuel : Nat) (state : core.State) :
    Trace core state ((coreMachine core).run fuel state).1 (walk core fuel state) := by
  rcases core_run_sound core fuel state with ⟨final, trace, ending⟩ | ⟨final, trace, ending, _⟩
  · rcases core_run_endpoint core fuel state with reached | ⟨reached, _⟩
    · rw [ending] at reached
      cases reached
      exact trace
    · rw [ending] at reached
      cases reached
  · rcases core_run_endpoint core fuel state with reached | ⟨reached, _⟩
    · rw [ending] at reached
      cases reached
    · rw [ending] at reached
      cases reached
      exact trace

/-- The scheduler's retained singleton is the exact endpoint of the existing
productive-machine core adapter, with an independently derived trace and cost.
Allocation rounds and actual computational work are accounted separately. -/
theorem scheduled_core_trace (core : MachineCore Term) {n : Nat}
    (clocks : Fin n → Nat) (states : Fin n → core.State)
    (schedule : List (ScheduledFrontier.Command n)) (id : Fin n) :
    let used := min (Mettapedia.Machines.Cursor.Scheduling.allocation id schedule) (clocks id)
    let final := walk core used (states id)
    (ScheduledFrontier.execute (orderedCore core) schedule
      (ScheduledFrontier.reserve clocks (fun owner => [states owner])) id).states = [final] ∧
      Trace core (states id) ((coreMachine core).run used (states id)).1 final ∧
      ((coreMachine core).spent (fun _ => 1) used (states id) =
        ((coreMachine core).run used (states id)).1.length) ∧
      (coreMachine core).spent (fun _ => 1) used (states id) ≤ used := by
  dsimp only
  refine ⟨?_, core_run_trace core _ _, ?_, unit_account_le_budget (coreMachine core) _ _⟩
  · rw [ScheduledFrontier.execute_reservation, ordered_frontier_walk]
    rfl
  · rw [core_spent_is_charge, charge_unit]

/-! ## Constructed variable administration and retained occurrence clocks -/

abbrev LatencyState (core : MachineCore Term) := core.State × Nat

/-- Independent transition judgment for inserting a finite administrative
phase before each actual computational occurrence. A missing original edge
remains stuck, even if the phase count is positive. -/
inductive LatencyStep (core : MachineCore Term) (delay : core.State → Nat) :
    LatencyState core → LatencyState core → Prop where
  | administrative {state next : core.State} (moving : core.StepRel state next) (remaining : Nat) :
      LatencyStep core delay (state, remaining + 1) (state, remaining)
  | computational {state next : core.State} (moving : core.StepRel state next) :
      LatencyStep core delay (state, 0) (next, delay next)

abbrev latencyCore (core : MachineCore Term) (delay : core.State → Nat) : MachineCore Term where
  State := LatencyState core
  load term := let state := core.load term; (state, delay state)
  step pair := match core.step pair.1 with
    | none => none
    | some next =>
        if pair.2 = 0 then some (next, delay next) else some (pair.1, pair.2 - 1)

theorem latency_step_iff (core : MachineCore Term) (delay : core.State → Nat)
    (state next : LatencyState core) :
    (latencyCore core delay).StepRel state next ↔ LatencyStep core delay state next := by
  constructor
  · rcases state with ⟨state, remaining⟩
    intro stepped
    change (match core.step state with
      | none => none
      | some next => if remaining = 0 then some (next, delay next)
          else some (state, remaining - 1)) = some next at stepped
    cases found : core.step state with
    | none => simp only [found, reduceCtorEq] at stepped
    | some following =>
        cases remaining with
        | zero =>
            simp only [found, if_true, Option.some.injEq] at stepped
            subst next
            exact .computational found
        | succ remaining =>
            simp only [found, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel,
              Option.some.injEq] at stepped
            subst next
            exact .administrative found remaining
  · intro derivation
    cases derivation with
    | administrative moving remaining =>
        change core.step _ = some _ at moving
        simp only [MachineCore.StepRel, latencyCore, moving, Nat.add_one_ne_zero,
          if_false, Nat.add_sub_cancel]
    | computational moving =>
        change core.step _ = some _ at moving
        simp only [MachineCore.StepRel, latencyCore, moving, if_true]

theorem latency_final_iff (core : MachineCore Term) (delay : core.State → Nat)
    (state : LatencyState core) : (latencyCore core delay).Final state ↔ core.Final state.1 := by
  cases state with
  | mk state remaining =>
      cases found : core.step state <;> cases remaining <;>
        simp [MachineCore.Final, latencyCore, found]

/-- Only the inserted positive-count phase is administrative. Original
computational occurrences remain computational even if their endpoints coincide. -/
theorem latency_read_step (core : MachineCore Term) (delay : core.State → Nat)
    {state next : LatencyState core} (stepped : LatencyStep core delay state next) :
    (next.1 = state.1 ∧ next.2 < state.2) ∨ core.StepRel state.1 next.1 := by
  cases stepped with
  | administrative _ remaining => exact .inl ⟨rfl, by omega⟩
  | computational moving => exact .inr moving

theorem latency_positive_phase_decreases (core : MachineCore Term) (delay : core.State → Nat)
    {state next : LatencyState core} (stepped : LatencyStep core delay state next)
    (positive : 0 < state.2) : next.2 < state.2 := by
  cases stepped with
  | administrative _ remaining => omega
  | computational _ => simp only at positive; omega

theorem latency_no_infinite_administration (core : MachineCore Term)
    (delay : core.State → Nat) (states : Nat → LatencyState core)
    (administrative : ∀ index, LatencyStep core delay (states index) (states (index + 1)) ∧
      0 < (states index).2) : False := by
  have decreases : ∀ index, (states (index + 1)).2 < (states index).2 := by
    intro index
    exact latency_positive_phase_decreases core delay (administrative index).1
      (administrative index).2
  have bounds : ∀ index, (states index).2 + index ≤ (states 0).2 := by
    intro index
    induction index with
    | zero => omega
    | succ index ih => have dropped := decreases index; omega
  have impossible := bounds ((states 0).2 + 1)
  omega

/-- Every bounded target prefix reads back an authorized finite source prefix.
This is the backward/no-invention side; no boundary-clock premise is needed. -/
theorem latency_prefix_readback (core : MachineCore Term) (delay : core.State → Nat)
    (fuel : Nat) (state : LatencyState core) :
    ∃ used, used ≤ fuel ∧
      walk core used state.1 = (walk (latencyCore core delay) fuel state).1 := by
  have readStep : ∀ state next, (latencyCore core delay).step state = some next →
      next.1 = state.1 ∨ core.step state.1 = some next.1 := by
    intro state next stepped
    rcases latency_read_step core delay ((latency_step_iff core delay state next).mp stepped) with
      ⟨unchanged, _⟩ | computed
    · exact .inl unchanged
    · exact .inr computed
  obtain ⟨used, bound, readback⟩ := core.runSlice_decode_stuttering
    (latencyCore core delay) Prod.fst readStep fuel state
  have sourceEndpoint := congrArg (fun result : core.State × Nat => result.1) readback
  refine ⟨used, bound.trans ((latencyCore core delay).runSlice_used_le fuel state), ?_⟩
  calc
    walk core used state.1 = (core.runSlice used state.1).1 := walk_runSlice core used state.1
    _ = ((latencyCore core delay).runSlice fuel state).1.1 := sourceEndpoint
    _ = (walk (latencyCore core delay) fuel state).1 :=
      congrArg (fun result : LatencyState core => result.1)
        (walk_runSlice (latencyCore core delay) fuel state).symm

theorem latency_walk_block (core : MachineCore Term) (delay : core.State → Nat)
    {state next : core.State} (moving : core.StepRel state next) (remaining : Nat) :
    walk (latencyCore core delay) (remaining + 1) (state, remaining) = (next, delay next) := by
  change core.step state = some next at moving
  induction remaining with
  | zero => simp only [walk, latencyCore, moving, if_true]
  | succ remaining ih =>
      simpa only [walk, latencyCore, moving, Nat.add_one_ne_zero, if_false,
        Nat.add_sub_cancel] using ih

/-- The common machine interface observes original computational occurrences.
Only the independently specified positive-count latency phase is silent. -/
def latencyMachine (core : MachineCore Term) (delay : core.State → Nat) :
    Machine (LatencyState core) (Occurrence core.State) Empty Empty where
  step state := match core.step state.1 with
    | none => none
    | some next => if state.2 = 0 then
        some (.publish [(state.1, next)] (next, delay next))
      else some (.silent (state.1, state.2 - 1))

theorem latency_machine_block (core : MachineCore Term) (delay : core.State → Nat)
    {state next : core.State} (moving : core.StepRel state next) (remaining : Nat) :
    (latencyMachine core delay).run (remaining + 1) (state, remaining) =
      ([(state, next)], .exhausted (next, delay next)) := by
  change core.step state = some next at moving
  induction remaining with
  | zero => simp only [Machine.run, latencyMachine, moving, if_true, List.append_nil]
  | succ remaining ih =>
      simpa only [Machine.run, latencyMachine, moving, Nat.add_one_ne_zero, if_false,
        Nat.add_sub_cancel] using ih

theorem latency_machine_rank (core : MachineCore Term) (delay : core.State → Nat)
    {state next : LatencyState core}
    (silent : (latencyMachine core delay).step state = some (.silent next)) :
    next.2 < state.2 := by
  rcases state with ⟨state, remaining⟩
  cases found : core.step state with
  | none => simp only [latencyMachine, found, reduceCtorEq] at silent
  | some following =>
      cases remaining with
      | zero => simp only [latencyMachine, found, if_true, Option.some.injEq, reduceCtorEq] at silent
      | succ remaining =>
          simp only [latencyMachine, found, Nat.add_one_ne_zero, if_false,
            Nat.add_sub_cancel, Option.some.injEq, Transition.silent.injEq] at silent
          subst next
          omega

/-- The independent core slice counts every target primitive in a block. -/
theorem latency_slice_block (core : MachineCore Term) (delay : core.State → Nat)
    {state next : core.State} (moving : core.StepRel state next) (remaining : Nat) :
    (latencyCore core delay).runSlice (remaining + 1) (state, remaining) =
      ((next, delay next), remaining + 1) := by
  change core.step state = some next at moving
  induction remaining with
  | zero => simp only [MachineCore.runSlice, latencyCore, moving, if_true]
  | succ remaining ih =>
      have advanced : (latencyCore core delay).step (state, remaining + 1) =
          some (state, remaining) := by
        simp only [latencyCore, moving, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      rw [MachineCore.runSlice, advanced]
      simp only [ih]

theorem core_spent_runSlice (core : MachineCore Term) (fuel : Nat) (state : core.State) :
    (coreMachine core).spent (fun _ => 1) fuel state = (core.runSlice fuel state).2 := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases found : core.step state with
      | none => simp only [Machine.spent, coreMachine, found, Option.map_none, MachineCore.runSlice]
      | some next =>
          simpa only [Machine.spent, coreMachine, found, Option.map_some, MachineCore.runSlice,
            Nat.add_comm] using congrArg (1 + ·) (ih next)

theorem latency_machine_spent (core : MachineCore Term) (delay : core.State → Nat)
    (price : LatencyState core → Nat) (fuel : Nat) (state : LatencyState core) :
    (latencyMachine core delay).spent price fuel state =
      (coreMachine (latencyCore core delay)).spent price fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      rcases state with ⟨state, remaining⟩
      dsimp only [latencyMachine, coreMachine, latencyCore] at ih
      cases found : core.step state <;> cases remaining <;>
        simp only [Machine.spent, latencyMachine, coreMachine, latencyCore, found,
          Option.map_none, Option.map_some, if_true, Nat.add_one_ne_zero, if_false,
          Nat.add_sub_cancel, ih]

/-- The executable clock sums precisely the inserted phase and original edge
at each reached source state. It stops charging when the source has no edge. -/
def boundaryClock (core : MachineCore Term) (delay : core.State → Nat) :
    Nat → LatencyState core → Nat
  | 0, _ => 0
  | fuel + 1, (state, remaining) => match core.step state with
      | none => 0
      | some next => remaining + 1 + boundaryClock core delay fuel (next, delay next)

/-- A derived clock realizes the exact original computational trace, while the
exhausted residual retains the target's current phase. Boundary exhaustion is
intentionally separate from polling a successful answer or a stuck state. -/
theorem latency_machine_boundary (core : MachineCore Term) (delay : core.State → Nat)
    (fuel : Nat) (state : LatencyState core) :
    (latencyMachine core delay).run (boundaryClock core delay fuel state) state =
      (((coreMachine core).run fuel state.1).1,
        .exhausted (walk (latencyCore core delay) (boundaryClock core delay fuel state) state)) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      rcases state with ⟨state, remaining⟩
      cases found : core.step state with
      | none => simp only [boundaryClock, found, Machine.run, core_missing_step core found, walk]
      | some next =>
          simp only [boundaryClock, found]
          rw [(latencyMachine core delay).run_add (remaining + 1)
            (boundaryClock core delay fuel (next, delay next)),
            latency_machine_block core delay found]
          simp only [Machine.continueRun]
          rw [ih (next, delay next), walk_add (latencyCore core delay) (remaining + 1)
            (boundaryClock core delay fuel (next, delay next)),
            latency_walk_block core delay found]
          simp only [Machine.run, core_step core found, List.singleton_append]

theorem boundaryClock_debit (core : MachineCore Term) (delay : core.State → Nat)
    (fuel : Nat) (state : LatencyState core) :
    ((latencyCore core delay).runSlice (boundaryClock core delay fuel state) state).2 =
      boundaryClock core delay fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      rcases state with ⟨state, remaining⟩
      cases found : core.step state with
      | none => simp only [boundaryClock, found, MachineCore.runSlice]
      | some next =>
          simp only [boundaryClock, found]
          rw [(latencyCore core delay).runSlice_add (remaining + 1)
            (boundaryClock core delay fuel (next, delay next)), latency_slice_block core delay found]
          exact congrArg (remaining + 1 + ·) (ih (next, delay next))

theorem latency_instruction_debit (core : MachineCore Term) (delay : core.State → Nat)
    (fuel : Nat) (state : LatencyState core) :
    (latencyMachine core delay).spent (fun _ => 1) (boundaryClock core delay fuel state) state =
      boundaryClock core delay fuel state := by
  rw [latency_machine_spent, core_spent_runSlice, boundaryClock_debit]

/-- Independently executed target primitives read back the finite source run.
The constructed clock depends on the actual branch, not a global multiplier. -/
theorem boundaryClock_readback (core : MachineCore Term) (delay : core.State → Nat)
    (fuel : Nat) (state : LatencyState core) :
    (walk (latencyCore core delay) (boundaryClock core delay fuel state) state).1 =
      walk core fuel state.1 := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      rcases state with ⟨state, remaining⟩
      cases found : core.step state with
      | none => simp only [boundaryClock, found, walk]
      | some next =>
          simp only [boundaryClock, found]
          rw [walk_add (latencyCore core delay) (remaining + 1)
            (boundaryClock core delay fuel (next, delay next)) (state, remaining),
            latency_walk_block core delay found]
          simpa only [walk, found] using ih (next, delay next)

theorem boundaryClock_add (core : MachineCore Term) (delay : core.State → Nat)
    (first second : Nat) (state : LatencyState core) :
    boundaryClock core delay (first + second) state = boundaryClock core delay first state +
      boundaryClock core delay second
        (walk (latencyCore core delay) (boundaryClock core delay first state) state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, boundaryClock, walk]
  | succ first ih =>
      rcases state with ⟨state, remaining⟩
      rw [show first + 1 + second = (first + second) + 1 by omega]
      cases found : core.step state with
      | none => cases second <;> simp only [boundaryClock, found, walk, Nat.zero_add]
      | some next =>
          simp only [boundaryClock, found]
          rw [walk_add (latencyCore core delay) (remaining + 1)
            (boundaryClock core delay first (next, delay next)) (state, remaining),
            latency_walk_block core delay found, ih]
          omega

theorem boundaryClock_bound (core : MachineCore Term) (delay : core.State → Nat)
    (bound : Nat) (bounded : ∀ state, delay state ≤ bound)
    (fuel : Nat) (state : LatencyState core) (reserved : state.2 ≤ bound) :
    boundaryClock core delay fuel state ≤ (bound + 1) * fuel := by
  induction fuel generalizing state with
  | zero => simp only [boundaryClock, Nat.mul_zero]; exact Nat.le_refl _
  | succ fuel ih =>
      rcases state with ⟨state, remaining⟩
      cases found : core.step state with
      | none => simp only [boundaryClock, found]; exact Nat.zero_le _
      | some next =>
          have rest := ih (next, delay next) (bounded next)
          simp only [boundaryClock, found, Nat.mul_succ]
          omega

theorem ordered_core_halts_have_no_successors (core : MachineCore Term) :
    ∀ state, (orderedCore core).halted state = true → (orderedCore core).step state = [] := by
  intro state halted
  have stopped := (ordered_halted_iff core state).mp halted
  change core.step state = none at stopped
  simp only [orderedCore, stopped, Option.toList_none]

/-- The reserved-frontier bridge is constructed for every deterministic core,
every finite source observation, every finite frontier and every latency profile.
It preserves ordered slots and repeated occurrences under any sufficient schedule. -/
theorem scheduled_latency_frontier (core : MachineCore Term) (delay : core.State → Nat)
    {n : Nat} (fuel : Nat) (states : Fin n → LatencyState core)
    (schedule : List (ScheduledFrontier.Command n))
    (enough : ∀ id, boundaryClock core delay fuel (states id) ≤
      Mettapedia.Machines.Cursor.Scheduling.allocation id schedule) :
    List.Forall₂ (fun source target => target.1 = source)
      ((orderedCore core).runFrontier fuel (List.ofFn (fun id => (states id).1)))
      (ScheduledFrontier.view (ScheduledFrontier.execute (orderedCore (latencyCore core delay))
        schedule (ScheduledFrontier.reserve (fun id => boundaryClock core delay fuel (states id))
          (fun id => [states id])))) := by
  apply ScheduledFrontier.source_frontier_related (ordered_core_halts_have_no_successors core)
  · intro id
    rw [ordered_frontier_walk core, ordered_frontier_walk (latencyCore core delay)]
    simp only [List.map_cons, List.map_nil]
    exact .cons (boundaryClock_readback core delay fuel (states id)) .nil
  · exact enough

/-- The complete target frontier's readback is exactly the source frontier,
including its order and multiplicity, rather than merely the same support. -/
theorem scheduled_latency_readback (core : MachineCore Term) (delay : core.State → Nat)
    {n : Nat} (fuel : Nat) (states : Fin n → LatencyState core)
    (schedule : List (ScheduledFrontier.Command n))
    (enough : ∀ id, boundaryClock core delay fuel (states id) ≤
      Mettapedia.Machines.Cursor.Scheduling.allocation id schedule) :
    (ScheduledFrontier.view (ScheduledFrontier.execute (orderedCore (latencyCore core delay))
      schedule (ScheduledFrontier.reserve (fun id => boundaryClock core delay fuel (states id))
        (fun id => [states id])))).map Prod.fst =
      (orderedCore core).runFrontier fuel (List.ofFn (fun id => (states id).1)) := by
  have matching := scheduled_latency_frontier core delay fuel states schedule enough
  have graph : ∀ {first : List core.State} {second : List (LatencyState core)},
      List.Forall₂ (fun source target => target.1 = source) first second →
        second.map Prod.fst = first := by
    intro first second matched
    induction matched with
    | nil => rfl
    | cons head _ ih => simp only [List.map_cons, head, ih]
  exact graph matching

/-- A concrete finite scheduler realizes the derived clocks; no arbitrary
finite-realization premise remains in this deterministic-core instance. -/
theorem scheduled_latency_realization (core : MachineCore Term) (delay : core.State → Nat)
    {n : Nat} (fuel : Nat) (states : Fin n → LatencyState core) :
    ∃ schedule : List (ScheduledFrontier.Command n),
      (ScheduledFrontier.view (ScheduledFrontier.execute (orderedCore (latencyCore core delay))
        schedule (ScheduledFrontier.reserve (fun id => boundaryClock core delay fuel (states id))
          (fun id => [states id])))).map Prod.fst =
        (orderedCore core).runFrontier fuel (List.ofFn (fun id => (states id).1)) := by
  obtain ⟨count, bound⟩ := Finite.exists_le (fun id => boundaryClock core delay fuel (states id))
  refine ⟨ScheduledFrontier.rounds 1 count, scheduled_latency_readback core delay fuel states _ ?_⟩
  intro id
  simpa only [ScheduledFrontier.rounds_allocation, Nat.mul_one] using bound id

/-- Any declared observation factoring through the original state has the same
ordered occurrences at the realized boundary. This includes the old answer
observers; the delay count is not itself preserved by such an observation. -/
theorem scheduled_latency_observation (core : MachineCore Term) (delay : core.State → Nat)
    {Answer : Type} (observe : core.State → Option Answer)
    {n : Nat} (fuel : Nat) (states : Fin n → LatencyState core)
    (schedule : List (ScheduledFrontier.Command n))
    (enough : ∀ id, boundaryClock core delay fuel (states id) ≤
      Mettapedia.Machines.Cursor.Scheduling.allocation id schedule) :
    (ScheduledFrontier.view (ScheduledFrontier.execute (orderedCore (latencyCore core delay))
      schedule (ScheduledFrontier.reserve (fun id => boundaryClock core delay fuel (states id))
        (fun id => [states id])))).filterMap (fun state => observe state.1) =
      ((orderedCore core).runFrontier fuel (List.ofFn (fun id => (states id).1))).filterMap observe := by
  have statesAgree := scheduled_latency_readback core delay fuel states schedule enough
  have observationsAgree := congrArg (List.filterMap observe) statesAgree
  simpa only [List.filterMap_map, Function.comp_def] using observationsAgree

/-- Fair service reaches each finite source observation, even when a retained
source branch runs forever. Reaching the reservation is not a final-answer
assertion, and completed slots remain at their exact observation boundary. -/
theorem fair_scheduled_latency (core : MachineCore Term) (delay : core.State → Nat)
    {n : Nat} (fuel : Nat) (states : Fin n → LatencyState core)
    (schedule : Nat → ScheduledFrontier.Command n)
    (fair : Mettapedia.Machines.Cursor.FairObservation.FairAllocation schedule) :
    ∃ horizon, ∀ extra,
      (ScheduledFrontier.view (ScheduledFrontier.execute (orderedCore (latencyCore core delay))
        (Mettapedia.Machines.Cursor.FairObservation.schedulePrefix schedule (horizon + extra))
        (ScheduledFrontier.reserve (fun id => boundaryClock core delay fuel (states id))
          (fun id => [states id])))).map Prod.fst =
        (orderedCore core).runFrontier fuel (List.ofFn (fun id => (states id).1)) := by
  obtain ⟨horizon, stable⟩ := ScheduledFrontier.fair_eventually_boundary
    (orderedCore (latencyCore core delay)) schedule fair
    (fun id => boundaryClock core delay fuel (states id)) (fun id => [states id])
  refine ⟨horizon, fun extra => scheduled_latency_readback core delay fuel states _ ?_⟩
  apply (ScheduledFrontier.reservation_complete_iff (orderedCore (latencyCore core delay))
    _ _ _).mp
  intro id
  rw [stable extra]

end Mettapedia.Machines.ProductiveCoreOrdered
