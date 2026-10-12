import Mettapedia.GSLT.Distinction.OrderedSimulationSpans

/-!
# Controls for ordered simulations as span relations

* **A lockstep instance** (`chain_simulation`, `chain_future`).  A two-state
  system and a relabelled copy on another carrier are related by a map; the
  span reading transfers a future formula about the successor at position
  zero.
* **Fibre matching is more than the modal laws** (`merged_control`).  A state
  with two equal successors and a state with one satisfy both endpoint source
  laws, yet no ordered simulation relates them, and they have different
  numbers of successor occurrences.
* **Stuttering misaligns lockstep frontiers** (`stutter_branches`,
  `stutter_misaligns`, `stutter_realigns`).  Each branch of the source is
  matched within one or two target steps, the slow branch through an
  administrative state related to the same source state.  After one source
  step and two target steps the frontiers are not related position by
  position, although they are after one target step, and again at
  completion.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.OrderedSimulationSpansControls

open Mettapedia.GSLT.Distinction.SpanTransport

/-! ## A lockstep instance -/

/-- One step to a halted state. -/
def single : OrderedSystem Bool where
  step
    | false => [true]
    | true => []
  halted state := state

/-- The same shape on another carrier. -/
def chain : OrderedSystem (Option Unit) where
  step
    | none => [some ()]
    | some () => []
  halted state := state.isSome

def relabel : Bool → Option Unit
  | false => none
  | true => some ()

theorem chain_simulation : OrderedSimulation single chain (fun state state' => state' = relabel state) :=
  OrderedSimulation.ofMap relabel (by intro state; cases state <;> rfl) (by intro state; cases state <;> rfl)

/-- The successor at position zero halts. -/
def haltsNext : Tense Bool ℕ :=
  .future 0 (.atom true)

/-- **The formula agrees on related states**; it holds at the start. -/
theorem chain_future :
    (Tense.sat single.occurrences haltsNext false ↔ Tense.sat chain.occurrences haltsNext none) ∧
      Tense.sat single.occurrences haltsNext false :=
  ⟨chain_simulation.future_related (.future 0 (.atom true)) rfl,
    ⟨⟨false, 0, by decide⟩, rfl, rfl, rfl⟩⟩

/-! ## Fibre matching is more than the modal laws -/

/-- Two equal successors. -/
def doubled : OrderedSystem Bool where
  step
    | false => [true, true]
    | true => []
  halted state := state

theorem doubled_next (occurrence : doubled.Occurrence) : occurrence.next = true := by
  obtain ⟨state, position, inRange⟩ := occurrence
  cases state with
  | false =>
      rcases position with _ | _ | position
      · rfl
      · rfl
      · simp [doubled] at inRange
  | true => simp [doubled] at inRange

theorem single_next (occurrence : single.Occurrence) : occurrence.next = true := by
  obtain ⟨state, position, inRange⟩ := occurrence
  cases state with
  | false =>
      rcases position with _ | position
      · rfl
      · simp [single] at inRange
  | true => simp [single] at inRange

theorem doubled_state (occurrence : doubled.Occurrence) : occurrence.state = false := by
  obtain ⟨state, position, inRange⟩ := occurrence
  cases state with
  | false => rfl
  | true => simp [doubled] at inRange

theorem single_state (occurrence : single.Occurrence) : occurrence.state = false := by
  obtain ⟨state, position, inRange⟩ := occurrence
  cases state with
  | false => rfl
  | true => simp [single] at inRange

/-- **Both endpoint source laws hold, no ordered simulation exists, and the
numbers of successor occurrences differ.** -/
theorem merged_control :
    SourceForth doubled.occurrenceSpan single.occurrenceSpan Eq ∧
      SourceBack doubled.occurrenceSpan single.occurrenceSpan Eq ∧
      ¬ OrderedSimulation doubled single Eq ∧
      (∃ occurrence : doubled.Occurrence, occurrence.position = 1) ∧
      ¬ ∃ occurrence : single.Occurrence, occurrence.position = 1 := by
  refine ⟨?_, ?_, ?_, ⟨⟨false, 1, by decide⟩, rfl⟩, ?_⟩
  · rintro x _ rfl occurrence rfl
    refine ⟨⟨false, 0, by decide⟩, (doubled_state occurrence).symm, ?_⟩
    exact (doubled_next occurrence).trans (single_next _).symm
  · rintro x _ rfl occurrence rfl
    refine ⟨⟨false, 0, by decide⟩, (single_state occurrence).symm, ?_⟩
    exact (doubled_next _).trans (single_next occurrence).symm
  · intro simulation
    have lengths := (simulation.step (state := false) (state' := false) rfl).length_eq
    simp [doubled, single] at lengths
  · rintro ⟨⟨state, position, inRange⟩, rfl⟩
    cases state <;> simp [single] at inRange

/-! ## Stuttering misaligns lockstep frontiers -/

inductive Source where
  | root
  | left
  | right
  | leftDone
  | rightDone
  deriving DecidableEq

inductive Target where
  | root
  | left
  | rightAdmin
  | right
  | leftDone
  | rightDone
  deriving DecidableEq

def source : OrderedSystem Source where
  step
    | .root => [.left, .right]
    | .left => [.leftDone]
    | .right => [.rightDone]
    | _ => []
  halted
    | .leftDone => true
    | .rightDone => true
    | _ => false

/-- The right branch takes an administrative step first. -/
def target : OrderedSystem Target where
  step
    | .root => [.left, .rightAdmin]
    | .left => [.leftDone]
    | .rightAdmin => [.right]
    | .right => [.rightDone]
    | _ => []
  halted
    | .leftDone => true
    | .rightDone => true
    | _ => false

/-- The stuttering relation: the right source state is related to the
administrative target state and to its successor. -/
def stutter : Source → Target → Prop
  | .root, .root => True
  | .left, .left => True
  | .right, .rightAdmin => True
  | .right, .right => True
  | .leftDone, .leftDone => True
  | .rightDone, .rightDone => True
  | _, _ => False

/-- **Each branch is matched within one or two target steps**: related states
agree on halting, and either both have no successors, or the source successors
are related position by position to the target frontier after one or two
steps. -/
theorem stutter_branches :
    ∀ state state', stutter state state' →
      target.halted state' = source.halted state ∧
        ((source.step state = [] ∧ target.step state' = []) ∨
          ∃ k, 1 ≤ k ∧ k ≤ 2 ∧
            List.Forall₂ stutter (source.step state) (target.runFrontier k [state'])) := by
  intro state state' related
  cases state <;> cases state' <;> simp only [stutter] at related
  · exact ⟨rfl, Or.inr ⟨1, le_rfl, by omega, .cons trivial (.cons trivial .nil)⟩⟩
  · exact ⟨rfl, Or.inr ⟨1, le_rfl, by omega, .cons trivial .nil⟩⟩
  · exact ⟨rfl, Or.inr ⟨2, by omega, le_rfl, .cons trivial .nil⟩⟩
  · exact ⟨rfl, Or.inr ⟨1, le_rfl, by omega, .cons trivial .nil⟩⟩
  · exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- **After one source step and two target steps the frontiers are not related
position by position.** -/
theorem stutter_misaligns :
    ¬ List.Forall₂ stutter (source.runFrontier 1 [.root]) (target.runFrontier (2 * 1) [.root]) := by
  intro related
  cases related with
  | cons head _ => exact head

/-- They are after one target step, and at completion. -/
theorem stutter_realigns :
    List.Forall₂ stutter (source.runFrontier 1 [.root]) (target.runFrontier 1 [.root]) ∧
      List.Forall₂ stutter (source.runFrontier 2 [.root]) (target.runFrontier (2 * 2) [.root]) :=
  ⟨.cons trivial (.cons trivial .nil), .cons trivial (.cons trivial .nil)⟩

/-- Equal numeric budgets need not expose equal prefixes under different
schedules. The unserviced right branch remains present in the depth-first view. -/
theorem depth_first_retains_unserviced_alternative :
    source.expandFirst^[2] [.root] = [.leftDone, .right] ∧
      source.runFrontier 2 [.root] = [.leftDone, .rightDone] ∧
      source.expandFirst^[2] [.root] ≠ source.runFrontier 2 [.root] := by
  decide +kernel

/-- Separate equal-looking source occurrences stay separate throughout the
common depth-first simulation, not only once they have both completed. -/
theorem depth_first_duplicate_transport (count : Nat) :
    chain.expandFirst^[count] [none, none] =
      (single.expandFirst^[count] [false, false]).map relabel :=
  OrderedSimulation.expandFirst_iterate_map (source := single) (target := chain) relabel
    (by intro state; cases state <;> rfl)
    (by intro state; cases state <;> rfl) count [false, false]

/-- A nonhalting dead end cannot disappear from the frontier. In particular
it cannot expose a later answer as though the first occurrence had finished. -/
theorem depth_first_preserves_stuck :
    let blocked : OrderedSystem Bool := { step := fun _ => [], halted := id }
    blocked.expandFirst [false, true] = [false, true] ∧
      blocked.expandFirst [false, true] ≠ [true] := by
  decide +kernel

/-! ## Independently serviced retained boundaries -/

open ScheduledFrontier

def branchStates (id : Fin 2) : List Target :=
  if id = 0 then [.left] else [.rightAdmin]

def branchClocks (id : Fin 2) : Nat := if id = 0 then 1 else 2

def branchReservation : Slots 2 Target := reserve branchClocks branchStates

def firstServices : List (Command 2) := [(0, 1), (1, 1)]
def lastService : List (Command 2) := [(1, 1)]

theorem unequal_administration_retains_complete_residual :
    execute target firstServices branchReservation 0 = ⟨1, 0, [.leftDone]⟩ ∧
      execute target firstServices branchReservation 1 = ⟨1, 1, [.right]⟩ := ⟨rfl, rfl⟩

theorem completed_branch_cannot_overrun :
    execute target (firstServices ++ [(0, 19)]) branchReservation =
      execute target firstServices branchReservation := by
  rw [execute_append]
  funext id
  fin_cases id <;> rfl

theorem unequal_boundaries_resume_exactly :
    execute target (firstServices ++ lastService) branchReservation =
      execute target lastService (execute target firstServices branchReservation) :=
  execute_append target firstServices lastService branchReservation

theorem unequal_branches_preserve_order :
    view (execute target (firstServices ++ lastService) branchReservation) =
      [.leftDone, .rightDone] := rfl

theorem boundary_accounts_are_local :
    (execute target (firstServices ++ lastService) branchReservation 0).worked = 1 ∧
      (execute target (firstServices ++ lastService) branchReservation 1).worked = 2 := ⟨rfl, rfl⟩

theorem different_completion_chronology_has_the_same_ordered_boundary :
    execute target [(1, 2), (0, 1)] branchReservation =
      execute target (firstServices ++ lastService) branchReservation := by
  apply execute_eq_of_allocation_eq
  intro id
  fin_cases id <;> rfl

theorem remaining_administration_is_not_a_final_answer :
    (execute target firstServices branchReservation 1).remaining = 1 ∧
      target.halted .right = false := ⟨rfl, rfl⟩

theorem zero_service_cannot_finish_a_positive_reservation (count : Nat) :
    (execute target (rounds 0 count) branchReservation 1).remaining = 2 := by
  rw [zero_quantum_preserves_reservations]
  rfl

theorem unserviced_occurrence_stays_pending (fuel : Nat) :
    (execute target [(0, fuel)] branchReservation 1).remaining = 2 := by
  rw [execute_at]
  rfl

/-- Halting flags alone do not authorize distributing an ordered frontier:
this deliberately inconsistent profile has a halted state with a successor. -/
def activeHalted : OrderedSystem Bool where
  step
    | false => [true]
    | true => [false]
  halted state := state

theorem local_halting_requires_the_stability_premise :
    activeHalted.runFrontier 1 [true, false] = [false, true] ∧
      (activeHalted.runFrontier 1 [true] ++ activeHalted.runFrontier 1 [false]) = [true, true] :=
  ⟨rfl, rfl⟩

/-- A concrete ongoing fair policy for the two retained occurrence owners. -/
def twoSlotRoundRobin (index : Nat) : Command 2 := (⟨index % 2, Nat.mod_lt _ (by omega)⟩, 1)

theorem twoSlotRoundRobin_allocation (id : Fin 2) (roundCount : Nat) :
    Mettapedia.Machines.Cursor.Scheduling.allocation id
      (Mettapedia.Machines.Cursor.FairObservation.schedulePrefix twoSlotRoundRobin (2 * roundCount)) =
        roundCount := by
  induction roundCount with
  | zero => rfl
  | succ roundCount ih =>
      rw [show 2 * (roundCount + 1) = (2 * roundCount + 1) + 1 by omega,
        Mettapedia.Machines.Cursor.FairObservation.schedulePrefix,
        Mettapedia.Machines.Cursor.FairObservation.allocation_append,
        Mettapedia.Machines.Cursor.FairObservation.schedulePrefix,
        Mettapedia.Machines.Cursor.FairObservation.allocation_append, ih]
      fin_cases id <;>
        simp [Mettapedia.Machines.Cursor.Scheduling.allocation, twoSlotRoundRobin, Nat.add_mod]

theorem twoSlotRoundRobin_fair :
    Mettapedia.Machines.Cursor.FairObservation.FairAllocation twoSlotRoundRobin := by
  intro id demand
  exact ⟨2 * demand, by rw [twoSlotRoundRobin_allocation]⟩

theorem fair_unequal_branches_eventually_reach_their_exact_boundaries :
    ∃ horizon, ∀ extra,
      view (execute target
        (Mettapedia.Machines.Cursor.FairObservation.schedulePrefix twoSlotRoundRobin (horizon + extra))
        branchReservation) = [.leftDone, .rightDone] := by
  obtain ⟨horizon, settled⟩ := fair_eventually_boundary target twoSlotRoundRobin
    twoSlotRoundRobin_fair branchClocks branchStates
  refine ⟨horizon, fun extra => ?_⟩
  change view (execute target _ (reserve branchClocks branchStates)) = _
  rw [settled extra]
  rfl

end Mettapedia.GSLT.Distinction.OrderedSimulationSpansControls
