import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Peak space along an actual machine execution

`peak` traverses the same states as `EvalsTo`; it is not a freely assigned
space account. Sequential runs take the maximum of their peaks, including
their shared endpoint. For stack machines, the footprint counts all live
stack cells. Encoding those cells as bits requires a finite alphabet on each
stack and its own representation bound. Native allocator space is separate.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.ExecutionSpace

open StateTransition Turing
open scoped BigOperators

variable {State : Type*}

def footprint (measure : State → Nat) (state : Option State) : Nat :=
  state.elim 0 measure

/-- Include both endpoint states of a prefix of the original transition run. -/
def peak (step : State → Option State) (measure : State → Nat) : Nat → Option State → Nat
  | 0, state => footprint measure state
  | n + 1, state => max (footprint measure state) (peak step measure n (state.bind step))

theorem initial_le_peak (step : State → Option State) (measure : State → Nat)
    (n : Nat) (state : Option State) : footprint measure state ≤ peak step measure n state := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

theorem endpoint_le_peak (step : State → Option State) (measure : State → Nat)
    (n : Nat) (state : Option State) :
    footprint measure ((fun s => s.bind step)^[n] state) ≤ peak step measure n state := by
  induction n generalizing state with
  | zero => exact le_rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact (ih _).trans (le_max_right _ _)

/-- Sequential prefixes share one boundary state; peak storage uses maximum,
whereas step counts use addition. -/
theorem peak_add (step : State → Option State) (measure : State → Nat)
    (n m : Nat) (state : Option State) :
    peak step measure (n + m) state = max (peak step measure n state)
      (peak step measure m ((fun s => s.bind step)^[n] state)) := by
  induction n generalizing state with
  | zero =>
      simpa only [Nat.zero_add, peak, Function.iterate_zero_apply] using
        (max_eq_right (initial_le_peak step measure m state)).symm
  | succ n ih =>
      rw [Nat.succ_add, peak, ih, peak, Function.iterate_succ_apply, max_assoc]

theorem peak_join {step : State → Option State} (measure : State → Nat)
    {first middle : State} {last : Option State}
    (left : EvalsTo step first (some middle)) (right : EvalsTo step middle last) :
    peak step measure (left.steps + right.steps) (some first) =
      max (peak step measure left.steps (some first))
        (peak step measure right.steps (some middle)) := by
  rw [peak_add]
  have boundary := left.evals_in_steps
  change ((fun s : Option State => s.bind step)^[left.steps] (some first)) =
    some middle at boundary
  rw [boundary]

/-- Every stack contributes to the footprint, including temporary stacks. -/
def stackCells (machine : FinTM2) (state : machine.Cfg) : Nat :=
  @Finset.sum machine.K Nat _ (@Finset.univ machine.K machine.kFin)
    (fun key => (state.stk key).length)

theorem stack_le_cells (machine : FinTM2) (state : machine.Cfg) (key : machine.K) :
    (state.stk key).length ≤ stackCells machine state := by
  let := machine.kFin
  unfold stackCells
  exact Finset.single_le_sum (fun k _ => Nat.zero_le (state.stk k).length) (Finset.mem_univ key)

/-- Space is extracted from the actual number of executed transitions. -/
def runPeak (machine : FinTM2) {input : List (machine.Γ machine.k₀)}
    {output : List (machine.Γ machine.k₁)} {time : Nat}
    (run : TM2OutputsInTime machine input (some output) time) : Nat :=
  peak machine.step (stackCells machine) run.steps (some (initList machine input))

/-- A completed output must occupy physical cells at the final state. -/
theorem output_length_le_runPeak (machine : FinTM2)
    {input : List (machine.Γ machine.k₀)} {output : List (machine.Γ machine.k₁)}
    {time : Nat} (run : TM2OutputsInTime machine input (some output) time) :
    output.length ≤ runPeak machine run := by
  have endpoint := endpoint_le_peak machine.step (stackCells machine) run.steps
    (some (initList machine input))
  have stopped := run.evals_in_steps
  change ((fun s : Option machine.Cfg => s.bind machine.step)^[run.steps]
    (some (initList machine input))) = some (haltList machine output) at stopped
  rw [stopped] at endpoint
  have outputCells := stack_le_cells machine (haltList machine output) machine.k₁
  simp only [haltList, dite_true] at outputCells
  exact outputCells.trans endpoint

namespace Controls

/-- Release can reduce final storage while an earlier state fixes the peak. -/
def release (n : Nat) : Option Nat := if n = 0 then none else some (n - 1)

theorem released_storage_retains_peak : peak release id 4 (some 3) = 3 := by decide

/-- A zero-size final observation is not a zero-space execution. -/
theorem final_size_is_not_peak :
    footprint id ((fun s : Option Nat => s.bind release)^[4] (some 3)) = 0 ∧
      peak release id 4 (some 3) > 0 := by decide

end Controls

end Mettapedia.Computability.ExecutionSpace
