import Mettapedia.Computability.ExecutionSpace
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Physical stack growth along original TM2 executions

A command's maximal number of syntactic pushes bounds the cells it can add
in one actual macrostep. The maximum over finite labels therefore bounds
both the endpoint and peak stack footprint at the transition states of every
finite execution.

Cells alone do not bound bits when an internal stack alphabet is infinite.
A finite-alphabet representation must be supplied for a bit-space reading.
The statements here count physical stack cells, including temporary stacks.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.StackMachineSpaceGrowth

open Turing StateTransition
open ExecutionSpace
open scoped BigOperators

universe u v w x
variable {Key : Type u} {Alphabet : Key → Type v} {Label : Type w} {Registers : Type x}

/-- Maximal pushes along one syntactic command branch. A `goto` ends the
macrostep; its target command is charged at the next executed transition. -/
def pushCount : TM2.Stmt Alphabet Label Registers → Nat
  | .push _ _ rest => pushCount rest + 1
  | .peek _ _ rest | .pop _ _ rest | .load _ rest => pushCount rest
  | .branch _ yes no => max (pushCount yes) (pushCount no)
  | .goto _ | .halt => 0

section Statement

variable [DecidableEq Key] [Fintype Key]

theorem pushed_cells (contents : ∀ key, List (Alphabet key)) (key : Key) (value : Alphabet key) :
    (∑ slot, (Function.update contents key (value :: contents key) slot).length) =
      (∑ slot, (contents slot).length) + 1 := by
  calc
    (∑ slot, (Function.update contents key (value :: contents key) slot).length) =
        ∑ slot, ((contents slot).length + if slot = key then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro slot _
      by_cases same : slot = key
      · subst slot
        simp
      · simp [same]
    _ = (∑ slot, (contents slot).length) + 1 := by
      rw [Finset.sum_add_distrib]
      simp

theorem popped_cells_le (contents : ∀ key, List (Alphabet key)) (key : Key) :
    (∑ slot, (Function.update contents key (contents key).tail slot).length) ≤
      ∑ slot, (contents slot).length := by
  apply Finset.sum_le_sum
  intro slot _
  by_cases same : slot = key
  · subst slot
    simp
  · simp [Function.update_of_ne same]

/-- Count growth against the actual `TM2.stepAux` stack mutation, including
all sequential operations inside a single macrostep. -/
theorem stepAux_cells_le (statement : TM2.Stmt Alphabet Label Registers)
    (registers : Registers) (contents : ∀ key, List (Alphabet key)) :
    (∑ key, ((TM2.stepAux statement registers contents).stk key).length) ≤
      (∑ key, (contents key).length) + pushCount statement := by
  induction statement generalizing registers contents with
  | push key value rest ih =>
      simp only [TM2.stepAux, pushCount]
      have growth := ih registers (Function.update contents key (value registers :: contents key))
      rw [pushed_cells] at growth
      omega
  | peek key update rest ih =>
      exact ih _ contents
  | pop key update rest ih =>
      have growth := ih (update registers (contents key).head?)
        (Function.update contents key (contents key).tail)
      exact growth.trans (Nat.add_le_add_right (popped_cells_le contents key) (pushCount rest))
  | load update rest ih => exact ih _ contents
  | branch condition yes no yesIH noIH =>
      cases selected : condition registers with
      | false =>
          simp only [TM2.stepAux, selected, Bool.cond_false, pushCount]
          exact (noIH registers contents).trans (Nat.add_le_add_left (le_max_right _ _) _)
      | true =>
          simp only [TM2.stepAux, selected, Bool.cond_true, pushCount]
          exact (yesIH registers contents).trans (Nat.add_le_add_left (le_max_left _ _) _)
  | goto label => simp [TM2.stepAux, pushCount]
  | halt => simp [TM2.stepAux, pushCount]

end Statement

/-- A computable bound from every actual authored label's command. -/
def machinePushBound (machine : FinTM2) : Nat :=
  (@Finset.univ machine.Λ machine.ΛFin).sup (fun label => pushCount (machine.m label))

theorem command_le_machinePushBound (machine : FinTM2) (label : machine.Λ) :
    pushCount (machine.m label) ≤ machinePushBound machine := by
  let := machine.ΛFin
  exact Finset.le_sup (f := fun selected : machine.Λ => pushCount (machine.m selected)) (Finset.mem_univ label)

/-- Every successful original transition adds at most the fixed machine
push bound to the complete physical stack footprint. -/
theorem step_cells_le (machine : FinTM2) (before after : machine.Cfg)
    (advanced : machine.step before = some after) :
    stackCells machine after ≤ stackCells machine before + machinePushBound machine := by
  let := machine.kFin
  rcases before with ⟨label, registers, contents⟩
  cases label with
  | none => cases advanced
  | some label =>
      have same : TM2.stepAux (machine.m label) registers contents = after := Option.some.inj advanced
      rw [← same]
      exact (stepAux_cells_le (machine.m label) registers contents).trans
        (Nat.add_le_add_left (command_le_machinePushBound machine label) _)

theorem next_footprint_le (machine : FinTM2) (state : Option machine.Cfg) :
    footprint (stackCells machine) (state.bind machine.step) ≤
      footprint (stackCells machine) state + machinePushBound machine := by
  cases state with
  | none => exact Nat.zero_le _
  | some before =>
      change (machine.step before).elim 0 (stackCells machine) ≤
        stackCells machine before + machinePushBound machine
      cases advanced : machine.step before with
      | none => exact Nat.zero_le _
      | some after => exact step_cells_le machine before after advanced

/-- Every finite prefix, including halted or refusing prefixes, has peak
physical storage bounded by its actual number of transitions. -/
theorem peak_le (machine : FinTM2) (steps : Nat) (state : Option machine.Cfg) :
    peak machine.step (stackCells machine) steps state ≤
      footprint (stackCells machine) state + machinePushBound machine * steps := by
  induction steps generalizing state with
  | zero => simp [peak]
  | succ steps ih =>
      rw [peak]
      apply max_le
      · exact Nat.le_add_right _ _
      · have tail := ih (state.bind machine.step)
        have advanced := next_footprint_le machine state
        rw [Nat.mul_succ]
        omega

/-- The endpoint bound is obtained from the same finite execution prefix,
without an independently supplied storage account. -/
theorem iterate_footprint_le (machine : FinTM2) (steps : Nat) (state : Option machine.Cfg) :
    footprint (stackCells machine) ((fun next => next.bind machine.step)^[steps] state) ≤
      footprint (stackCells machine) state + machinePushBound machine * steps :=
  (endpoint_le_peak machine.step (stackCells machine) steps state).trans (peak_le machine steps state)

theorem initial_cells (machine : FinTM2) (input : List (machine.Γ machine.k₀)) :
    stackCells machine (initList machine input) = input.length := by
  let := machine.kFin
  unfold stackCells
  have contents : (fun key => ((initList machine input).stk key).length) =
      fun key => if key = machine.k₀ then input.length else 0 := by
    funext key
    by_cases same : key = machine.k₀
    · subst key
      simp [initList]
    · simp [initList, same]
  rw [contents]
  simp

/-- The entire peak, including scratch stacks and released intermediate
storage, is bounded by the real execution time. -/
theorem runPeak_le (machine : FinTM2)
    {input : List (machine.Γ machine.k₀)} {output : List (machine.Γ machine.k₁)}
    {time : Nat} (run : TM2OutputsInTime machine input (some output) time) :
    runPeak machine run ≤ input.length + machinePushBound machine * time := by
  have bound := peak_le machine run.steps (some (initList machine input))
  simp only [footprint, Option.elim_some, initial_cells] at bound
  exact bound.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ run.steps_le_m) _)

/-- A machine cannot produce more output cells than its input plus the
pushes paid for by its actual executed macrosteps. -/
theorem output_length_le (machine : FinTM2)
    {input : List (machine.Γ machine.k₀)} {output : List (machine.Γ machine.k₁)}
    {time : Nat} (run : TM2OutputsInTime machine input (some output) time) :
    output.length ≤ input.length + machinePushBound machine * time :=
  (output_length_le_runPeak machine run).trans (runPeak_le machine run)

namespace Controls

private def batch : TM2.Stmt (fun _ : Unit => Bool) Unit Unit :=
  .push () (fun _ => true) (.push () (fun _ => true) (.push () (fun _ => false) .halt))

private def machine : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m := fun _ => batch

private def empty : machine.Cfg := initList machine []
private def full : machine.Cfg := haltList machine [false, true, true]

/-- One original macrostep can perform several sequential pushes. -/
theorem three_pushes_in_one_transition : machine.step empty = some full := by
  change some (TM2.stepAux batch () (fun _ => [])) = some full
  congr 1

def threePushRun : TM2OutputsInTime machine [] (some [false, true, true]) 1 := by
  refine ⟨⟨1, ?_⟩, le_rfl⟩
  change machine.step empty = some full
  exact three_pushes_in_one_transition

theorem syntactic_bound_counts_all_three_pushes : machinePushBound machine = 3 := by decide

theorem executed_output_and_peak_attain_bound :
    ([false, true, true] : List Bool).length = 3 ∧
      runPeak machine threePushRun = 3 ∧ machinePushBound machine * threePushRun.steps = 3 := by
  refine ⟨rfl, ?_, rfl⟩
  change max 0 (stackCells machine full) = 3
  rfl

/-- Assuming only one added cell per macrostep is false for the retained
statement semantics. The syntactic machine constant is necessary. -/
theorem one_cell_per_macrostep_is_false :
    ¬ ([false, true, true] : List Bool).length ≤ ([] : List Bool).length + threePushRun.steps := by decide

theorem branch_bound_uses_larger_authored_path :
    pushCount (.branch (fun _ : Unit => false) batch
      (.push () (fun _ => true) (.halt : TM2.Stmt (fun _ : Unit => Bool) Unit Unit))) = 3 := by decide

theorem pop_does_not_add_cells (word : List Bool) :
    (∑ key : Unit,
      ((TM2.stepAux (.pop () (fun _ _ => ()) (.halt : TM2.Stmt (fun _ : Unit => Bool) Unit Unit))
        () (fun _ => word)).stk key).length) ≤ word.length := by
  simp

theorem halting_does_not_add_cells :
    footprint (stackCells machine) ((some full).bind machine.step) = 0 := rfl

/-- The original output bound also applies when an execution prefix already
starts after halt; no fabricated stack cells are charged to refused steps. -/
theorem halted_prefix_has_no_extra_peak :
    peak machine.step (stackCells machine) 7 (some full) = 3 := by decide

end Controls

end Mettapedia.Computability.StackMachineSpaceGrowth
