import Mettapedia.Computability.StackMachineSpaceGrowth

/-!
# Peak stack cells inside executed TM2 commands

TM2 transitions execute a whole statement, which may push and then pop
temporary cells before returning. Transition-state peaks therefore omit some
storage. This refinement follows the same original primitive mutations and
selected branches inside each command. It also includes every configuration
between commands. The same syntactic push bound controls the refined peak.

This counts cells of the abstract stack machine, not native allocator bytes,
register encodings, or temporary objects created by an implementation of lists.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.StackMachineMicroSpace

open Turing StateTransition ExecutionSpace StackMachineSpaceGrowth
open scoped BigOperators

variable {Key Label Registers : Type}

section Statement

variable {Symbols : Key → Type} [DecidableEq Key] [Fintype Key]

/-- Follow the original primitive stack mutations and the actually selected
branch. A goto ends this command; its successor is charged by the next step. -/
def commandPeak : TM2.Stmt Symbols Label Registers → Registers →
    (∀ key, List (Symbols key)) → Nat
  | .push key value rest, registers, contents =>
      max (∑ key, (contents key).length)
        (commandPeak rest registers (Function.update contents key (value registers :: contents key)))
  | .peek key update rest, registers, contents =>
      commandPeak rest (update registers (contents key).head?) contents
  | .pop key update rest, registers, contents =>
      max (∑ key, (contents key).length)
        (commandPeak rest (update registers (contents key).head?)
          (Function.update contents key (contents key).tail))
  | .load update rest, registers, contents => commandPeak rest (update registers) contents
  | .branch condition yes no, registers, contents =>
      if condition registers then commandPeak yes registers contents
      else commandPeak no registers contents
  | .goto _, _, contents | .halt, _, contents => ∑ key, (contents key).length

theorem initial_le_commandPeak (statement : TM2.Stmt Symbols Label Registers)
    (registers : Registers) (contents : ∀ key, List (Symbols key)) :
    (∑ key, (contents key).length) ≤ commandPeak statement registers contents := by
  induction statement generalizing registers contents with
  | push => exact le_max_left _ _
  | peek key update rest ih => exact ih _ _
  | pop => exact le_max_left _ _
  | load update rest ih => exact ih _ _
  | branch condition yes no iy ino =>
      simp only [commandPeak]
      split
      · exact iy _ _
      · exact ino _ _
  | goto => exact le_rfl
  | halt => exact le_rfl

theorem endpoint_le_commandPeak (statement : TM2.Stmt Symbols Label Registers)
    (registers : Registers) (contents : ∀ key, List (Symbols key)) :
    (∑ key, ((TM2.stepAux statement registers contents).stk key).length) ≤
      commandPeak statement registers contents := by
  induction statement generalizing registers contents with
  | push key value rest ih => exact (ih _ _).trans (le_max_right _ _)
  | peek key update rest ih => exact ih _ _
  | pop key update rest ih => exact (ih _ _).trans (le_max_right _ _)
  | load update rest ih => exact ih _ _
  | branch condition yes no iy ino =>
      cases chosen : condition registers <;> simp only [TM2.stepAux, commandPeak, chosen]
      · exact ino _ _
      · exact iy _ _
  | goto => exact le_rfl
  | halt => exact le_rfl

/-- All temporary pushes are covered even if the command pops them before
the next transition state. -/
theorem commandPeak_le (statement : TM2.Stmt Symbols Label Registers)
    (registers : Registers) (contents : ∀ key, List (Symbols key)) :
    commandPeak statement registers contents ≤
      (∑ key, (contents key).length) + pushCount statement := by
  induction statement generalizing registers contents with
  | push key value rest ih =>
      simp only [commandPeak, pushCount]
      apply max_le (by omega)
      have bound := ih registers (Function.update contents key (value registers :: contents key))
      rw [pushed_cells] at bound
      omega
  | peek key update rest ih => exact ih _ _
  | pop key update rest ih =>
      simp only [commandPeak, pushCount]
      apply max_le (Nat.le_add_right _ _)
      exact (ih _ _).trans (Nat.add_le_add_right (popped_cells_le contents key) _)
  | load update rest ih => exact ih _ _
  | branch condition yes no iy ino =>
      simp only [commandPeak, pushCount]
      split
      · exact (iy _ _).trans (Nat.add_le_add_left (le_max_left _ _) _)
      · exact (ino _ _).trans (Nat.add_le_add_left (le_max_right _ _) _)
  | goto => simp [commandPeak, pushCount]
  | halt => simp [commandPeak, pushCount]

end Statement

/-- The next command's original execution, with halted states retaining their
current storage and absent states contributing zero. -/
def nextPeak (machine : FinTM2) (state : Option machine.Cfg) : Nat := by
  let := machine.kFin
  exact match state with
    | none => 0
    | some state => match state.l with
      | none => stackCells machine state
      | some label => commandPeak (machine.m label) state.var state.stk

theorem initial_le_nextPeak (machine : FinTM2) (state : Option machine.Cfg) :
    footprint (stackCells machine) state ≤ nextPeak machine state := by
  let := machine.kFin
  cases state with
  | none => exact le_rfl
  | some state =>
      cases found : state.l with
      | none => simp [nextPeak, footprint, found]
      | some label =>
          simpa only [footprint, Option.elim_some, nextPeak, found, stackCells] using
            initial_le_commandPeak (machine.m label) state.var state.stk

theorem nextPeak_le (machine : FinTM2) (state : Option machine.Cfg) :
    nextPeak machine state ≤ footprint (stackCells machine) state + machinePushBound machine := by
  let := machine.kFin
  cases state with
  | none => exact Nat.zero_le _
  | some state =>
      cases found : state.l with
      | none => simp [nextPeak, footprint, found]
      | some label =>
          simp only [nextPeak, found, footprint, Option.elim_some]
          exact (commandPeak_le (machine.m label) state.var state.stk).trans
            (Nat.add_le_add_left (command_le_machinePushBound machine label) _)

def prefixPeak (machine : FinTM2) : Nat → Option machine.Cfg → Nat
  | 0, state => footprint (stackCells machine) state
  | steps + 1, state => max (nextPeak machine state)
      (prefixPeak machine steps (state.bind machine.step))

theorem transition_peak_le (machine : FinTM2) (steps : Nat) (state : Option machine.Cfg) :
    peak machine.step (stackCells machine) steps state ≤ prefixPeak machine steps state := by
  induction steps generalizing state with
  | zero => exact le_rfl
  | succ steps ih =>
      exact max_le_max (initial_le_nextPeak machine state) (ih _)

theorem prefixPeak_le (machine : FinTM2) (steps : Nat) (state : Option machine.Cfg) :
    prefixPeak machine steps state ≤
      footprint (stackCells machine) state + machinePushBound machine * steps := by
  induction steps generalizing state with
  | zero => simp [prefixPeak]
  | succ steps ih =>
      simp only [prefixPeak, Nat.mul_succ]
      apply max_le
      · have bound := nextPeak_le machine state
        omega
      · have bound := ih (state.bind machine.step)
        have growth := next_footprint_le machine state
        omega

def runPeak (machine : FinTM2)
    {input : List (machine.Γ machine.k₀)} {output : List (machine.Γ machine.k₁)}
    {time : Nat} (run : TM2OutputsInTime machine input (some output) time) : Nat :=
  prefixPeak machine run.steps (some (initList machine input))

theorem runPeak_le (machine : FinTM2)
    {input : List (machine.Γ machine.k₀)} {output : List (machine.Γ machine.k₁)}
    {time : Nat} (run : TM2OutputsInTime machine input (some output) time) :
    runPeak machine run ≤ input.length + machinePushBound machine * time := by
  have bound := prefixPeak_le machine run.steps (some (initList machine input))
  simp only [footprint, Option.elim_some, initial_cells] at bound
  exact bound.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ run.steps_le_m) _)

theorem output_le_runPeak (machine : FinTM2)
    {input : List (machine.Γ machine.k₀)} {output : List (machine.Γ machine.k₁)}
    {time : Nat} (run : TM2OutputsInTime machine input (some output) time) :
    output.length ≤ runPeak machine run :=
  (output_length_le_runPeak machine run).trans
    (transition_peak_le machine run.steps (some (initList machine input)))

namespace Controls

private def temporary : TM2.Stmt (fun _ : Unit => Bool) Unit Unit :=
  .push () (fun _ => true) (.pop () (fun _ _ => ()) .halt)

private def machine : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := temporary

def temporaryRun : TM2OutputsInTime machine [] (some []) 1 := ⟨⟨1, rfl⟩, le_rfl⟩

/-- The actual command allocates one cell and releases it before halt. -/
theorem temporary_peak : runPeak machine temporaryRun = 1 := by decide

/-- The transition-state measurement misses that temporary cell. -/
theorem transition_peak_misses_temporary :
    ExecutionSpace.runPeak machine temporaryRun = 0 ∧
      ExecutionSpace.runPeak machine temporaryRun < runPeak machine temporaryRun := by decide

theorem zero_space_is_false : ¬ runPeak machine temporaryRun ≤ 0 := by decide

end Controls

end Mettapedia.Computability.StackMachineMicroSpace
