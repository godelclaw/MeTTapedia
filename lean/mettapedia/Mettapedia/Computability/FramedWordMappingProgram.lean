import Mettapedia.Computability.FramedWordMapping

/-!
# Original framed mapper table without finite-enumeration arguments

The exposed table is equal to the qualified machine's original command table.
Native evaluation can supply component tables and physical keys directly,
without constructing finite register-state enumerations.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.FramedWordMapping.Programs
open Turing Turing.TM2.Stmt
variable {SourceKey Label SourceState : Type} {SourceCells : SourceKey → Type}
  (inputKey outputKey : SourceKey)
local notation "Input" => SourceCells inputKey
local notation "Output" => SourceCells outputKey
local notation "ExtraRegisters" => Option (Option Input) × Option Input × Option Output × Option (Option Output)
local notation "Registers" => SourceState × ExtraRegisters
local notation "Cells" => StackMachineRegisters.withStackAlphabet
  (StackMachineRegisters.withStackAlphabet
    (StackMachineRegisters.withStackAlphabet
      (StackMachineRegisters.withStackAlphabet SourceCells (Option Output)) (Option Output)) Input) (Option Input)

def lifted (source : Label → TM2.Stmt SourceCells Label SourceState) (label : Label) : TM2.Stmt Cells (Phase Label) Registers :=
  StackMachineRegisters.withStack (Cell := Option Input) id
    (StackMachineRegisters.withStack (Cell := Input) id
      (StackMachineRegisters.withStack (Cell := Option Output) id
        (StackMachineRegisters.withStack (Cell := Option Output) id
          (StackMachineRegisters.returning (Extra := ExtraRegisters)
            Phase.run (fun _ => Phase.collect) (source label)))))

def body (initialState : SourceState) (main : Label)
    (inputDefault : Input) (outputDefault : Output)
    (source : Label → TM2.Stmt SourceCells Label SourceState) (phase : Phase Label) :
    TM2.Stmt Cells (Phase Label) Registers :=
  match phase with
  | .scan => pop none (fun state cell => (state.1, cell, state.2.2))
      (branch (fun state => state.2.1.isNone) (goto fun _ => .reverse)
        (branch (fun state => (state.2.1.getD none).isSome)
          (push (some none) (fun state => (state.2.1.getD none).getD inputDefault)
            (goto fun _ => .copy)) (goto fun _ => .restore)))
  | .copy => pop none (fun state cell => (state.1, cell, state.2.2))
      (branch (fun state => state.2.1.isNone) (goto fun _ => .rejectTemporary)
        (branch (fun state => (state.2.1.getD none).isSome)
          (push (some none) (fun state => (state.2.1.getD none).getD inputDefault)
            (goto fun _ => .copy)) (goto fun _ => .restore)))
  | .restore => pop (some none) (fun state cell => (state.1, state.2.1, cell, state.2.2.2))
      (branch (fun state => state.2.2.1.isSome)
        (push (some (some (some (some inputKey)))) (fun state => state.2.2.1.getD inputDefault) (goto fun _ => .restore))
        (load (fun _ => (initialState, none, none, none, none)) (goto fun _ => .run main)))
  | .run label => lifted inputKey outputKey source label
  | .collect => pop (some (some (some (some outputKey))))
      (fun state cell => (state.1, state.2.1, state.2.2.1, cell, state.2.2.2.2))
      (branch (fun state => state.2.2.2.1.isSome)
        (push (some (some none)) (fun state => some (state.2.2.2.1.getD outputDefault))
          (goto fun _ => .collect))
        (push (some (some none)) (fun _ => none)
          (load (fun _ => (initialState, none, none, none, none)) (goto fun _ => .scan))))
  | .reverse => pop (some (some none))
      (fun state cell => (state.1, state.2.1, state.2.2.1, state.2.2.2.1, cell))
      (branch (fun state => state.2.2.2.2.isSome)
        (push (some (some (some none))) (fun state => state.2.2.2.2.getD none) (goto fun _ => .reverse))
        (load (fun _ => (initialState, none, none, none, none)) halt))
  | .rejectTemporary => pop (some none)
      (fun state cell => (state.1, state.2.1, cell, state.2.2.2))
      (branch (fun state => state.2.2.1.isSome) (goto fun _ => .rejectTemporary)
        (goto fun _ => .rejectAccumulator))
  | .rejectAccumulator => pop (some (some none))
      (fun state cell => (state.1, state.2.1, state.2.2.1, state.2.2.2.1, cell))
      (branch (fun state => state.2.2.2.2.isSome) (goto fun _ => .rejectAccumulator)
        (load (fun _ => (initialState, none, none, none, none)) halt))


theorem body_eq (program : FinTM2) [Fintype (program.Γ program.k₁)]
    [Inhabited (program.Γ program.k₀)] [Inhabited (program.Γ program.k₁)] :
    body program.k₀ program.k₁ program.initialState program.main default default program.m =
      statement program := by
  funext phase
  cases phase <;> rfl

end Mettapedia.Computability.FramedWordMapping.Programs
