import Mettapedia.Computability.RetainedWordExecution

/-!
# Executing retained-word composition without enumerating control states

This presentation exposes the existing retained-word command table with its
original program as a parameter. It omits the finite-type enumeration data
from the executable arguments. The equality below connects it to the
unchanged machine used by the retained-word execution theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.RetainedWordExecution.Programs

open Turing Turing.TM2.Stmt

variable {Key Label Registers Tag : Type} {Cells : Key → Type}

abbrev AddedCells (inputKey : Key) := StackMachineRegisters.withStackAlphabet
  (StackMachineRegisters.withStackAlphabet
    (StackMachineRegisters.withStackAlphabet Cells (Cells inputKey)) (Cells inputKey))
  (Cells inputKey ⊕ Tag)

def body (inputKey outputKey : Key) (initial : Registers) (main : Label)
    (inputDefault : Cells inputKey) (tagDefault : Tag)
    (readTag : Cells outputKey → Tag)
    (source : Label → TM2.Stmt Cells Label Registers) :
    Phase Label → TM2.Stmt (AddedCells (Cells := Cells) (Tag := Tag) inputKey)
      (Phase Label) (Registers × Option (Cells inputKey) × Option (Cells outputKey) × Tag)
  | .scan => pop (some (some (some inputKey))) (fun state value => (state.1, value, state.2.2))
      (branch (fun state => state.2.1.isSome)
        (push (some none) (fun state => state.2.1.getD inputDefault)
          (push (some (some none)) (fun state => state.2.1.getD inputDefault)
            (goto fun _ => .scan)))
        (goto fun _ => .restore))
  | .restore => pop (some none) (fun state value => (state.1, value, state.2.2))
      (branch (fun state => state.2.1.isSome)
        (push (some (some (some inputKey))) (fun state => state.2.1.getD inputDefault)
          (goto fun _ => .restore))
        (load (fun state => (initial, none, none, state.2.2.2)) (goto fun _ => .run main)))
  | .run label =>
      StackMachineRegisters.withStack (Cell := Cells inputKey ⊕ Tag) id
        (StackMachineRegisters.withStack (Cell := Cells inputKey) id
          (StackMachineRegisters.withStack (Cell := Cells inputKey) id
            (StackMachineRegisters.returning
              (Extra := Option (Cells inputKey) × Option (Cells outputKey) × Tag)
              Phase.run (fun _ => Phase.read) (source label))))
  | .read => pop (some (some (some outputKey)))
      (fun state value => (state.1, state.2.1, value, state.2.2.2))
      (load (fun state => (state.1, state.2.1, state.2.2.1,
        state.2.2.1.elim tagDefault readTag)) (goto fun _ => .discard))
  | .discard => pop (some (some (some outputKey)))
      (fun state value => (state.1, state.2.1, value, state.2.2.2))
      (branch (fun state => state.2.2.1.isSome) (goto fun _ => .discard) (goto fun _ => .finish))
  | .finish => pop (some (some none)) (fun state value => (state.1, value, state.2.2))
      (branch (fun state => state.2.1.isSome)
        (push none (fun state => .inl (state.2.1.getD inputDefault)) (goto fun _ => .finish))
        (push none (fun state => .inr state.2.2.2)
          (load (fun _ => (initial, none, none, tagDefault)) halt)))

theorem body_eq (machine : FinTM2) [Fintype Tag] [Inhabited Tag]
    [Fintype (machine.Γ machine.k₁)] [Inhabited (machine.Γ machine.k₀)]
    (readTag : machine.Γ machine.k₁ → Tag) :
    body machine.k₀ machine.k₁ machine.initialState machine.main default default readTag machine.m =
      statement machine readTag := by
  funext phase
  cases phase <;> rfl

end Mettapedia.Computability.RetainedWordExecution.Programs
