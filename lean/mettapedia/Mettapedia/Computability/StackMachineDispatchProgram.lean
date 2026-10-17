import Mettapedia.Computability.StackMachineComposition

/-!
# Executable status-dispatch table

The table takes only the physical keys, registers and original subroutine
table. Its equality with the original finite status dispatcher lets native
execution avoid enumeration of a composite machine's register states.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.StackMachineComposition.Dispatch.Programs
open Turing Turing.TM2.Stmt

variable {Key Label State : Type} {Cells : Key → Type}

/-- Original dispatch instructions with the source table supplied directly. -/
def body (inputKey outputKey : Key) (initialState : State) (main : Label)
    (accept : Cells inputKey → Bool) (refused : List (Cells outputKey))
    (source : Label → TM2.Stmt Cells Label State) :
    Phase Label → TM2.Stmt Cells (Phase Label) (State × Option (Cells inputKey))
  | .run label => StackMachineRegisters.extend Phase.run (source label)
  | .read => pop inputKey (fun state value => (state.1, value))
      (branch (fun state => state.2.any accept)
        (load (fun state => (state.1, none)) (goto fun _ => .run main))
        (goto fun _ => .discard))
  | .discard => pop inputKey (fun state value => (state.1, value))
      (branch (fun state => state.2.isSome) (goto fun _ => .discard)
        (refused.foldl (fun rest symbol => push outputKey (fun _ => symbol) rest)
          (load (fun _ => (initialState, none)) halt)))

private theorem lift_eq (program : FinTM2) (statement : program.Stmt) :
    lift program statement = StackMachineRegisters.extend Phase.run statement := by
  induction statement <;> simp_all only [lift, StackMachineRegisters.extend]

private theorem emit_eq (program : FinTM2) (word : List (program.Γ program.k₁))
    (rest : TM2.Stmt program.Γ (Phase program.Λ) (Dispatch.State program)) :
    Dispatch.emit program word rest =
      word.foldl (fun rest symbol => push program.k₁ (fun _ => symbol) rest) rest := by
  induction word generalizing rest with
  | nil => rfl
  | cons head tail ih => exact ih _

theorem body_eq (program : FinTM2) (accept : program.Γ program.k₀ → Bool)
    (refused : List (program.Γ program.k₁)) :
    (machine program accept refused).m =
      body program.k₀ program.k₁ program.initialState program.main accept refused program.m := by
  funext phase
  cases phase <;> simp only [machine, body, lift_eq, emit_eq]

end Mettapedia.Computability.StackMachineComposition.Dispatch.Programs
