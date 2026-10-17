import Mathlib.Computability.TuringMachine.Computable

/-!
# Reusing an earned physical statement

The cache retains one statement computed from a machine label. Its stored
proof earns the exact instruction. Reusing that statement when the label
agrees preserves the complete instruction table and each original TM2 step.
-/
set_option autoImplicit false
namespace Mettapedia.Computability.PhysicalStatementCache
open Turing

structure StatementCache {Key : Type} (Cells : Key → Type) (Labels Registers : Type)
    (table : Labels → TM2.Stmt Cells Labels Registers) where
  label : Labels
  statement : TM2.Stmt Cells Labels Registers
  earned : statement=table label

def remember {Key : Type} (Cells : Key → Type) (Labels Registers : Type)
    (table : Labels → TM2.Stmt Cells Labels Registers) (label : Labels) : StatementCache Cells Labels Registers table :=
  ⟨label,table label,rfl⟩

def memoized {Key : Type} {Cells : Key → Type} {Labels Registers : Type} [DecidableEq Labels]
    (table : Labels → TM2.Stmt Cells Labels Registers) (cache : Option (StatementCache Cells Labels Registers table)) :
    Labels → TM2.Stmt Cells Labels Registers := fun label =>
  match cache with
  | none => table label
  | some saved => if label=saved.label then saved.statement else table label

theorem memoized_eq {Key : Type} {Cells : Key → Type} {Labels Registers : Type} [DecidableEq Labels]
    (table : Labels → TM2.Stmt Cells Labels Registers) (cache : Option (StatementCache Cells Labels Registers table)) :
    memoized table cache=table := by
  funext label
  cases cache with
  | none => rfl
  | some saved =>
    change (if label=saved.label then saved.statement else table label)=table label
    split
    · rename_i same
      rw [same]
      exact saved.earned
    · rfl

theorem memoized_step_eq {Key : Type} {Cells : Key → Type} {Labels Registers : Type}
    [DecidableEq Key] [DecidableEq Labels]
    (table : Labels → TM2.Stmt Cells Labels Registers) (cache : Option (StatementCache Cells Labels Registers table)) :
    TM2.step (memoized table cache)=TM2.step table := by rw [memoized_eq]

end Mettapedia.Computability.PhysicalStatementCache
