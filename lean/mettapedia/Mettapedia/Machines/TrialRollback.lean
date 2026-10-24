import Mettapedia.Machines.MarkedUndoLog

/-!
# Trial writes and rollback of activation slots

A trial may allocate its first cell before it creates any choice frame.
Consequently an empty initial cell frontier does not mean an inactive trial.
Each slot write records its previous payload; a successful nested trial keeps
its records for the surrounding trial. Restoring just the cell frontier is
insufficient, as the final counterexample demonstrates.

This is a transition-level law. It does not verify native code or allocation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TrialRollback

open MarkedUndoLog

variable {Slot Payload : Type*} [DecidableEq Slot]

/-- Execute writes, recording the complete old value before each write. -/
def recordWrites (writes : List (Slot × Payload)) (store : Slot → Payload) :
    (Slot → Payload) × List (Slot × Payload) :=
  match writes with
  | [] => (store, [])
  | (key, value) :: rest =>
      let later := recordWrites rest (restore (key, value) store)
      (later.1, (key, store key) :: later.2)

theorem rollback_recordWrites (writes : List (Slot × Payload))
    (store : Slot → Payload) :
    rollback (recordWrites writes store).2 (recordWrites writes store).1 = store := by
  induction writes generalizing store with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      change restore (key, store key)
        (rollback (recordWrites rest (restore (key, value) store)).2
          (recordWrites rest (restore (key, value) store)).1) = store
      rw [ih]
      funext query
      by_cases same : query = key <;> simp [restore, same]

/-- Committing an inner trial keeps its undo records until the outer trial
commits. Concatenating chronological records gives the original outer store. -/
theorem rollback_nested (outer inner : List (Slot × Payload))
    (store : Slot → Payload) :
    let first := recordWrites outer store
    let second := recordWrites inner first.1
    rollback (first.2 ++ second.2) second.1 = store := by
  dsimp
  rw [rollback_append, rollback_recordWrites, rollback_recordWrites]

/-- Every occupied activation slot refers to a live cell. -/
def SlotsValid (frontier : Nat) (store : Slot → Option Nat) : Prop :=
  ∀ slot cell, store slot = some cell → cell < frontier

/-- Slot rollback together with frontier rollback preserves collector safety,
including a trial whose initial frontier is zero. -/
theorem rollback_preserves_slots (frontier : Nat) (store : Slot → Option Nat)
    (valid : SlotsValid frontier store) (writes : List (Slot × Option Nat)) :
    SlotsValid frontier
      (rollback (recordWrites writes store).2 (recordWrites writes store).1) := by
  rw [rollback_recordWrites]
  exact valid

example : SlotsValid 0 (fun (_ : Bool) => none) := by
  intro slot cell impossible
  cases impossible

/-- This is the discarded-cell fault: resetting the frontier without undoing
the first slot store leaves a reference to cell zero when no cells are live. -/
example : ¬ SlotsValid 0
    (recordWrites [(false, some 0)] (fun (_ : Bool) => none)).1 := by
  intro valid
  have impossible := valid false 0 (by rfl)
  exact Nat.not_lt_zero _ impossible

example : rollback
    (recordWrites [(false, some 0)] (fun (_ : Bool) => none)).2
    (recordWrites [(false, some 0)] (fun (_ : Bool) => none)).1 false = none := by
  rw [rollback_recordWrites]

#print axioms rollback_recordWrites
#print axioms rollback_nested
#print axioms rollback_preserves_slots

end Mettapedia.Machines.TrialRollback
