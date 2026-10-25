import Mettapedia.Machines.TrialRollback

/-!
# Cardinality from independent reversible trials

Each candidate is tested under the same store. The implementation executes
writes and restores their recorded undo entries; the reference independently
starts each test from the original store. Equality includes the final store,
so a surrounding trial retains every binding it had before counting.

The failure control models a nonlinear pattern: an early candidate binds its
cell and then fails, while a later candidate succeeds only if that write was
undone. Saving allocation lengths alone does not restore the cell.

These are pure binding-store and count laws. Native allocation, conditional
trailing coverage, candidate coverage, logical-update snapshots, errors and
budget admission remain implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TrialCounting

open MarkedUndoLog TrialRollback

variable {Slot Payload Candidate : Type*} [DecidableEq Slot]

def writeAll (writes : List (Slot × Payload)) (store : Slot → Payload) : Slot → Payload :=
  writes.foldl (fun state entry => restore entry state) store

theorem recordWrites_values (writes : List (Slot × Payload)) (store : Slot → Payload) :
    (recordWrites writes store).1 = writeAll writes store := by
  induction writes generalizing store with
  | nil => rfl
  | cons entry rest ih =>
      simpa only [recordWrites, writeAll, List.foldl_cons] using
        ih (restore entry store)

def countFresh (writes : Candidate → (Slot → Payload) → List (Slot × Payload))
    (accepts : Candidate → (Slot → Payload) → Bool) (store : Slot → Payload)
    (candidates : List Candidate) : Nat :=
  candidates.countP (fun candidate => accepts candidate (writeAll (writes candidate store) store))

def countByUndo (writes : Candidate → (Slot → Payload) → List (Slot × Payload))
    (accepts : Candidate → (Slot → Payload) → Bool) (store : Slot → Payload) :
    List Candidate → Nat × (Slot → Payload)
  | [] => (0, store)
  | candidate :: rest =>
      let attempted := recordWrites (writes candidate store) store
      let accepted := if accepts candidate attempted.1 then 1 else 0
      let resumed := rollback attempted.2 attempted.1
      let later := countByUndo writes accepts resumed rest
      (accepted + later.1, later.2)

theorem count_and_store_eq (writes : Candidate → (Slot → Payload) → List (Slot × Payload))
    (accepts : Candidate → (Slot → Payload) → Bool) (store : Slot → Payload)
    (candidates : List Candidate) :
    countByUndo writes accepts store candidates = (countFresh writes accepts store candidates, store) := by
  induction candidates with
  | nil => simp [countByUndo, countFresh]
  | cons candidate rest ih =>
      simp only [countByUndo]
      rw [rollback_recordWrites, ih]
      simp only [recordWrites_values, countFresh, List.countP_cons]
      split <;> simp_all [Nat.add_comm]

theorem surrounding_bindings_survive
    (writes : Candidate → (Slot → Payload) → List (Slot × Payload))
    (accepts : Candidate → (Slot → Payload) → Bool) (store : Slot → Payload)
    (candidates : List Candidate) (slot : Slot) :
    (countByUndo writes accepts store candidates).2 slot = store slot := by
  rw [count_and_store_eq]

theorem split_counts (writes : Candidate → (Slot → Payload) → List (Slot × Payload))
    (accepts : Candidate → (Slot → Payload) → Bool) (store : Slot → Payload)
    (first second : List Candidate) :
    (countByUndo writes accepts store (first ++ second)).1 =
      (countByUndo writes accepts store first).1 + (countByUndo writes accepts store second).1 := by
  simp only [count_and_store_eq, countFresh, List.countP_append]

theorem duplicate_candidates_count_twice
    (writes : Candidate → (Slot → Payload) → List (Slot × Payload))
    (accepts : Candidate → (Slot → Payload) → Bool) (store : Slot → Payload)
    (candidate : Candidate)
    (accepted : accepts candidate (writeAll (writes candidate store) store) = true) :
    (countByUndo writes accepts store [candidate, candidate]).1 = 2 := by
  simp [count_and_store_eq, countFresh, accepted]

namespace Controls

def writes (candidate : Nat) (store : Bool → Option Nat) : List (Bool × Option Nat) :=
  if store false = none then [(false, some candidate)] else []

def accepts (candidate : Nat) (store : Bool → Option Nat) : Bool :=
  candidate == 2 && store false == some 2

def countWithoutUndo (store : Bool → Option Nat) : List Nat → Nat
  | [] => 0
  | candidate :: rest =>
      let afterWrite := writeAll (writes candidate store) store
      (if accepts candidate afterWrite then 1 else 0) + countWithoutUndo afterWrite rest

theorem failed_attempt_cannot_poison_next :
    (countByUndo writes accepts (fun _ => none) [1, 2]).1 = 1 ∧
    (countByUndo writes accepts (fun _ => none) [1, 2]).2 false = none ∧
    countWithoutUndo (fun _ => none) [1, 2] = 0 := by decide

theorem existing_outer_binding_is_preserved :
    (countByUndo writes accepts (fun _ => some 2) [1, 2, 2]).1 = 2 ∧
    (countByUndo writes accepts (fun _ => some 2) [1, 2, 2]).2 false = some 2 := by decide

end Controls

end Mettapedia.Machines.TrialCounting
