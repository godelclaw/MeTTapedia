import Mettapedia.Computability.RegularLanguages.RegexPikeVM

/-!
# Logical reset of reusable regex storage

Physical buffer tails may contain prior frontiers. Only the live prefix is
observable. Replacing that prefix, clearing its length, and resetting the
first-visit memo supply the same input to the existing ordered executor as
fresh storage. This is a representation/initialization law, not C verification
or a proof about allocator success and pointer aliasing.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexWorkspace

open RegexTaggedGraph

universe u v w

structure Buffer (α : Type u) where
  cells : List α
  live : Nat

def Buffer.read {α : Type u} (buffer : Buffer α) : List α := buffer.cells.take buffer.live

def Buffer.clear {α : Type u} (buffer : Buffer α) : Buffer α := { buffer with live := 0 }

def Buffer.replace {α : Type u} (buffer : Buffer α) (values : List α) : Buffer α :=
  ⟨values ++ buffer.cells.drop values.length, values.length⟩

theorem read_clear {α : Type u} (buffer : Buffer α) : buffer.clear.read = [] := by
  simp [Buffer.read, Buffer.clear]

theorem read_replace {α : Type u} (buffer : Buffer α) (values : List α) :
    (buffer.replace values).read = values := by
  simp [Buffer.read, Buffer.replace]

theorem replace_retains_tail {α : Type u} (buffer : Buffer α) (values : List α) :
    (buffer.replace values).cells.drop values.length = buffer.cells.drop values.length := by
  simp [Buffer.replace]

/-- A previously visited PC cannot suppress a new search entry. The concrete
stale pending buffer is retained beyond its overwritten live prefix. -/
theorem closure_reinitialize {α : Type u} {Key : Type v} [DecidableEq Key]
    (key : α → Key) (children : α → List α) (emit : α → Bool)
    (fuel : Nat) (old : Buffer α) (entries : List α) (oldSeen : Finset Key) :
    firstVisits key children emit fuel (old.replace entries).read (oldSeen \ oldSeen) =
      firstVisits key children emit fuel entries ∅ := by
  rw [read_replace, Finset.sdiff_self]

/-- Capture-bearing threads, priority order, and incomplete outcomes are
preserved for the entire existing frontier driver, not just recognition. -/
theorem execute_reinitialize {α : Type u} {Key : Type v} {Tag : Type w} [DecidableEq Key]
    (key : α → Key) (epsilon : α → List α) (emit : α → Bool)
    (consume : α → List α) (accepts : α → Option Tag) (eligible : α → Bool)
    (closureFuel fuel : Nat) (old : Buffer α) (entries : List α) :
    RegexPikeVM.execute key epsilon emit consume accepts eligible closureFuel fuel
      (old.replace entries).read none =
    RegexPikeVM.execute key epsilon emit consume accepts eligible closureFuel fuel entries none := by
  rw [read_replace]

/-- Clearing the length does not require erasing unused physical cells. -/
example : (Buffer.clear (⟨[3, 7, 11], 2⟩ : Buffer Nat)).cells = [3, 7, 11] ∧
    (Buffer.clear (⟨[3, 7, 11], 2⟩ : Buffer Nat)).read = [] := by decide

/-- Retaining the old length instead is observably wrong. -/
example : (⟨[3, 7, 11], 2⟩ : Buffer Nat).read ≠ ([] : List Nat) := by decide

/-- A stale first-visit memo loses a real frontier occurrence. -/
example : firstVisits id (fun _ : Nat => []) (fun _ => true) 2 [3] {3} = some [] ∧
    firstVisits id (fun _ : Nat => []) (fun _ => true) 2 [3] ∅ = some [3] := by decide

#print axioms closure_reinitialize
#print axioms execute_reinitialize

end Mettapedia.Computability.RegularLanguages.RegexWorkspace
