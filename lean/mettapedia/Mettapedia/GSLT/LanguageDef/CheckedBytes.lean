import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Lean.Elab.Tactic.Omega

/-!
# Byte-buffer permissions

A local array or allocated buffer has one owner. Read views may be copied;
write views are exclusive, with a suspended parent while a reborrow is live.
Roots identify allocations or the lifetime supplied by a view parameter.
Ancestors record suspended views, not arbitrary pointer reachability.

This is a sequential byte-buffer model. A native interface must realize its
declared lifetime, allocation, initialized-range and effect contracts. The
model is separate from general C pointer semantics and from graph ownership.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CheckedBytes

inductive Kind where
  | read | write | own | local
  deriving DecidableEq, Repr

def Kind.loan : Kind → Bool
  | .read | .write => true
  | .own | .local => false

def Kind.owner (kind : Kind) : Bool := !kind.loan

def Kind.writable (kind : Kind) : Bool := kind != .read

structure Binding where
  id : Nat
  kind : Kind
  root : Nat
  ancestors : List Nat := []
  deriving DecidableEq, Repr

structure State where
  cells : List Binding := []
  external : List Nat := []
  ownedResult : Bool := false
  borrowedResult : Option (Nat × Kind) := none
  deriving DecidableEq, Repr

def State.find (s : State) (id : Nat) : Option Binding :=
  s.cells.find? (fun binding => binding.id == id)

def State.erase (s : State) (id : Nat) : State :=
  { s with cells := s.cells.filter (fun binding => binding.id != id) }

def Alive (s : State) (root : Nat) : Prop :=
  root ∈ s.external ∨ ∃ binding ∈ s.cells, binding.kind.owner = true ∧ binding.root = root

instance (s : State) (root : Nat) : Decidable (Alive s root) := by
  unfold Alive
  infer_instance

def Ordered (s : State) : Prop :=
  ∀ binding ∈ s.cells, ∀ parent ∈ binding.ancestors, parent < binding.id

def Valid (s : State) : Prop :=
  (s.cells.map Binding.id).Nodup ∧ Ordered s ∧
  (∀ binding ∈ s.cells, binding.root ≤ binding.id ∧ Alive s binding.root ∧
    (binding.kind.owner = true → binding.ancestors = [])) ∧
  (∀ first ∈ s.cells, ∀ second ∈ s.cells,
    first.kind.owner = true → second.kind.owner = true →
    first.root = second.root → first.id = second.id)

instance (s : State) : Decidable (Valid s) := by
  unfold Valid Ordered
  infer_instance

/-- A parent view may be suspended by its descendants. Siblings cannot bypass
one another's permissions, even when their byte subranges are disjoint. -/
def CanAccess (s : State) (binding : Binding) (writing : Bool) : Prop :=
  binding ∈ s.cells ∧ Alive s binding.root ∧
  (writing = true → binding.kind.writable = true) ∧
  ∀ other ∈ s.cells, other.id ≠ binding.id → other.root = binding.root →
    other.kind.loan = true → other.id ∉ binding.ancestors →
    writing = false ∧ other.kind ≠ .write

instance (s : State) (binding : Binding) (writing : Bool) :
    Decidable (CanAccess s binding writing) := by
  unfold CanAccess
  infer_instance

def Unborrowed (s : State) (root : Nat) : Prop :=
  ∀ binding ∈ s.cells, binding.kind.loan = true → binding.root ≠ root

instance (s : State) (root : Nat) : Decidable (Unborrowed s root) := by
  unfold Unborrowed
  infer_instance

def NoChildren (s : State) (id : Nat) : Prop :=
  ∀ binding ∈ s.cells, binding.kind.loan = true → id ∉ binding.ancestors

instance (s : State) (id : Nat) : Decidable (NoChildren s id) := by
  unfold NoChildren
  infer_instance

def Fresh (s : State) (id : Nat) : Prop :=
  (∀ binding ∈ s.cells, binding.id < id ∧ binding.root < id ∧
    ∀ parent ∈ binding.ancestors, parent < id) ∧
  ∀ root ∈ s.external, root < id

instance (s : State) (id : Nat) : Decidable (Fresh s id) := by
  unfold Fresh
  infer_instance

theorem find_mem {s : State} {id : Nat} {binding : Binding}
    (found : s.find id = some binding) : binding ∈ s.cells ∧ binding.id = id := by
  exact ⟨List.mem_of_find?_eq_some found, by simpa using List.find?_some found⟩

theorem write_requires_writable {s : State} {binding : Binding}
    (access : CanAccess s binding true) : binding.kind.writable = true :=
  access.2.2.1 rfl

theorem access_has_live_root {s : State} {binding : Binding} {writing : Bool}
    (access : CanAccess s binding writing) : Alive s binding.root := access.2.1

theorem release_refused_with_loan {s : State} {root : Nat} {binding : Binding}
    (present : binding ∈ s.cells) (loan : binding.kind.loan = true)
    (same : binding.root = root) : ¬ Unborrowed s root := by
  intro unborrowed
  exact unborrowed binding present loan same

theorem parent_end_refused_with_child {s : State} {parent : Nat} {binding : Binding}
    (present : binding ∈ s.cells) (loan : binding.kind.loan = true)
    (child : parent ∈ binding.ancestors) : ¬ NoChildren s parent := by
  intro clear
  exact clear binding present loan child

theorem conflicting_loan_is_ancestor {s : State} {first second : Binding}
    {writing : Bool} (access : CanAccess s first writing)
    (present : second ∈ s.cells) (different : second.id ≠ first.id)
    (same : second.root = first.root) (loan : second.kind.loan = true)
    (conflict : writing = true ∨ second.kind = .write) :
    second.id ∈ first.ancestors := by
  by_contra absent
  obtain ⟨reads, shared⟩ := access.2.2.2 second present different same loan absent
  rcases conflict with writes | exclusive
  · simp [writes] at reads
  · exact shared exclusive

/-- Two separately usable views of one root cannot include a writable one.
Reborrowing is allowed because the parent is suspended, not independently usable. -/
theorem exclusive_access {s : State} {writer reader : Binding} {reading : Bool}
    (valid : Valid s) (write : CanAccess s writer true)
    (read : CanAccess s reader reading) (same : writer.root = reader.root) :
    writer.id = reader.id := by
  by_contra different
  have wmem := write.1
  have rmem := read.1
  have wkind : writer.kind ≠ .read := by
    have writable := write_requires_writable write
    simpa [Kind.writable] using writable
  by_cases rloan : reader.kind.loan = true
  · have parent := conflicting_loan_is_ancestor write rmem (Ne.symm different)
        same.symm rloan (.inl rfl)
    have before := valid.2.1 writer wmem reader.id parent
    cases hkind : writer.kind with
    | read => exact wkind hkind
    | write =>
        have other := conflicting_loan_is_ancestor read wmem different same
          (by simp [hkind, Kind.loan]) (.inr hkind)
        have after := valid.2.1 reader rmem writer.id other
        omega
    | own =>
        have empty := (valid.2.2.1 writer wmem).2.2 (by simp [hkind, Kind.owner, Kind.loan])
        simp [empty] at parent
    | «local» =>
        have empty := (valid.2.2.1 writer wmem).2.2 (by simp [hkind, Kind.owner, Kind.loan])
        simp [empty] at parent
  · have rowner : reader.kind.owner = true := by simpa [Kind.owner] using rloan
    by_cases wloan : writer.kind.loan = true
    · have wwrite : writer.kind = .write := by
        cases hkind : writer.kind <;> simp_all [Kind.loan]
      have parent := conflicting_loan_is_ancestor read wmem different same wloan (.inr wwrite)
      have empty := (valid.2.2.1 reader rmem).2.2 rowner
      simp [empty] at parent
    · have wowner : writer.kind.owner = true := by simpa [Kind.owner] using wloan
      exact different (valid.2.2.2 writer wmem reader rmem wowner rowner same)

/-- Releasing or transferring the sole owner leaves no root-local permission.
External view roots are lifetime assumptions and cannot be released here. -/
theorem erase_owner_removes_root {s : State} {binding : Binding}
    (valid : Valid s) (present : binding ∈ s.cells)
    (owned : binding.kind.owner = true) (clear : Unborrowed s binding.root) :
    ∀ remaining ∈ (s.erase binding.id).cells, remaining.root ≠ binding.root := by
  intro remaining member same
  have filtered := List.mem_filter.mp member
  have different : remaining.id ≠ binding.id := by simpa using filtered.2
  by_cases loan : remaining.kind.loan = true
  · exact clear remaining filtered.1 loan same
  · have owner : remaining.kind.owner = true := by simpa [Kind.owner] using loan
    exact different (valid.2.2.2 remaining filtered.1 binding present owner owned same)

theorem erase_owner_refuses_later_access {s : State} {binding other : Binding}
    {writing : Bool} (valid : Valid s) (present : binding ∈ s.cells)
    (owned : binding.kind.owner = true) (clear : Unborrowed s binding.root)
    (same : other.root = binding.root) :
    ¬ CanAccess (s.erase binding.id) other writing := by
  intro access
  exact erase_owner_removes_root valid present owned clear other access.1 same

/-- The subtraction-form C slice guard authorizes every translated index,
without requiring a potentially overflowing `start + count` guard. -/
theorem slice_index_in_range {length start count index : Nat}
    (startBound : start ≤ length) (countBound : count ≤ length - start)
    (indexBound : index < count) : start + index < length := by omega

theorem nested_slice_in_range {length start count inner offset index : Nat}
    (startBound : start ≤ length) (countBound : count ≤ length - start)
    (innerBound : inner ≤ count) (offsetBound : offset ≤ count - inner)
    (indexBound : index < offset) : start + inner + index < length := by omega

theorem checked_add_in_range {left right limit : Nat}
    (rightBound : right ≤ limit) (leftBound : left ≤ limit - right) :
    left + right ≤ limit := by omega

end Mettapedia.GSLT.LanguageDef.CheckedBytes
