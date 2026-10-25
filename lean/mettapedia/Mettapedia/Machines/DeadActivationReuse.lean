import Mathlib.Data.List.Basic

/-!
# Reusing a dead activation's slot vector

Frame addresses are private to this machine. Values are opaque payloads;
the instruction language can read them through registered frame roots but
cannot reinterpret them as frame addresses. Logical variable cells and their
identities are separate from this storage interface.

Replacing the current root by a fresh vector or by an unreferenced old vector
preserves rooted values and aliasing. Root reads, writes, captures and ordered
publication respect that relation. Native admission must establish the root
exclusion, argument staging, capacity and collector invariants separately.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.DeadActivationReuse

structure State (Root Value : Type) where
  location : Root → Nat
  heap : Nat → List Value

variable {Root Other Value : Type}

def State.read (state : State Root Value) (root : Root) : List Value :=
  state.heap (state.location root)

def State.write (state : State Root Value) (root : Root)
    (values : List Value) : State Root Value :=
  { state with heap := Function.update state.heap (state.location root) values }

/-- Both values and aliasing matter: equal readouts alone do not license a
write through two roots that alias in only one representation. -/
structure RootedEquivalent (left right : State Root Value) : Prop where
  values : ∀ root, left.read root = right.read root
  aliases : ∀ one two,
    left.location one = left.location two ↔ right.location one = right.location two

/-- Preparing an unpublished vector cannot corrupt the source state needed
if admission fails and the ordinary route must resume. -/
theorem private_preparation_preserves (state : State Root Value)
    (scratch : Nat) (values : List Value)
    (privateScratch : ∀ root, state.location root ≠ scratch) :
    RootedEquivalent state {state with heap := Function.update state.heap scratch values} where
  aliases _ _ := Iff.rfl
  values root := by simp [State.read, privateScratch root]

theorem RootedEquivalent.write {left right : State Root Value}
    (same : RootedEquivalent left right) (root : Root) (values : List Value) :
    RootedEquivalent (left.write root values) (right.write root values) where
  aliases := same.aliases
  values other := by
    by_cases hit : left.location other = left.location root
    · have there := (same.aliases other root).mp hit
      simp [State.read, State.write, hit, there]
    · have there : right.location other ≠ right.location root :=
        fun equal => hit ((same.aliases other root).mpr equal)
      simpa [State.read, State.write, hit, there] using same.values other

/-- A capture duplicates or rearranges existing roots; no address becomes
observable and no new alias can be invented. -/
def State.reindex (state : State Root Value) (select : Other → Root) : State Other Value :=
  ⟨state.location ∘ select, state.heap⟩

theorem RootedEquivalent.reindex {left right : State Root Value}
    (same : RootedEquivalent left right) (select : Other → Root) :
    RootedEquivalent (left.reindex select) (right.reindex select) where
  values root := same.values (select root)
  aliases one two := same.aliases (select one) (select two)

/-- The arguments have already been staged before the old vector is cleared.
`none` is the new current activation; `some root` is a suspended root. -/
def enter (heap : Nat → List Value) (current : Nat) (suspended : Root → Nat)
    (initial : List Value) : State (Option Root) Value :=
  ⟨fun root => match root with | none => current | some saved => suspended saved,
   Function.update heap current initial⟩

theorem reuse_equivalent (heap : Nat → List Value) (old fresh : Nat)
    (suspended : Root → Nat) (initial : List Value)
    (oldDead : ∀ root, suspended root ≠ old)
    (freshUnused : ∀ root, suspended root ≠ fresh) :
    RootedEquivalent (enter heap old suspended initial)
      (enter heap fresh suspended initial) where
  values root := by
    cases root with
    | none => simp [State.read, enter]
    | some saved => simp [State.read, enter, oldDead saved, freshUnused saved]
  aliases one two := by
    cases one with
    | none =>
      cases two with
      | none => simp only
      | some saved => simp [enter, Ne.symm (oldDead saved), Ne.symm (freshUnused saved)]
    | some saved =>
      cases two with
      | none => simp [enter, oldDead saved, freshUnused saved]
      | some other => rfl

inductive Instruction (Root Value : Type) where
  | put (root : Root) (values : List Value)
  | putSlot (root : Root) (slot : Nat) (value : Value)
  | emit (root : Root)

/-- Publication retains chronological order and duplicate observations. -/
def execute (state : State Root Value) : List (Instruction Root Value) →
    State Root Value × List (List Value)
  | [] => (state, [])
  | .put root values :: rest => execute (state.write root values) rest
  | .putSlot root slot value :: rest =>
      execute (state.write root ((state.read root).set slot value)) rest
  | .emit root :: rest =>
      let after := execute state rest
      (after.1, state.read root :: after.2)

/-- Arbitrary later frame writes, reads and publications preserve the same
observations. Capturing or retiring roots is handled by `reindex`. -/
theorem execute_preserves {left right : State Root Value}
    (same : RootedEquivalent left right) (program : List (Instruction Root Value)) :
    RootedEquivalent (execute left program).1 (execute right program).1 ∧
      (execute left program).2 = (execute right program).2 := by
  induction program generalizing left right with
  | nil => exact ⟨same, rfl⟩
  | cons instruction rest ih =>
      cases instruction with
      | put root values => exact ih (same.write root values)
      | putSlot root slot value =>
          simpa only [execute, same.values root] using
            ih (same.write root ((left.read root).set slot value))
      | emit root =>
          have after := ih same
          exact ⟨after.1, congrArg₂ List.cons (same.values root) after.2⟩

/-- Native stack chronology can establish exclusion of a current activation
from every suspended choice root. Return-continuation roots need their own
fresh-allocation/no-alias invariant, rather than this height argument alone. -/
theorem unprotected_excludes_choice_roots (height activationBirth : Nat)
    (sameHeight : activationBirth = height)
    (rootBirth : Root → Nat) (referencedBirth : Root → Nat)
    (bounded : ∀ root, rootBirth root ≤ height)
    (chronological : ∀ root, referencedBirth root < rootBirth root) :
    ∀ root, referencedBirth root ≠ activationBirth := by
  intro root equal
  have strict := chronological root
  have bound := bounded root
  rw [equal, sameHeight] at strict
  exact (Nat.not_lt_of_ge bound) strict

namespace Controls

def heap : Nat → List Nat := fun _ => [1, 2]
def saved : Unit → Nat := fun _ => 0

/-- Omitting root exclusion overwrites an observable suspended frame. -/
theorem live_root_reuse_changes_observation :
    (enter heap 0 saved [9]).read (some ()) = [9] ∧
    (enter heap 1 saved [9]).read (some ()) = [1, 2] := by decide

def disjoint : Unit → Nat := fun _ => 2

def after : List (Instruction (Option Unit) Nat) :=
  [.putSlot none 0 7, .emit (some ()), .emit none, .emit none]

theorem reused_and_fresh_ordered_control :
    (execute (enter heap 0 disjoint [4, 5]) after).2 =
      [[1, 2], [7, 5], [7, 5]] ∧
    (execute (enter heap 1 disjoint [4, 5]) after).2 =
      [[1, 2], [7, 5], [7, 5]] := by decide

/-- Clearing or overwriting the source before staging an overlapping argument
loses its old value. The native call must first fill its separate registers. -/
theorem unstaged_swap_loses_argument :
    ([1, 2].set 0 2).set 1 (([1, 2].set 0 2).getD 0 0) = [2, 2] ∧
    [([1, 2] : List Nat).getD 1 0, [1, 2].getD 0 0] = [2, 1] := by decide

end Controls
end Mettapedia.Machines.DeadActivationReuse
