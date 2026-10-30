import Mettapedia.GSLT.LanguageDef.OwnershipCalls

/-!
# Bounded references as resource-bearing values

The pointer's footprint and the length carried in its record must agree.
Slicing preserves that relation and cannot widen either lifetime or rights.
These laws apply to stack arrays, arenas and uniquely owned resizable buffers;
allocation/reclamation policy is not part of the view representation.

Native projection and integer-width conversion remain separate obligations.
No checksum, allocator success or unspecified C arithmetic is assumed here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Ownership

open Mettapedia.Machines.CMemory.Borrowing

structure BoundedView where
  region : Region
  length : Nat
  writing : Bool
  deriving DecidableEq, Repr

def BoundedView.Coherent (view : BoundedView) : Prop := view.length = view.region.count

def BoundedView.slice (view : BoundedView) (offset count : Nat) : Option BoundedView :=
  if offset ≤ view.length ∧ count ≤ view.length - offset then
    some ⟨instantiateView view.region offset count, count, view.writing⟩
  else none

theorem slice_preserves_contract {view child : BoundedView} {offset count : Nat}
    (coherent : view.Coherent) (step : view.slice offset count = some child) :
    child.Coherent ∧ view.region.Contains child.region ∧ child.writing = view.writing := by
  unfold BoundedView.slice at step
  split at step
  · rename_i bounds
    cases Option.some.inj step
    refine ⟨rfl, instantiateView_contained (Nat.le_refl _) ?_, rfl⟩
    unfold BoundedView.Coherent at coherent
    omega
  · contradiction

/-- A byte access through an admitted view lies in a live allocation.
This combines record coherence, bounds, spatial access and allocation life. -/
theorem admitted_view_index_live {s after : State} (valid : Valid s)
    {id index : Nat} {view : BoundedView}
    (admitted : apply s (.view id view.region view.length view.writing) = some after)
    (bound : index < view.length) :
    ∃ allocation ∈ s.allocations,
      allocation.region.Contains (instantiateView view.region index 1) := by
  obtain ⟨coherent, access⟩ := admitted_view_exact admitted
  have inside : index + 1 ≤ view.region.count := by omega
  have subaccess : Access s.loans id (instantiateView view.region index 1) view.writing :=
    access_subfootprint regionGeometry access (instantiateView_contained (Nat.le_refl _) inside)
  obtain ⟨loan, present, _, contains⟩ := access_has_live_loan subaccess
  obtain ⟨allocation, live, rootBounds⟩ := valid.2.2.2.2.1 loan present
  exact ⟨allocation, live, Region.contains_trans rootBounds contains⟩

theorem admitted_view_write_excludes_alias {s after : State} (valid : Valid s)
    {id other index length : Nat} {view region : Region} {writing : Bool}
    (admitted : apply s (.view id view length true) = some after)
    (bound : index < length) (different : id ≠ other)
    (reader : Access s.loans other region writing) :
    (instantiateView view index 1).Disjoint region := by
  obtain ⟨coherent, access⟩ := admitted_view_exact admitted
  have inside : index + 1 ≤ view.count := by omega
  have subaccess : Access s.loans id (instantiateView view index 1) true :=
    access_subfootprint regionGeometry access (instantiateView_contained (Nat.le_refl _) inside)
  exact exclusive_access_disjoint valid.2.2.2.1 different subaccess reader

/-- Every framed caller reference stays subject to the same alias rule after
a checked byte routine receives a view. This is independent of its indexing
algorithm; all accesses must stay within the supplied view. -/
theorem view_call_subaccess {s after : State} {id : Nat} {writing : Bool} {part : Region}
    (passed : passArgument s (.viewed writing) (.loan id) = some after)
    (bounded : ∀ loan ∈ s.loans, loan.id = id → loan.region.Contains part) :
    Access s.loans id part writing := by
  obtain ⟨loan, present, identity, access⟩ := passed_view_has_access passed
  exact access_subfootprint regionGeometry access (bounded loan present identity)

namespace ViewControls

open Controls

theorem stack_view_cannot_escape : run initial
    [.root 1 16 .exclusive .local 0, .borrow 2 1 ⟨1, 0, 8⟩ .shared,
      .endLoan 1] = none := by decide

theorem vector_cannot_release_under_view : run initial
    [.root 1 16 .exclusive .heap 9, .borrow 2 1 ⟨1, 0, 8⟩ .shared,
      .endLoan 1, .release 1 9] = none := by decide

theorem arena_cannot_reset_under_view : run initial
    [.root 1 4096 .exclusive .local 0, .borrow 2 1 ⟨1, 128, 64⟩ .shared,
      .endLoan 1] = none := by decide

theorem cloned_read_views_allowed : (run initial
    [.root 1 16 .exclusive .local 0, .borrow 2 1 ⟨1, 0, 8⟩ .shared,
      .borrow 3 2 ⟨1, 0, 8⟩ .shared,
      .view 2 ⟨1, 0, 8⟩ 8 false, .view 3 ⟨1, 0, 8⟩ 8 false]).isSome = true := by decide

theorem exclusive_copy_suspends_source : run initial
    [.root 1 16 .exclusive .local 0, .borrow 2 1 ⟨1, 0, 8⟩ .exclusive,
      .borrow 3 2 ⟨1, 0, 8⟩ .exclusive, .access 2 ⟨1, 0, 1⟩ true] = none := by decide

theorem disjoint_mutable_slices_allowed : (run initial
    [.root 1 16 .exclusive .local 0, .borrow 2 1 ⟨1, 0, 8⟩ .exclusive,
      .borrow 3 1 ⟨1, 8, 8⟩ .exclusive,
      .view 2 ⟨1, 0, 8⟩ 8 true, .view 3 ⟨1, 8, 8⟩ 8 true]).isSome = true := by decide

theorem forged_length_refused : run initial
    [.root 1 8 .exclusive .local 0, .view 1 ⟨1, 0, 8⟩ 9 false] = none := by decide

theorem forged_footprint_refused : run initial
    [.root 1 8 .exclusive .local 0, .view 1 ⟨1, 0, 9⟩ 9 false] = none := by decide

theorem dead_view_refused : run initial
    [.root 1 8 .exclusive .local 0, .endLoan 1, .view 1 ⟨1, 0, 8⟩ 8 false] = none := by decide

theorem narrowed_view_uses_new_bound : (run initial
    [.root 1 8 .exclusive .local 0, .borrow 2 1 ⟨1, 0, 8⟩ .shared,
      .restrict 2 ⟨1, 0, 4⟩, .access 2 ⟨1, 3, 1⟩ false]).isSome = true := by decide

theorem old_bound_cannot_survive_narrowing : run initial
    [.root 1 8 .exclusive .local 0, .borrow 2 1 ⟨1, 0, 8⟩ .shared,
      .restrict 2 ⟨1, 0, 4⟩, .access 2 ⟨1, 4, 1⟩ false] = none := by decide

theorem restriction_cannot_shrink_release_authority : run initial
    [.root 1 8 .exclusive .heap 9, .restrict 1 ⟨1, 0, 4⟩] = none := by decide

theorem empty_view_has_no_index : ¬∃ index : Nat, index < (0 : Nat) := by omega

end ViewControls

end Mettapedia.GSLT.LanguageDef.Ownership
