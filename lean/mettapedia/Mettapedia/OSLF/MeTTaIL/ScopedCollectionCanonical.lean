import Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachine

/-!
# Canonical residuals without repeated sorting

Allocation only removes or retains physical elements. Consequently a residual
of an arranged collection remains arranged. The executable batch may use that
residual directly once its input collection is canonical.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionSelection

theorem tracedAllocations_residual_sublist {α : Type} {idempotent : Bool} {count : Nat}
    {items : List α} {allocation : Allocation α}
    (member : allocation ∈ tracedAllocations idempotent count items) :
    allocation.residual.Sublist items := by
  induction count generalizing items allocation with
  | zero =>
      simp only [tracedAllocations, List.mem_singleton] at member
      subst allocation
      exact List.Sublist.refl _
  | succ count ih =>
      simp only [tracedAllocations, List.mem_flatMap, List.mem_map] at member
      obtain ⟨choice, selected, tail, allocated, rfl⟩ := member
      have residual := (choice_valid selected).2.2
      have subset : choice.residual.Sublist items := by
        rw [residual]
        cases choice.retained <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · exact List.eraseIdx_sublist _ _
        · exact List.Sublist.refl _
      exact (ih allocated).trans subset

end Mettapedia.OSLF.MeTTaIL.CollectionSelection

namespace Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachine

open Syntax CanonicalBags PatternLexOrder CollectionSelection

theorem arrange_sublist_fixed (kind : CollType) {items residual : List Pattern}
    (fixed : arrange kind items = items) (sublist : residual.Sublist items) :
    arrange kind residual = residual := by
  cases kind with
  | vec => rfl
  | hashBag =>
      have sorted : items.Pairwise PatternLe := by
        rw [← fixed]
        exact sortLex_pairwise items
      exact List.Perm.eq_of_pairwise' (sortLex_pairwise residual)
        (sorted.sublist sublist) (sortLex_perm residual)
  | hashSet =>
      have sorted : items.Pairwise PatternLe := by
        rw [← fixed]
        exact (sortLex_pairwise items).sublist (List.dedup_sublist _)
      have distinct : items.Nodup := by
        rw [← fixed]
        exact List.nodup_dedup _
      have ordered : sortLex residual = residual :=
        List.Perm.eq_of_pairwise' (sortLex_pairwise residual)
          (sorted.sublist sublist) (sortLex_perm residual)
      simp only [arrange_set, ordered, List.dedup_eq_self.mpr (distinct.sublist sublist)]

theorem allocation_residual_fixed (request : Request)
    (fixed : arrange request.kind request.targets = request.targets)
    {allocation : Allocation Pattern} (member : allocation ∈ request.allocations) :
    arrange request.kind allocation.residual = allocation.residual :=
  arrange_sublist_fixed request.kind fixed (tracedAllocations_residual_sublist member)

/-- The runtime construction uses the already arranged residual directly. -/
def rawAllocationState (request : Request) (allocation : Allocation Pattern) :
    GeneralScopedMatchMachine.State :=
  let arguments := GeneralScopedMatchMachine.Task.arguments request.path request.depth request.index
    request.schemas allocation.values
  match request.rest with
  | none =>
      if allocation.residual.isEmpty then
        { agenda := [⟨request.initial, [arguments], []⟩] }
      else { agenda := [] }
  | some name =>
      { agenda := [⟨request.initial,
          [arguments, .restCapture (request.path ++ [request.index + request.schemas.length])
            request.depth name request.kind allocation.residual], []⟩] }

theorem rawAllocationState_eq (request : Request) (allocation : Allocation Pattern)
    (fixed : arrange request.kind allocation.residual = allocation.residual) :
    rawAllocationState request allocation = allocationState request allocation := by
  simp only [rawAllocationState, allocationState, fixed]
  rfl

def rawStart (request : Request) : State :=
  request.allocations.map fun allocation => ⟨allocation, rawAllocationState request allocation⟩

theorem rawStart_eq (request : Request)
    (fixed : arrange request.kind request.targets = request.targets) :
    rawStart request = start request := by
  apply List.map_congr_left
  intro allocation member
  rw [rawAllocationState_eq request allocation (allocation_residual_fixed request fixed member)]

end Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachine
