import Mettapedia.Machines.CMemory.ExecutableStorage
import Mettapedia.Machines.CMemory.Values

/-!
# Executable lifetime, initialization and allocation controls

These controls use the existing typed scalar values. They exercise the
executable storage operations and their logical ownership correspondence;
they do not claim native byte layout or a complete C expression interpreter.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.ExecutableStorage.Controls

open Mettapedia.GSLT.SeparationAlgebra

def initial : Storage CVal := [(3, ⟨true, [some (.u32 7), none]⟩)]
def dead : Storage CVal := put initial 3 ⟨false, [some (.u32 7), none]⟩
def updated : Storage CVal := put initial 3 ⟨true, [some (.u32 7), some (.u32 9)]⟩

theorem initialized_cell_loads : load initial ⟨3, 0⟩ = some (.u32 7) := rfl
theorem indeterminate_cell_does_not_load : load initial ⟨3, 1⟩ = none := rfl
theorem one_past_does_not_load : load initial ⟨3, 2⟩ = none := rfl
theorem absent_block_does_not_load : load initial ⟨4, 0⟩ = none := rfl
theorem dead_block_does_not_load : load dead ⟨3, 0⟩ = none := rfl

theorem store_initializes_cell : store initial ⟨3, 1⟩ (.u32 9) = some updated := rfl
theorem initialized_store_is_readable : load updated ⟨3, 1⟩ = some (.u32 9) := rfl
theorem dead_block_does_not_store : store dead ⟨3, 0⟩ (.u32 9) = none := rfl
theorem one_past_does_not_store : store initial ⟨3, 2⟩ (.u32 9) = none := rfl

theorem base_free_retires_block : free initial (some ⟨3, 0⟩) = some dead := rfl
theorem null_free_preserves_storage : free initial none = some initial := rfl
theorem interior_free_is_rejected : free initial (some ⟨3, 1⟩) = none := rfl
theorem repeated_free_is_rejected : free dead (some ⟨3, 0⟩) = none := rfl

theorem allocation_failure_preserves_storage :
    allocate initial 5 .failure = some (none, initial) := rfl
theorem fresh_allocation_keeps_existing_blocks :
    allocate initial 2 (.fresh 4) =
      some (some ⟨4, 0⟩, put initial 4 ⟨true, [none, none]⟩) := rfl
theorem live_identity_is_not_fresh : allocate initial 2 (.fresh 3) = none := rfl
theorem dead_identity_is_not_fresh : allocate dead 2 (.fresh 3) = none := rfl
theorem zero_extent_can_have_a_fresh_identity :
    allocate initial 0 (.fresh 4) = some (some ⟨4, 0⟩, put initial 4 ⟨true, []⟩) := rfl
theorem zero_extent_cannot_be_dereferenced :
    load (put initial 4 ⟨true, []⟩) ⟨4, 0⟩ = none := rfl

theorem one_past_is_valid_for_comparison : validPointer initial ⟨3, 2⟩ = true := rfl
theorem beyond_one_past_is_invalid : validPointer initial ⟨3, 3⟩ = false := rfl
theorem dead_pointer_comparison_is_refused : compare dead (some ⟨3, 0⟩) none = none := rfl
theorem live_pointer_self_comparison :
    compare initial (some ⟨3, 2⟩) (some ⟨3, 2⟩) = some true := rfl

theorem reallocation_failure_keeps_old_storage :
    reallocate initial (some ⟨3, 0⟩) 4 .failure = some (none, initial) := rfl
theorem reallocation_copies_prefix_and_retires_old_identity :
    reallocate initial (some ⟨3, 0⟩) 4 (.fresh 4) =
      some (some ⟨4, 0⟩,
        put dead 4 ⟨true, [some (.u32 7), none, none, none]⟩) := rfl
theorem nonzero_reallocation_profile_rejects_zero_extent :
    reallocate initial (some ⟨3, 0⟩) 0 .failure = none := rfl

theorem executable_store_has_owned_logical_endpoint :
    (act (L := Excl (Option CVal)) (.store ⟨3, 1⟩ (.u32 9))).Safe (heap initial) ∧
      (act (L := Excl (Option CVal)) (.store ⟨3, 1⟩ (.u32 9))).Step
        (heap initial) () (heap updated) :=
  store_sound initial updated ⟨3, 1⟩ (.u32 9) store_initializes_cell

theorem executable_free_has_owned_logical_endpoint :
    (act (L := Excl (Option CVal)) (.free (some ⟨3, 0⟩))).Safe (heap initial) ∧
      (act (L := Excl (Option CVal)) (.free (some ⟨3, 0⟩))).Step
        (heap initial) () (heap dead) :=
  free_sound initial dead (some ⟨3, 0⟩) base_free_retires_block

end Mettapedia.Machines.CMemory.ExecutableStorage.Controls
