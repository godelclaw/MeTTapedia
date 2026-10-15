import Mettapedia.OSLF.Syntax.RhoIntrinsicCanonicalBag
import Mathlib.Data.Multiset.MapFold

/-!
# Typed parallel inventories of the complete scoped rho equation quotient

Every component carries its actual source-context sorting evidence. The two
inventory carriers are independently converted in both directions. Their
readouts identify all process classes, including open terms and input bodies.
Parallel composition and null become multiset addition and the empty bag.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedParallelInventory

open RhoSchema RhoQuotationClassFibres RhoIntrinsicCanonicalBag
open Mettapedia.OSLF.MeTTaIL.Syntax

abbrev Prime (context : Ctx sig) := {pattern : Pattern // IsPrime context pattern}

def values {context : Ctx sig} (inventory : Multiset (Prime context)) : Multiset Pattern :=
  inventory.map Subtype.val

theorem values_injective (context : Ctx sig) :
    Function.Injective (values (context := context)) :=
  Multiset.map_injective Subtype.val_injective

def fromTyped {context : Ctx sig} (inventory : Multiset (Prime context)) : Inventory context :=
  ⟨values inventory, by
    intro pattern member
    obtain ⟨prime, _listed, rfl⟩ := Multiset.mem_map.mp member
    exact prime.property⟩

def toTyped {context : Ctx sig} (inventory : Inventory context) : Multiset (Prime context) :=
  inventory.val.attach.map (fun selected => ⟨selected.val, inventory.property _ selected.property⟩)

theorem values_toTyped {context : Ctx sig} (inventory : Inventory context) :
    values (toTyped inventory) = inventory.val := by
  unfold values toTyped
  rw [Multiset.map_map]
  exact Multiset.attach_map_val inventory.val

theorem fromTyped_toTyped {context : Ctx sig} (inventory : Inventory context) :
    fromTyped (toTyped inventory) = inventory :=
  Subtype.ext (values_toTyped inventory)

theorem toTyped_fromTyped {context : Ctx sig} (inventory : Multiset (Prime context)) :
    toTyped (fromTyped inventory) = inventory := by
  apply values_injective context
  exact values_toTyped (fromTyped inventory)

def inventoryEquiv (context : Ctx sig) : Inventory context ≃ Multiset (Prime context) where
  toFun := toTyped
  invFun := fromTyped
  left_inv := fromTyped_toTyped
  right_inv := toTyped_fromTyped

/-- The process and component carriers are formed independently. -/
def processEquiv (context : Ctx sig) : Process context ≃ Multiset (Prime context) :=
  (processInventoryEquiv context).trans (inventoryEquiv context)

def read {context : Ctx sig} (process : Process context) : Multiset (Prime context) :=
  processEquiv context process

def write {context : Ctx sig} (inventory : Multiset (Prime context)) : Process context :=
  (processEquiv context).symm inventory

theorem write_read {context : Ctx sig} (process : Process context) : write (read process) = process :=
  (processEquiv context).symm_apply_apply process

theorem read_write {context : Ctx sig} (inventory : Multiset (Prime context)) :
    read (write inventory) = inventory :=
  (processEquiv context).apply_symm_apply inventory

theorem values_read {context : Ctx sig} (process : Process context) :
    values (read process) = components process :=
  values_toTyped (decompose process)

theorem read_injective (context : Ctx sig) : Function.Injective (read (context := context)) :=
  (processEquiv context).injective

theorem read_zero (context : Ctx sig) : read (zero context) = 0 := by
  apply values_injective context
  rw [values_read, zero_components]
  rfl

theorem read_join {context : Ctx sig} (first second : Process context) :
    read (join first second) = read first + read second := by
  apply values_injective context
  rw [values_read, join_components]
  simp only [values, Multiset.map_add]
  exact (congrArg₂ (· + ·) (values_read first) (values_read second)).symm

theorem write_zero (context : Ctx sig) : write (0 : Multiset (Prime context)) = zero context := by
  apply read_injective context
  rw [read_write, read_zero]

theorem write_add {context : Ctx sig} (first second : Multiset (Prime context)) :
    write (first + second) = join (write first) (write second) := by
  apply read_injective context
  rw [read_write, read_join, read_write, read_write]

/-- All competitors in the inventory category have actual source-class readouts. -/
theorem all_inventories_realized {context : Ctx sig} (inventory : Multiset (Prime context)) :
    ∃ process : Process context, read process = inventory := ⟨write inventory, read_write inventory⟩

end Mettapedia.OSLF.Binding.RhoScopedParallelInventory
