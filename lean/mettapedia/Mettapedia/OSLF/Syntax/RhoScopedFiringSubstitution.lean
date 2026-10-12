import Mettapedia.OSLF.Syntax.RhoScopedEventPresheaf
import Mettapedia.OSLF.Syntax.RhoScopedParallelReactiveSystem

/-!
# Full firing substitution and the exact least-label admission condition

Every supplied original firing maps to an actual enabled event after its
label context is filled. The complete mapped rule and surrounding process
are retained. Mapping also gives an IPO firing precisely when their mapped
inventories retain the required disjointness. This condition is not supplied
by endpoint agreement or by the ability to express a native predicate.

Identity-labelled native events need no additional condition: their empty
label remains empty under every capture-avoiding substitution.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.RhoScopedFiringSubstitution

open RhoSchema RhoQuotationClassFibres RhoScopedParallelEvents
open RhoScopedParallelInventory RhoScopedParallelReactiveSystem RhoScopedEventPresheaf

universe u
variable {Index : Type u} {rules : Index → ProcessRule} {admitted : Index → Prop}
variable {context destination : Ctx sig}
local instance (scope : Ctx sig) : DecidableEq (Prime scope) := Classical.decEq _

theorem substitute_zero (change : Sub sig context destination) :
    bindQ change (zero context) = zero destination := rfl

def LeastAdmission (change : Sub sig context destination)
    {first label second : Process context}
    (receipt : Firing (rules := rules) (admitted := admitted) first label second) : Prop :=
  read (bindQ change label) ∩ read (bindQ change receipt.surrounding) = 0

theorem substituted_square (change : Sub sig context destination)
    {first label second : Process context}
    (receipt : Firing (rules := rules) (admitted := admitted) first label second) :
    join (bindQ change first) (bindQ change label) =
      join (receipt.root.map change).source (bindQ change receipt.surrounding) := by
  rw [Root.source_map, ← substitute_join, ← substitute_join, receipt.square]

theorem substituted_target (change : Sub sig context destination)
    {first label second : Process context}
    (receipt : Firing (rules := rules) (admitted := admitted) first label second) :
    bindQ change second = join (receipt.root.map change).target (bindQ change receipt.surrounding) := by
  rw [Root.target_map, ← substitute_join, ← receipt.target]

theorem enabled_after_filling_mapped_label (change : Sub sig context destination)
    {first label second : Process context}
    (receipt : Firing (rules := rules) (admitted := admitted) first label second) :
    RhoScopedParallelEvents.Step (rules := rules) (admitted := admitted)
      (join (bindQ change first) (bindQ change label)) (bindQ change second) := by
  exact (step_iff_root_surrounding _ _).mpr
    ⟨receipt.root.map change, bindQ change receipt.surrounding,
      substituted_square change receipt, substituted_target change receipt⟩

def map (change : Sub sig context destination)
    {first label second : Process context}
    (receipt : Firing (rules := rules) (admitted := admitted) first label second)
    (allowed : LeastAdmission change receipt) :
    Firing (rules := rules) (admitted := admitted)
      (bindQ change first) (bindQ change label) (bindQ change second) where
  root := receipt.root.map change
  surrounding := bindQ change receipt.surrounding
  square := substituted_square change receipt
  least := allowed
  target := substituted_target change receipt

theorem complete_map_admission_iff (change : Sub sig context destination)
    {first label second : Process context}
    (receipt : Firing (rules := rules) (admitted := admitted) first label second) :
    (∃ mapped : Firing (rules := rules) (admitted := admitted)
        (bindQ change first) (bindQ change label) (bindQ change second),
      mapped.root = receipt.root.map change ∧
        mapped.surrounding = bindQ change receipt.surrounding) ↔ LeastAdmission change receipt := by
  constructor
  · rintro ⟨mapped, _rootRead, surroundingRead⟩
    have least := mapped.least
    rw [surroundingRead] at least
    exact least
  · intro allowed
    exact ⟨map change receipt allowed, rfl, rfl⟩

def mapIdentity (change : Sub sig context destination)
    {first second : Process context}
    (receipt : Firing (rules := rules) (admitted := admitted) first (zero context) second) :
    Firing (rules := rules) (admitted := admitted)
      (bindQ change first) (zero destination) (bindQ change second) :=
  map change receipt (by
    unfold LeastAdmission
    rw [substitute_zero, read_zero, Multiset.zero_inter])

theorem identity_rule_origin (change : Sub sig context destination)
    {first second : Process context}
    (receipt : Firing (rules := rules) (admitted := admitted) first (zero context) second) :
    (mapIdentity change receipt).root.1 = receipt.root.1 := rfl

theorem identity_complete_surrounding (change : Sub sig context destination)
    {first second : Process context}
    (receipt : Firing (rules := rules) (admitted := admitted) first (zero context) second) :
    (mapIdentity change receipt).surrounding = bindQ change receipt.surrounding := rfl

end Mettapedia.OSLF.Binding.RhoScopedFiringSubstitution
