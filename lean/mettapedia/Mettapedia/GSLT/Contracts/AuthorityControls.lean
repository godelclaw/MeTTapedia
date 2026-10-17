import Mettapedia.GSLT.Contracts.FrameUpdate
import Mettapedia.GSLT.Logic.SeparationProduct
import Mettapedia.Machines.CMemory.Fractional

/-!
# Controls for authority and its transport

## Read and consume

`Access` is the separation algebra of one object's access rights: nothing, a
duplicable read right, or the consume right.  Read rights can be held side by
side; the consume right excludes every other right.

* Read is shared and consume is exclusive (`read_shared`, `consume_exclusive`).
* **Reading never updates to consuming** (`not_frameUpdate_read_consume`), while
  the consumer may weaken to a reader (`consume_updates_read`).
* **No resource homomorphism carries read to consume**, into any separation
  algebra (`hom_read_not_exclusive`, `no_hom_read_to_consume`).  This holds even
  for homomorphisms that erase resources, because a read right is separate from
  itself.

## The naive record

A capability recorded as a plain label (`CapabilityRecord`) can be relabelled by
any function.  The relabelling `upgrade` turns a read label into a consume
label (`upgrade_read`), and no resource homomorphism induces it
(`upgrade_not_transport`).  An unchecked label is not a preservation proof.

## A revoking transport can upgrade

`Halves` splits one object between two named holders.  The left half is shared:
the right half can be held beside it.  The homomorphism `revokeRight` erases
the right half and gives the left holder the consume right
(`revokeRight_upgrades`).  It erases a non-empty resource
(`revokeRight_not_reflectsZero`), which is exactly the hypothesis that
`shared_map` needs.

## A homomorphism need not preserve updates

`splitOwner` carries exclusive ownership of a Boolean cell to a pair of cells,
attaching a second token to one value only.  Overwriting an owned cell is a
frame-preserving update at the source; its image is not, because a holder of
the second token, which no source frame accounts for, is broken by it
(`splitOwner_not_preservesUpdates`).  The map does not lift extensions
(`splitOwner_not_liftsExtensions`), the sufficient condition of
`preservesUpdates_of_liftsExtensions`.

## Fractional permissions

Boyland's fractional permissions on a C memory cell
(`Mettapedia.Machines.CMemory.Frac`) obey the same law: the whole permission is
exclusive, a half is shared, and a half never updates to the whole
(`Fractional.not_frameUpdate_half_whole`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.SeparationTransport
open scoped Mettapedia.GSLT.SeparationAlgebra

universe u

/-! ## Read and consume -/

/-- **Access rights to one object.** -/
inductive Access where
  | none
  | read
  | consume
  deriving DecidableEq, Repr

namespace Access

instance : Zero Access := ⟨.none⟩

/-- Combining rights; the result matters only for separate rights. -/
def add : Access → Access → Access
  | .none, y => y
  | .read, .none => .read
  | .read, .read => .read
  | .read, .consume => .consume
  | .consume, _ => .consume

instance : Add Access := ⟨add⟩

/-- Read rights sit beside read rights; the consume right sits beside nothing. -/
def separate : Access → Access → Bool
  | .none, _ => true
  | _, .none => true
  | .read, .read => true
  | _, _ => false

instance instSepAlgebra : SepAlgebra Access where
  Separate x y := separate x y = true
  separate_zero x := by cases x <;> rfl
  separate_symm := by
    intro x y h
    revert h
    cases x <;> cases y <;> decide
  add_zero x := by cases x <;> rfl
  add_comm := by
    intro x y h
    revert h
    cases x <;> cases y <;> decide
  add_assoc := by
    intro x y z h₁ h₂ h₃
    revert h₁ h₂ h₃
    cases x <;> cases y <;> cases z <;> decide
  separate_of_separate_add := by
    intro x y z h₁ h₂
    revert h₁ h₂
    cases x <;> cases y <;> cases z <;> decide
  separate_add_of_separate_add := by
    intro x y z h₁ h₂
    revert h₁ h₂
    cases x <;> cases y <;> cases z <;> decide

instance (x y : Access) : Decidable (x ## y) :=
  inferInstanceAs (Decidable (separate x y = true))

theorem zero_eq : (0 : Access) = .none := rfl

theorem read_selfSeparate : Access.read ## Access.read := rfl

theorem read_shared : Shared Access.read :=
  shared_of_selfSeparate (by decide) read_selfSeparate

theorem consume_exclusive : Exclusive Access.consume := by
  refine ⟨by decide, ?_⟩
  intro c h
  cases c
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- **Reading never updates to consuming.** -/
theorem not_frameUpdate_read_consume : ¬ FrameUpdate Access.read Access.consume :=
  not_frameUpdate_of_shared_exclusive read_shared consume_exclusive

/-- The consumer may weaken to a reader. -/
theorem consume_updates_read : FrameUpdate Access.consume Access.read :=
  consume_exclusive.frameUpdate _

/-- **No resource homomorphism, into any separation algebra, makes read
exclusive.** -/
theorem hom_read_not_exclusive {B : Type u} [Zero B] [Add B] [SepAlgebra B]
    (f : Hom Access B) : ¬ Exclusive (f .read) :=
  not_exclusive_map_of_selfSeparate f read_selfSeparate

theorem no_hom_read_to_consume (f : Hom Access Access) : f .read ≠ .consume := by
  intro upgraded
  apply hom_read_not_exclusive f
  rw [upgraded]
  exact consume_exclusive

end Access

/-! ## The naive record -/

/-- A capability as an unchecked label. -/
inductive RightLabel where
  | read
  | consume
  deriving DecidableEq, Repr

/-- **A capability record**: an object and a right, with no laws. -/
structure CapabilityRecord (Obj : Type u) where
  object : Obj
  right : RightLabel
  deriving DecidableEq

namespace CapabilityRecord

variable {Obj : Type u}

/-- The access right a record claims. -/
def access (record : CapabilityRecord Obj) : Access :=
  match record.right with
  | .read => .read
  | .consume => .consume

/-- A relabelling that any function on records may perform. -/
def upgrade (record : CapabilityRecord Obj) : CapabilityRecord Obj :=
  { record with right := .consume }

theorem upgrade_read (object : Obj) : (upgrade ⟨object, .read⟩).right = .consume := rfl

/-- **The relabelling is induced by no resource homomorphism.** -/
theorem upgrade_not_transport (object : Obj) :
    ¬ ∃ f : Hom Access Access, ∀ record : CapabilityRecord Obj,
      f record.access = (upgrade record).access := by
  rintro ⟨f, induced⟩
  exact Access.no_hom_read_to_consume f (induced ⟨object, .read⟩)

end CapabilityRecord

/-! ## A revoking transport can upgrade -/

/-- One object split between two named holders. -/
inductive Halves where
  | none
  | left
  | right
  | whole
  deriving DecidableEq, Repr

namespace Halves

instance : Zero Halves := ⟨.none⟩

def add : Halves → Halves → Halves
  | .none, y => y
  | x, .none => x
  | _, _ => .whole

instance : Add Halves := ⟨add⟩

def separate : Halves → Halves → Bool
  | .none, _ => true
  | _, .none => true
  | .left, .right => true
  | .right, .left => true
  | _, _ => false

instance instSepAlgebra : SepAlgebra Halves where
  Separate x y := separate x y = true
  separate_zero x := by cases x <;> rfl
  separate_symm := by
    intro x y h
    revert h
    cases x <;> cases y <;> decide
  add_zero x := by cases x <;> rfl
  add_comm := by
    intro x y h
    revert h
    cases x <;> cases y <;> decide
  add_assoc := by
    intro x y z h₁ h₂ h₃
    revert h₁ h₂ h₃
    cases x <;> cases y <;> cases z <;> decide
  separate_of_separate_add := by
    intro x y z h₁ h₂
    revert h₁ h₂
    cases x <;> cases y <;> cases z <;> decide
  separate_add_of_separate_add := by
    intro x y z h₁ h₂
    revert h₁ h₂
    cases x <;> cases y <;> cases z <;> decide

instance (x y : Halves) : Decidable (x ## y) :=
  inferInstanceAs (Decidable (separate x y = true))

theorem left_shared : Shared Halves.left := ⟨.right, by decide, rfl⟩

end Halves

/-- Revoke the right half and give its rights to the left holder. -/
def revokeRight : Hom Halves Access where
  toFun
    | .none => .none
    | .left => .consume
    | .right => .none
    | .whole => .consume
  map_zero := rfl
  map_add := by
    intro x y h
    revert h
    cases x <;> cases y <;> decide
  map_separate := by
    intro x y h
    revert h
    cases x <;> cases y <;> decide

theorem revokeRight_not_reflectsZero : ¬ revokeRight.ReflectsZero := by
  intro reflects
  exact absurd (reflects .right rfl) (by decide)

/-- **A revoking transport upgrades a shared holder to exclusive authority.** -/
theorem revokeRight_upgrades : Shared Halves.left ∧ Exclusive (revokeRight .left) :=
  ⟨Halves.left_shared, Access.consume_exclusive⟩

/-! ## A homomorphism need not preserve updates -/

/-- Ownership of a Boolean cell carried to a pair of cells; owning the value
`false` also takes a second token. -/
def splitOwner : Hom (Excl Bool) (Excl Bool × Excl Unit) where
  toFun
    | .empty => (.empty, .empty)
    | .own true => (.own true, .empty)
    | .own false => (.own false, .own ())
  map_zero := rfl
  map_add := by
    rintro (_ | _ | _) (_ | _ | _) (h | h) <;> first | rfl | cases h
  map_separate := by
    rintro (_ | _ | _) (_ | _ | _) (h | h) <;>
      first | exact ⟨Or.inl rfl, Or.inl rfl⟩ | exact ⟨Or.inr rfl, Or.inr rfl⟩ | cases h

/-- Overwriting an owned cell is a frame-preserving update. -/
theorem overwrite_frameUpdate : FrameUpdate (Excl.own true) (Excl.own false) := by
  rintro c (h | h)
  · cases h
  · exact Or.inr h

/-- **The image of the overwrite is not frame-preserving.** -/
theorem splitOwner_not_preservesUpdates : ¬ PreservesUpdates splitOwner := by
  intro preserves
  have image := preserves _ _ overwrite_frameUpdate (.empty, .own ())
    ⟨Or.inr rfl, Or.inl rfl⟩
  rcases image.2 with h | h <;> cases h

theorem splitOwner_not_liftsExtensions : ¬ splitOwner.LiftsExtensions := fun lifts =>
  splitOwner_not_preservesUpdates (preservesUpdates_of_liftsExtensions splitOwner lifts)

/-! ## Fractional permissions on a C memory cell -/

namespace Fractional

open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.CellPermission

variable {C : Type}

theorem whole_exclusive (c : C) : Exclusive (whole c : Frac C) :=
  ⟨whole_ne_zero c, fun _ separate => eq_zero_of_whole_separate separate⟩

theorem half_shared (c : C) : Shared (Frac.half c) := by
  refine ⟨Frac.half c, ?_, (Frac.whole_eq_half_add_half c).1⟩
  intro h
  cases h

/-- **A half permission never updates to the whole one.** -/
theorem not_frameUpdate_half_whole (c c' : C) :
    ¬ FrameUpdate (Frac.half c) (whole c' : Frac C) :=
  not_frameUpdate_of_shared_exclusive (half_shared c) (whole_exclusive c')

/-- The whole permission may weaken to a half. -/
theorem whole_updates_half (c c' : C) : FrameUpdate (whole c : Frac C) (Frac.half c') :=
  (whole_exclusive c).frameUpdate _

end Fractional

/-! ## Axiom audit -/

#print axioms Access.not_frameUpdate_read_consume
#print axioms Access.no_hom_read_to_consume
#print axioms CapabilityRecord.upgrade_not_transport
#print axioms revokeRight_upgrades
#print axioms revokeRight_not_reflectsZero
#print axioms splitOwner_not_preservesUpdates
#print axioms Fractional.not_frameUpdate_half_whole

end Mettapedia.GSLT.Contracts
